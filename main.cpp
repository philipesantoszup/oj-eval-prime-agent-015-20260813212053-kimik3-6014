#include <cstdio>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>

// Disk-based B+ tree key-value store.
// Key = (index string padded to 64 bytes with zeros, value int).
// All data lives in file "data.bin"; only a small page cache is kept in memory.

typedef int64_t i64;

static const int PAGE_SIZE = 4096;
static const int M = 52;            // max keys in internal node
static const int L = 58;            // max keys in leaf node
static const int MMIN = M / 2;      // min keys internal = 26
static const int LMIN = (L + 1) / 2;// min keys leaf = 29
static const i64 MAGIC = 0x46534A5455425031LL; // "FSJTUBP1"-ish

struct Key {
    char s[64];
    int  v;
};

static inline int cmpKey(const Key& a, const Key& b) {
    int c = memcmp(a.s, b.s, 64);
    if (c) return c;
    return (a.v > b.v) - (a.v < b.v);
}

struct Node {
    i64 next;      // leaf: next leaf page id, -1 if none
    int is_leaf;
    int cnt;
    union {
        Key lk[L + 1];                                   // leaf entries
        struct { Key k[M + 1]; i64 ch[M + 2]; } in;      // internal
    };
};
static_assert(sizeof(Node) <= PAGE_SIZE, "node too big");

struct Header {
    i64 magic;
    i64 root;       // page id of root
    i64 pages;      // next unallocated page id
};

// ---------------- file layer with small direct-mapped read cache ------------
static int fd = -1;
static Header hdr;

static const int CSLOTS = 128;
struct CEnt { i64 pid; int valid; char data[PAGE_SIZE]; };
static CEnt cache[CSLOTS];

static void rawRead(i64 pid, void* buf) {
    char* p = (char*)buf;
    i64 off = pid * (i64)PAGE_SIZE, left = PAGE_SIZE;
    while (left > 0) {
        ssize_t r = pread(fd, p, left, off);
        if (r <= 0) { memset(p, 0, left); return; } // short read at fresh page
        p += r; off += r; left -= r;
    }
}
static void rawWrite(i64 pid, const void* buf) {
    const char* p = (const char*)buf;
    i64 off = pid * (i64)PAGE_SIZE, left = PAGE_SIZE;
    while (left > 0) {
        ssize_t w = pwrite(fd, p, left, off);
        if (w <= 0) return;
        p += w; off += w; left -= w;
    }
}

static void readNode(i64 pid, Node& nd) {
    int s = (int)(pid & (CSLOTS - 1));
    if (!(cache[s].valid && cache[s].pid == pid)) {
        rawRead(pid, cache[s].data);
        cache[s].pid = pid; cache[s].valid = 1;
    }
    memcpy(&nd, cache[s].data, sizeof(Node));
}
static void writeNode(i64 pid, const Node& nd) {
    int s = (int)(pid & (CSLOTS - 1));
    memcpy(cache[s].data, &nd, sizeof(Node));
    cache[s].pid = pid; cache[s].valid = 1;
    rawWrite(pid, cache[s].data);
}
static i64 allocPage() { return hdr.pages++; }

static void writeHeader() {
    char buf[PAGE_SIZE];
    memset(buf, 0, sizeof(buf));
    memcpy(buf, &hdr, sizeof(hdr));
    rawWrite(0, buf);
    int s = 0; // pid 0 slot
    memcpy(cache[s].data, buf, PAGE_SIZE);
    cache[s].pid = 0; cache[s].valid = 1;
}

static void initStore() {
    fd = open("data.bin", O_RDWR | O_CREAT, 0644);
    struct stat st;
    fstat(fd, &st);
    bool fresh = true;
    if (st.st_size >= PAGE_SIZE) {
        char buf[PAGE_SIZE];
        rawRead(0, buf);
        Header h; memcpy(&h, buf, sizeof(h));
        if (h.magic == MAGIC && h.root >= 1 && h.pages > h.root) { hdr = h; fresh = false; }
    }
    if (fresh) {
        hdr.magic = MAGIC; hdr.pages = 1; hdr.root = 0;
        Node rt; memset(&rt, 0, sizeof(rt));
        rt.is_leaf = 1; rt.cnt = 0; rt.next = -1;
        i64 rp = allocPage();
        hdr.root = rp;
        writeNode(rp, rt);
        writeHeader();
    }
}

// ---------------- B+ tree operations ----------------

// returns true if node split; up = promoted key, rpid = new right page
static bool ins(i64 pid, const Key& k, Key& up, i64& rpid) {
    Node nd; readNode(pid, nd);
    if (nd.is_leaf) {
        int pos = 0;
        while (pos < nd.cnt && cmpKey(nd.lk[pos], k) < 0) pos++;
        for (int i = nd.cnt; i > pos; i--) nd.lk[i] = nd.lk[i - 1];
        nd.lk[pos] = k; nd.cnt++;
        if (nd.cnt <= L) { writeNode(pid, nd); return false; }
        int half = nd.cnt / 2;
        Node rn; rn.is_leaf = 1; rn.cnt = nd.cnt - half;
        memcpy(rn.lk, nd.lk + half, rn.cnt * sizeof(Key));
        i64 np = allocPage();
        rn.next = nd.next; nd.next = np;
        nd.cnt = half;
        writeNode(pid, nd); writeNode(np, rn);
        up = rn.lk[0]; rpid = np;
        return true;
    }
    int i = 0;
    while (i < nd.cnt && cmpKey(nd.in.k[i], k) <= 0) i++;
    Key up2; i64 rp2;
    if (!ins(nd.in.ch[i], k, up2, rp2)) return false;
    for (int j = nd.cnt; j > i; j--) nd.in.k[j] = nd.in.k[j - 1];
    for (int j = nd.cnt + 1; j > i + 1; j--) nd.in.ch[j] = nd.in.ch[j - 1];
    nd.in.k[i] = up2; nd.in.ch[i + 1] = rp2; nd.cnt++;
    if (nd.cnt <= M) { writeNode(pid, nd); return false; }
    int mid = nd.cnt / 2;
    Node rn; rn.is_leaf = 0;
    rn.cnt = nd.cnt - mid - 1;
    memcpy(rn.in.k, nd.in.k + mid + 1, rn.cnt * sizeof(Key));
    memcpy(rn.in.ch, nd.in.ch + mid + 1, (rn.cnt + 1) * sizeof(i64));
    i64 np = allocPage();
    up = nd.in.k[mid]; rpid = np;
    nd.cnt = mid;
    writeNode(pid, nd); writeNode(np, rn);
    return true;
}

static void insertKey(const Key& k) {
    Key up; i64 rp;
    if (ins(hdr.root, k, up, rp)) {
        Node nr; nr.is_leaf = 0; nr.cnt = 1; nr.next = -1;
        nr.in.k[0] = up; nr.in.ch[0] = hdr.root; nr.in.ch[1] = rp;
        i64 np = allocPage();
        writeNode(np, nr);
        hdr.root = np;
        writeHeader();
    }
}

// child p.ch[i] underflowed; rebalance. writes p (at ppid) and touched siblings.
static void fixChild(Node& p, i64 ppid, int i) {
    i64 cpid = p.in.ch[i];
    Node c; readNode(cpid, c);
    int minc = c.is_leaf ? LMIN : MMIN;
    // borrow from left sibling
    if (i > 0) {
        Node ls; readNode(p.in.ch[i - 1], ls);
        if (ls.cnt > minc) {
            if (c.is_leaf) {
                for (int j = c.cnt; j > 0; j--) c.lk[j] = c.lk[j - 1];
                c.lk[0] = ls.lk[ls.cnt - 1]; c.cnt++; ls.cnt--;
                p.in.k[i - 1] = c.lk[0];
            } else {
                for (int j = c.cnt; j > 0; j--) c.in.k[j] = c.in.k[j - 1];
                for (int j = c.cnt + 1; j > 0; j--) c.in.ch[j] = c.in.ch[j - 1];
                c.in.k[0] = p.in.k[i - 1];
                c.in.ch[0] = ls.in.ch[ls.cnt];
                c.cnt++;
                p.in.k[i - 1] = ls.in.k[ls.cnt - 1];
                ls.cnt--;
            }
            writeNode(cpid, c); writeNode(p.in.ch[i - 1], ls); writeNode(ppid, p);
            return;
        }
    }
    // borrow from right sibling
    if (i < p.cnt) {
        Node rs; readNode(p.in.ch[i + 1], rs);
        if (rs.cnt > minc) {
            if (c.is_leaf) {
                c.lk[c.cnt] = rs.lk[0]; c.cnt++;
                for (int j = 0; j + 1 < rs.cnt; j++) rs.lk[j] = rs.lk[j + 1];
                rs.cnt--;
                p.in.k[i] = rs.lk[0];
            } else {
                int C = rs.cnt;
                c.in.k[c.cnt] = p.in.k[i];
                c.in.ch[c.cnt + 1] = rs.in.ch[0];
                c.cnt++;
                p.in.k[i] = rs.in.k[0];
                for (int j = 0; j + 1 < C; j++) rs.in.k[j] = rs.in.k[j + 1];
                for (int j = 0; j < C; j++) rs.in.ch[j] = rs.in.ch[j + 1];
                rs.cnt = C - 1;
            }
            writeNode(cpid, c); writeNode(p.in.ch[i + 1], rs); writeNode(ppid, p);
            return;
        }
    }
    // merge
    if (i > 0) {
        // merge c into left sibling
        Node ls; readNode(p.in.ch[i - 1], ls);
        if (c.is_leaf) {
            memcpy(ls.lk + ls.cnt, c.lk, c.cnt * sizeof(Key));
            ls.cnt += c.cnt;
            ls.next = c.next;
        } else {
            ls.in.k[ls.cnt] = p.in.k[i - 1];
            memcpy(ls.in.k + ls.cnt + 1, c.in.k, c.cnt * sizeof(Key));
            memcpy(ls.in.ch + ls.cnt + 1, c.in.ch, (c.cnt + 1) * sizeof(i64));
            ls.cnt += c.cnt + 1;
        }
        writeNode(p.in.ch[i - 1], ls);
        for (int j = i - 1; j + 1 < p.cnt; j++) p.in.k[j] = p.in.k[j + 1];
        for (int j = i; j < p.cnt; j++) p.in.ch[j] = p.in.ch[j + 1];
        p.cnt--;
        writeNode(ppid, p);
    } else {
        // merge right sibling into c
        Node rs; readNode(p.in.ch[1], rs);
        if (c.is_leaf) {
            memcpy(c.lk + c.cnt, rs.lk, rs.cnt * sizeof(Key));
            c.cnt += rs.cnt;
            c.next = rs.next;
        } else {
            c.in.k[c.cnt] = p.in.k[0];
            memcpy(c.in.k + c.cnt + 1, rs.in.k, rs.cnt * sizeof(Key));
            memcpy(c.in.ch + c.cnt + 1, rs.in.ch, (rs.cnt + 1) * sizeof(i64));
            c.cnt += rs.cnt + 1;
        }
        writeNode(cpid, c);
        for (int j = 0; j + 1 < p.cnt; j++) p.in.k[j] = p.in.k[j + 1];
        for (int j = 1; j < p.cnt; j++) p.in.ch[j] = p.in.ch[j + 1];
        p.cnt--;
        writeNode(ppid, p);
    }
}

// returns true if subtree at pid underflowed
static bool del(i64 pid, const Key& k) {
    Node nd; readNode(pid, nd);
    if (nd.is_leaf) {
        int pos = 0;
        while (pos < nd.cnt && cmpKey(nd.lk[pos], k) < 0) pos++;
        if (pos < nd.cnt && cmpKey(nd.lk[pos], k) == 0) {
            for (int i = pos; i + 1 < nd.cnt; i++) nd.lk[i] = nd.lk[i + 1];
            nd.cnt--;
            writeNode(pid, nd);
        }
        return nd.cnt < LMIN;
    }
    int i = 0;
    while (i < nd.cnt && cmpKey(nd.in.k[i], k) <= 0) i++;
    if (del(nd.in.ch[i], k)) fixChild(nd, pid, i);
    else writeNode(pid, nd); // child didn't underflow; nd unchanged, but harmless
    return nd.cnt < MMIN;
}

static void deleteKey(const Key& k) {
    del(hdr.root, k);
    Node rt; readNode(hdr.root, rt);
    if (!rt.is_leaf && rt.cnt == 0) {
        hdr.root = rt.in.ch[0];
        writeHeader();
    }
}

// ---------------- output buffer ----------------
static char outbuf[1 << 20];
static int outlen = 0;
static void outFlush() { if (outlen) { fwrite(outbuf, 1, outlen, stdout); outlen = 0; } }
static void outRaw(const char* s, int n) {
    if (outlen + n >= (int)sizeof(outbuf)) outFlush();
    memcpy(outbuf + outlen, s, n); outlen += n;
}
static void outStr(const char* s) { outRaw(s, (int)strlen(s)); }
static void outInt(int v) {
    char tmp[16]; int n = sprintf(tmp, "%d", v);
    outRaw(tmp, n);
}

static void findKey(const char* idx) {
    Key lo; memset(lo.s, 0, 64);
    size_t ln = strlen(idx); if (ln > 64) ln = 64;
    memcpy(lo.s, idx, ln);
    lo.v = -1;
    i64 pid = hdr.root;
    Node nd;
    for (;;) {
        readNode(pid, nd);
        if (nd.is_leaf) break;
        int i = 0;
        while (i < nd.cnt && cmpKey(nd.in.k[i], lo) <= 0) i++;
        pid = nd.in.ch[i];
    }
    bool any = false, done = false;
    for (;;) {
        for (int j = 0; j < nd.cnt; j++) {
            int c = memcmp(nd.lk[j].s, lo.s, 64);
            if (c == 0) {
                if (any) outRaw(" ", 1);
                outInt(nd.lk[j].v);
                any = true;
            } else if (c > 0) { done = true; break; }
        }
        if (done || nd.next == -1 || nd.cnt == 0) break;
        pid = nd.next;
        readNode(pid, nd);
    }
    if (!any) outStr("null");
    outRaw("\n", 1);
}

// ---------------- fast input ----------------
static char inbuf[1 << 16];
static int inpos = 0, inlen = 0;
static int getCh() {
    if (inpos >= inlen) {
        inlen = (int)fread(inbuf, 1, sizeof(inbuf), stdin);
        inpos = 0;
        if (inlen <= 0) return -1;
    }
    return inbuf[inpos++];
}
// read next whitespace-delimited token into buf; returns length or -1 at EOF
static int nextToken(char* buf) {
    int c, n = 0;
    do { c = getCh(); } while (c == ' ' || c == '\n' || c == '\r' || c == '\t');
    if (c == -1) return -1;
    while (c != -1 && c != ' ' && c != '\n' && c != '\r' && c != '\t') {
        buf[n++] = (char)c;
        c = getCh();
    }
    buf[n] = 0;
    return n;
}

int main() {
    initStore();
    char cmd[16], idx[80];
    if (nextToken(cmd) < 0) return 0;
    long n = atol(cmd);
    for (long t = 0; t < n; t++) {
        if (nextToken(cmd) < 0) break;
        char c = cmd[0];
        if (c == 'i') {
            nextToken(idx);
            char vb[16]; nextToken(vb);
            Key k; memset(k.s, 0, 64);
            size_t ln = strlen(idx); if (ln > 64) ln = 64;
            memcpy(k.s, idx, ln);
            k.v = atoi(vb);
            insertKey(k);
        } else if (c == 'd') {
            nextToken(idx);
            char vb[16]; nextToken(vb);
            Key k; memset(k.s, 0, 64);
            size_t ln = strlen(idx); if (ln > 64) ln = 64;
            memcpy(k.s, idx, ln);
            k.v = atoi(vb);
            deleteKey(k);
        } else if (c == 'f') {
            nextToken(idx);
            findKey(idx);
        }
    }
    outFlush();
    writeHeader();
    close(fd);
    return 0;
}
