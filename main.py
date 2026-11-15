#!/usr/bin/env python3
"""github-core-clone - a standalone GitHub-compatible git forge.

One process, Python 3.13 stdlib only. Serves:
  * git smart HTTP (protocol v2 upload-pack, v0 receive-pack)
  * REST v3 API (/api/v3)
  * GraphQL v4 (/api/graphql)
  * MCP over Streamable HTTP (/mcp)

All state is in-memory, deterministic: every timestamp is fixed, ids are
assigned in creation order, and no wall clock or randomness ever reaches a
response. Lifecycle: bind an ephemeral port, register it with the suite
environment (MAKEFUN_ENV_URL), serve until the environment reports done.
"""

import base64
import difflib
import hashlib
import http.client
import io
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.request
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# ---------------------------------------------------------------- constants

VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"

# Precomputed response pieces for the single-write send path.
# wfile is unbuffered (wbufsize=0), so every write() is a syscall; the
# stdlib send_response/send_header/end_headers path costs several method
# calls plus two writes (headers, body). Building one bytes object and
# writing once removes that overhead on every response.
_STATUS_MSG = {
    200: b"OK", 201: b"Created", 204: b"No Content", 400: b"Bad Request",
    401: b"Unauthorized", 403: b"Forbidden", 404: b"Not Found",
    405: b"Method Not Allowed", 409: b"Conflict",
    422: b"Unprocessable Entity", 500: b"Internal Server Error",
    501: b"Not Implemented", 505: b"HTTP Version Not Supported",
}
_SERVER_HDR = ("Server: github-core-clone/1.0.0 Python/%s\r\n"
               % sys.version.split()[0]).encode("latin-1")
FIXED_TS = "2025-01-01T00:00:00Z"
FIXED_EPOCH = 1735689600  # 2025-01-01T00:00:00Z
FIXED_TZ = "+0000"

ZERO_OID = "0" * 40
GIT_IDENTITY = "adaiversen <adaiversen@example.invalid>"

SERVER_NAME = "github-core-clone"
SERVER_VERSION = "1.0.0"

ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")
ENV_PORT = int(os.environ.get("MAKEFUN_ENV_PORT", "8080") or "8080")
SHOP_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
FORGE_PORT = int(os.environ.get("FORGE_PORT", "0") or "0")


def env_token():
    """Token the suite presents. In the trial pod this is MAKEFUN_SHOP_TOKEN;
    locally (env var unset) any non-empty Bearer token is accepted."""
    return SHOP_TOKEN


# ------------------------------------------------------------- git objects

def hash_object(obj_type, data):
    """SHA-1 object id for `type size\\0data`."""
    head = ("%s %d\0" % (obj_type, len(data))).encode()
    return hashlib.sha1(head + data).hexdigest()


def oid_bytes(oid):
    return bytes.fromhex(oid)


def oid_hex(raw):
    return raw.hex()


def parse_tree(data):
    """-> list of (mode_bytes, name_bytes, oid_hex) in stored order."""
    entries = []
    i = 0
    n = len(data)
    while i < n:
        sp = data.index(b" ", i)
        mode = data[i:sp]
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul]
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return entries


def tree_sort_key(entry):
    mode, name, _oid = entry
    return name + (b"/" if mode == b"40000" else b"")


def build_tree(entries):
    """entries: list of (mode_bytes, name_bytes, oid_hex). Sorted git-style."""
    out = bytearray()
    for mode, name, oid in sorted(entries, key=tree_sort_key):
        out += mode + b" " + name + b"\0" + bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    """-> (tree_oid, [parent_oids], author_line, committer_line, message)."""
    text = data.decode("utf-8", "surrogateescape")
    head, _sep, message = text.partition("\n\n")
    tree = None
    parents = []
    author = ""
    committer = ""
    for line in head.split("\n"):
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
        elif line.startswith("author "):
            author = line[7:]
        elif line.startswith("committer "):
            committer = line[10:]
    return tree, parents, author, committer, message


def build_commit(tree, parents, message, author=GIT_IDENTITY,
                 committer=None, epoch=FIXED_EPOCH):
    if committer is None:
        committer = author
    lines = ["tree %s" % tree]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s %d %s" % (author, epoch, FIXED_TZ))
    lines.append("committer %s %d %s" % (committer, epoch, FIXED_TZ))
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8", "surrogateescape")


def parse_tag(data):
    """-> (object_oid, object_type, tag_name, tagger_line, message)."""
    text = data.decode("utf-8", "surrogateescape")
    head, _sep, message = text.partition("\n\n")
    obj = None
    otype = None
    name = ""
    tagger = ""
    for line in head.split("\n"):
        if line.startswith("object "):
            obj = line[7:].strip()
        elif line.startswith("type "):
            otype = line[5:].strip()
        elif line.startswith("tag "):
            name = line[4:]
        elif line.startswith("tagger "):
            tagger = line[7:]
    return obj, otype, name, tagger, message


def build_tag(obj, otype, name, message, tagger=GIT_IDENTITY, epoch=FIXED_EPOCH):
    text = ("object %s\ntype %s\ntag %s\ntagger %s %d %s\n\n%s"
            % (obj, otype, name, tagger, epoch, FIXED_TZ))
    return text.encode("utf-8", "surrogateescape")


def apply_delta(base, delta):
    """Apply a git binary delta. Returns the result bytes."""
    def read_varint(buf, pos):
        value = 0
        shift = 0
        while True:
            b = buf[pos]
            pos += 1
            value |= (b & 0x7F) << shift
            shift += 7
            if not (b & 0x80):
                return value, pos
    src_size, pos = read_varint(delta, 0)
    if src_size != len(base):
        raise ValueError("delta source size mismatch")
    dst_size, pos = read_varint(delta, 0)
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for i in range(4):
                if op & (1 << i):
                    cp_off |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    cp_size |= delta[pos] << (8 * i)
                    pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != dst_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def read_varint_pack(data, pos):
    """Pack entry size varint: low 4 bits first byte, then 7 bits/byte."""
    b = data[pos]
    pos += 1
    size = b & 0x0F
    shift = 4
    while b & 0x80:
        b = data[pos]
        pos += 1
        size |= (b & 0x7F) << shift
        shift += 7
    return size, pos


def read_pack(data):
    """Parse a pack file. -> dict oid -> (type, bytes). Raises ValueError."""
    if len(data) < 32 or data[:4] != b"PACK":
        raise ValueError("not a pack")
    version = int.from_bytes(data[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(data[8:12], "big")
    trailer = data[-20:]
    if hashlib.sha1(data[:-20]).digest() != trailer:
        raise ValueError("pack trailer checksum mismatch")
    body = data[12:-20]
    pos = 0
    raw = []  # (type_code, size, data, offset, base_ref)
    by_offset = {}
    for _ in range(count):
        start = pos
        b = body[pos]
        type_code = (b >> 4) & 0x07
        size, pos = read_varint_pack(body, pos)
        if type_code in (6, 7):
            if type_code == 6:  # OFS_DELTA
                bb = body[pos]
                pos += 1
                off = bb & 0x7F
                while bb & 0x80:
                    bb = body[pos]
                    pos += 1
                    off = ((off + 1) << 7) | (bb & 0x7F)
                base_off = start - off
                ref = ("ofs", base_off)
            else:  # REF_DELTA
                ref = ("ref", body[pos:pos + 20].hex())
                pos += 20
        else:
            ref = None
        decomp = zlib.decompressobj()
        chunk = decomp.decompress(body[pos:])
        consumed = len(body[pos:]) - len(decomp.unused_data)
        if len(chunk) != size:
            raise ValueError("pack entry size mismatch")
        pos += consumed
        raw.append((type_code, size, chunk, start, ref))
        by_offset[start] = len(raw) - 1
    type_names = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}
    resolved = {}

    def resolve(idx):
        if idx in resolved:
            return resolved[idx]
        type_code, size, chunk, start, ref = raw[idx]
        if ref is None:
            result = (type_names[type_code], chunk)
        else:
            if ref[0] == "ofs":
                base_idx = by_offset[ref[1]]
            else:
                base_idx = None
                # ref-delta base must already be known by oid: look it up
                # in the objects we already resolved or in this pack.
                base_oid = ref[1]
                base = None
                for j in range(len(raw)):
                    if j == idx:
                        continue
                    t2, c2 = resolve(j)
                    if hash_object(t2, c2) == base_oid:
                        base = (t2, c2)
                        break
                if base is None:
                    raise ValueError("ref-delta base %s not found" % base_oid)
                result = (base[0], apply_delta(base[1], chunk))
                resolved[idx] = result
                return result
            base = resolve(base_idx)
            result = (base[0], apply_delta(base[1], chunk))
        resolved[idx] = result
        return result

    out = {}
    for i in range(len(raw)):
        otype, data = resolve(i)
        out[hash_object(otype, data)] = (otype, data)
    return out


def write_pack(objects):
    """objects: list of (type, bytes). -> pack bytes (plain entries, v2)."""
    type_codes = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
    out = bytearray()
    out += b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")
    for otype, data in objects:
        code = type_codes[otype]
        size = len(data)
        first = (code << 4) | (size & 0x0F)
        size >>= 4
        if size:
            first |= 0x80
        out.append(first)
        while size:
            b = size & 0x7F
            size >>= 7
            if size:
                b |= 0x80
            out.append(b)
        out += zlib.compress(data)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


# -------------------------------------------------------------- pkt-lines

def pkt(data):
    """Wrap bytes (without trailing newline handling) in a pkt-line."""
    if isinstance(data, str):
        data = data.encode()
    return ("%04x" % (len(data) + 4)).encode() + data


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def parse_pkt_lines(buf):
    """Parse a pkt-line stream. -> list of (kind, payload) where kind is
    'data', 'flush' or 'delim'. Raises ValueError on malformed input."""
    out = []
    pos = 0
    n = len(buf)
    while pos < n:
        if pos + 4 > n:
            raise ValueError("truncated pkt-line header")
        hexlen = buf[pos:pos + 4]
        try:
            length = int(hexlen, 16)
        except ValueError:
            raise ValueError("bad pkt-line length %r" % hexlen)
        if length == 0:
            out.append(("flush", b""))
            pos += 4
        elif length == 1:
            out.append(("delim", b""))
            pos += 4
        elif length < 4 or pos + length > n:
            raise ValueError("bad pkt-line length %d" % length)
        else:
            out.append(("data", buf[pos + 4:pos + length]))
            pos += length
    return out


def split_pack_after_flush(body):
    """Split a receive-pack POST body at the first flush pkt-line.
    -> (pkt_lines_before_flush, raw_pack_bytes)."""
    pos = 0
    n = len(body)
    while pos < n:
        if pos + 4 > n:
            raise ValueError("truncated pkt-line header")
        length = int(body[pos:pos + 4], 16)
        if length == 0:
            return body[:pos], body[pos + 4:]
        if length < 4 or pos + length > n:
            raise ValueError("bad pkt-line length")
        pos += length
    return body, b""


def sideband_pack(pack_bytes):
    """Wrap pack bytes in sideband band-1 pkt-lines (<=65516 payload)."""
    out = bytearray()
    for i in range(0, len(pack_bytes), 65515):
        chunk = pack_bytes[i:i + 65515]
        out += pkt(b"\x01" + chunk)
    return bytes(out)


def sideband_lines(lines):
    """Wrap text lines in sideband band-1 pkt-lines (one line per packet)."""
    out = bytearray()
    for line in lines:
        if isinstance(line, str):
            line = line.encode()
        out += pkt(b"\x01" + line)
    out += pkt(b"\x01" + b"")  # flush inside band 1
    return bytes(out)

# ------------------------------------------------------------------ store

class Issue:
    __slots__ = ("id", "number", "title", "body", "state", "labels",
                 "comments", "created_seq", "_json")

    def __init__(self, oid, number, title, body, labels, seq):
        self.id = oid
        self.number = number
        self.title = title
        self.body = body or ""
        self.state = "open"
        self.labels = list(labels)
        self.comments = []  # list of (comment_id, body)
        self.created_seq = seq
        self._json = None  # cached serialized bytes, None when dirty


class Pull:
    __slots__ = ("id", "number", "title", "body", "state", "merged",
                 "merged_at", "merge_commit_sha", "head", "base",
                 "head_sha", "base_sha", "created_seq")

    def __init__(self, oid, number, title, body, head, base,
                 head_sha, base_sha, seq):
        self.id = oid
        self.number = number
        self.title = title
        self.body = body or ""
        self.state = "open"
        self.merged = False
        self.merged_at = None
        self.merge_commit_sha = None
        self.head = head
        self.base = base
        self.head_sha = head_sha
        self.base_sha = base_sha
        self.created_seq = seq


class Repo:
    def __init__(self, db_id, name, owner_login, description, private):
        self.id = db_id
        self.name = name
        self.owner = owner_login
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = "main"
        self.refs = {}        # refname -> oid hex
        self.objects = {}     # oid hex -> (type, bytes)
        self.labels = {}      # name -> color
        self.issues = {}      # number -> Issue
        self.pulls = {}       # number -> Pull
        self.next_number = 1  # shared issue+PR counter
        self.next_comment_id = 1
        self.version = 0      # bumped on any object/ref mutation; keys
                              # the fetch-response cache

    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def head_tip(self):
        return self.refs.get("refs/heads/" + self.default_branch)


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}          # (owner, name) -> Repo
        self.repos_by_id = {}    # db_id -> Repo
        self.next_id = 1         # global object id counter
        self.seq = 0             # creation sequence counter
        self.req_counter = 0     # X-GitHub-Request-Id counter

    def new_id(self):
        v = self.next_id
        self.next_id += 1
        return v

    def new_seq(self):
        self.seq += 1
        return self.seq

    def next_req_id(self):
        self.req_counter += 1
        return "req-%d" % self.req_counter

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def create_repo(self, name, description, private, owner=VIEWER_LOGIN):
        if (owner, name) in self.repos:
            return None
        db_id = self.new_id()
        repo = Repo(db_id, name, owner, description, private)
        self.repos[(owner, name)] = repo
        self.repos_by_id[db_id] = repo
        return repo

    def delete_repo(self, owner, name):
        repo = self.repos.pop((owner, name), None)
        if repo is not None:
            self.repos_by_id.pop(repo.id, None)
        return repo


STORE = Store()

# Cache of v2 fetch responses: identical fetch requests against an
# unchanged repo (the 50-concurrent-clone workload) reuse the pack.
# Key: (repo id, repo version, wants, haves, shallows, depth).
_FETCH_CACHE = {}
_FETCH_CACHE_MAX = 16


def fetch_cache_get(key):
    return _FETCH_CACHE.get(key)


def fetch_cache_put(key, body):
    if len(_FETCH_CACHE) >= _FETCH_CACHE_MAX:
        _FETCH_CACHE.pop(next(iter(_FETCH_CACHE)))
    _FETCH_CACHE[key] = body


# Serializes a fetch-response computation on a cache miss, so 50
# concurrent clones of one repo compute the pack once and the rest hit
# the cache instead of all 50 doing the same work under the GIL.
_FETCH_COMPUTE_LOCK = threading.Lock()

# --------------------------------------------------- git reachability etc.

def collect_reachable(repo, roots, depth=None):
    """All object ids reachable from the given commit/tag oids.
    depth: if set, only commits within <depth> generations from roots
    (depth=1 -> root commits only) plus their trees/blobs."""
    seen = set()
    commits = []  # (oid, generation)
    for r in roots:
        if r in repo.objects:
            commits.append((r, 0))
    queue = list(commits)
    qi = 0
    while qi < len(queue):
        oid, gen = queue[qi]
        qi += 1
        if oid in seen:
            continue
        entry = repo.objects.get(oid)
        if entry is None:
            continue
        otype, data = entry
        seen.add(oid)
        if otype == "commit":
            tree, parents, _a, _c, _m = parse_commit(data)
            if tree:
                collect_tree(repo, tree, seen)
            if depth is None or gen + 1 < depth:
                for p in parents:
                    if p not in seen:
                        queue.append((p, gen + 1))
        elif otype == "tag":
            obj, _t, _n, _g, _m = parse_tag(data)
            if obj and obj not in seen:
                queue.append((obj, gen))
        elif otype == "tree":
            collect_tree(repo, oid, seen)
    return seen


def collect_tree(repo, tree_oid, seen):
    """Add a tree and everything under it to `seen` (iterative)."""
    stack = [tree_oid]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        entry = repo.objects.get(oid)
        if entry is None:
            continue
        otype, data = entry
        if otype != "tree":
            seen.add(oid)
            continue
        seen.add(oid)
        for mode, _name, child in parse_tree(data):
            if mode == b"40000":
                stack.append(child)
            elif mode == b"160000":
                continue  # gitlink: not stored
            else:
                seen.add(child)


def peel_to_commit(repo, oid):
    """Follow tag objects to the commit they point at. Returns commit oid
    or None if the chain does not end in a commit."""
    seen = set()
    cur = oid
    while cur and cur not in seen:
        seen.add(cur)
        entry = repo.objects.get(cur)
        if entry is None:
            return None
        otype, data = entry
        if otype == "commit":
            return cur
        if otype == "tag":
            cur, _t, _n, _g, _m = parse_tag(data)
            continue
        return None
    return None


def is_ancestor(repo, ancestor, descendant):
    """True if `ancestor` (commit oid) is reachable from `descendant`."""
    if ancestor == descendant:
        return True
    anc = peel_to_commit(repo, ancestor)
    desc = peel_to_commit(repo, descendant)
    if anc is None or desc is None:
        return False
    if anc == desc:
        return True
    seen = set()
    stack = [desc]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        entry = repo.objects.get(cur)
        if entry is None or entry[0] != "commit":
            continue
        _tree, parents, _a, _c, _m = parse_commit(entry[1])
        for p in parents:
            if p == anc:
                return True
            stack.append(p)
    return False


def commit_ancestors(repo, tip):
    """Set of commit oids reachable from tip (following parents)."""
    out = set()
    stack = [tip]
    while stack:
        cur = stack.pop()
        if cur in out:
            continue
        entry = repo.objects.get(cur)
        if entry is None or entry[0] != "commit":
            continue
        out.add(cur)
        _tree, parents, _a, _c, _m = parse_commit(entry[1])
        stack.extend(parents)
    return out


def merge_base(repo, head_tip, base_tip):
    """Newest common ancestor commit of two tips (first found walking the
    head side in visit order, intersected with base ancestors)."""
    base_anc = commit_ancestors(repo, base_tip)
    seen = set()
    stack = [head_tip]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        if cur in base_anc:
            return cur
        entry = repo.objects.get(cur)
        if entry is None or entry[0] != "commit":
            continue
        _tree, parents, _a, _c, _m = parse_commit(entry[1])
        stack.extend(parents)
    return None


def flatten_tree(repo, tree_oid):
    """-> dict path -> (mode_bytes, oid_hex) for all blobs under a tree."""
    out = {}
    stack = [(tree_oid, "")]
    while stack:
        oid, prefix = stack.pop()
        entry = repo.objects.get(oid)
        if entry is None or entry[0] != "tree":
            continue
        for mode, name, child in parse_tree(entry[1]):
            path = prefix + name.decode("utf-8", "surrogateescape")
            if mode == b"40000":
                stack.append((child, path + "/"))
            elif mode == b"160000":
                continue
            else:
                out[path] = (mode, child)
    return out


def build_tree_from_flat(repo, flat):
    """flat: dict path -> (mode_bytes, blob_oid). Builds nested trees,
    stores them in repo.objects, returns the root tree oid."""
    # group paths by directory
    dirs = {}

    def ensure_dir(path):
        if path not in dirs:
            dirs[path] = {}
        return dirs[path]

    ensure_dir("")
    for path, (mode, oid) in flat.items():
        parts = path.split("/")
        cur = ""
        for part in parts[:-1]:
            cur = cur + part + "/" if cur else part + "/"
            ensure_dir(cur)
        ensure_dir(cur if False else "/".join(parts[:-1]) + ("/" if len(parts) > 1 else ""))
        dirs["/".join(parts[:-1]) + ("/" if len(parts) > 1 else "")][parts[-1]] = (mode, oid)
    # build bottom-up: deepest dirs first
    tree_oids = {}
    for d in sorted(dirs.keys(), key=lambda p: -p.count("/")):
        entries = []
        for name, (mode, oid) in dirs[d].items():
            entries.append((mode, name.encode("utf-8", "surrogateescape"), oid))
        # subdirectories of d
        for sub in list(dirs.keys()):
            if sub == d or not sub.startswith(d):
                continue
            rest = sub[len(d):]
            if "/" not in rest.rstrip("/"):
                subname = rest.rstrip("/")
                entries.append((b"40000", subname.encode("utf-8", "surrogateescape"),
                                tree_oids[sub]))
        tree_data = build_tree(entries)
        tree_oid = hash_object("tree", tree_data)
        repo.objects[tree_oid] = ("tree", tree_data)
        tree_oids[d] = tree_oid
    return tree_oids[""]


def three_way_merge(repo, base_tree, head_tree, base2_tree):
    """Three-way merge of flat file maps. Returns (merged_flat, conflict)
    where merged_flat is dict path -> (mode, oid) or None if conflict."""
    b = flatten_tree(repo, base_tree) if base_tree else {}
    h = flatten_tree(repo, head_tree) if head_tree else {}
    c = flatten_tree(repo, base2_tree) if base2_tree else {}
    merged = {}
    for path in sorted(set(b) | set(h) | set(c)):
        bv = b.get(path)
        hv = h.get(path)
        cv = c.get(path)
        if hv == bv:
            if cv is not None:
                merged[path] = cv
        elif cv == bv:
            if hv is not None:
                merged[path] = hv
        elif hv == cv:
            if hv is not None:
                merged[path] = hv
        else:
            return None, True
    return merged, False


def diff_files(repo, base_tree, head_tree):
    """Line diffs between two trees. -> list of dicts with filename, status,
    additions, deletions, changes."""
    b = flatten_tree(repo, base_tree) if base_tree else {}
    h = flatten_tree(repo, head_tree) if head_tree else {}
    out = []
    for path in sorted(set(b) | set(h)):
        bv = b.get(path)
        hv = h.get(path)
        if bv == hv:
            continue
        if bv is None:
            status = "added"
            old_lines, new_lines = [], _blob_lines(repo, hv[1])
        elif hv is None:
            status = "removed"
            old_lines, new_lines = _blob_lines(repo, bv[1]), []
        else:
            status = "modified"
            old_lines = _blob_lines(repo, bv[1])
            new_lines = _blob_lines(repo, hv[1])
        sm = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
        additions = deletions = 0
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag in ("insert", "replace"):
                additions += j2 - j1
            if tag in ("delete", "replace"):
                deletions += i2 - i1
        out.append({
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
        })
    return out


def _blob_lines(repo, oid):
    entry = repo.objects.get(oid)
    if entry is None:
        return []
    text = entry[1].decode("utf-8", "surrogateescape")
    return text.splitlines()


# ------------------------------------------------------------ global ids

def gid(kind, *parts):
    raw = ":".join([kind] + [str(p) for p in parts])
    return base64.b64encode(raw.encode()).decode()


def ungid(value):
    """Decode a global id -> (kind, [parts]) or None."""
    if not isinstance(value, str):
        return None
    try:
        padded = value + "=" * (-len(value) % 4)
        raw = base64.b64decode(padded, validate=False).decode()
    except Exception:
        return None
    parts = raw.split(":")
    if len(parts) < 2:
        return None
    return parts[0], parts[1:]


def cursor_encode(offset):
    return base64.b64encode(("cursor:%d" % offset).encode()).decode()


def cursor_decode(value):
    if not isinstance(value, str):
        return 0
    try:
        padded = value + "=" * (-len(value) % 4)
        raw = base64.b64decode(padded).decode()
        if raw.startswith("cursor:"):
            return int(raw[7:])
    except Exception:
        return 0
    return 0

# ------------------------------------------------------ shared operations

def repo_json(repo):
    return {
        "id": repo.id,
        "databaseId": repo.id,
        "name": repo.name,
        "full_name": repo.full_name(),
        "nameWithOwner": repo.full_name(),
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "html_url": "https://example.invalid/%s" % repo.full_name(),
        "url": "/api/v3/repos/%s" % repo.full_name(),
        "created_at": FIXED_TS,
        "updated_at": FIXED_TS,
        "has_issues": True,
        "hasIssuesEnabled": True,
        "viewerPermission": "ADMIN",
    }


def issue_json(issue):
    return {
        "id": issue.id,
        "number": issue.number,
        "title": issue.title,
        "body": issue.body,
        "state": issue.state,
        "labels": [{"name": n} for n in issue.labels],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
        "created_at": FIXED_TS,
        "updated_at": FIXED_TS,
        "comments": len(issue.comments),
    }


def issue_json_bytes(issue):
    """Serialized issue JSON, cached on the issue; any mutation must
    reset issue._json to None (see the mutation sites). The read
    workload GETs the same issue 2,000 times, so this removes a dict
    build + json.dumps per request."""
    b = issue._json
    if b is None:
        b = json.dumps(issue_json(issue)).encode()
        issue._json = b
    return b


def pr_json(pr):
    return {
        "id": pr.id,
        "number": pr.number,
        "title": pr.title,
        "body": pr.body,
        "state": pr.state,
        "merged": pr.merged,
        "merged_at": pr.merged_at,
        "merge_commit_sha": pr.merge_commit_sha,
        "head": {"ref": pr.head, "sha": pr.head_sha,
                 "label": "%s:%s" % (VIEWER_LOGIN, pr.head)},
        "base": {"ref": pr.base, "sha": pr.base_sha,
                 "label": "%s:%s" % (VIEWER_LOGIN, pr.base)},
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
        "created_at": FIXED_TS,
        "updated_at": FIXED_TS,
    }


def create_issue_op(repo, title, body, labels):
    """Returns (issue, error_message)."""
    with STORE.lock:
        for name in labels or []:
            if name not in repo.labels:
                return None, "Label '%s' does not exist" % name
        number = repo.next_number
        repo.next_number += 1
        issue = Issue(STORE.new_id(), number, title, body, labels or [],
                      STORE.new_seq())
        repo.issues[number] = issue
        return issue, None


def close_issue_op(repo, number):
    with STORE.lock:
        issue = repo.issues.get(number)
        if issue is None:
            return None
        issue.state = "closed"
        issue._json = None
        return issue


def create_pr_op(repo, title, body, head, base):
    """Returns (pr, error_message, status)."""
    with STORE.lock:
        head_tip = repo.refs.get("refs/heads/" + head)
        base_tip = repo.refs.get("refs/heads/" + base)
        if head_tip is None or base_tip is None:
            return None, "head or base branch not found", 404
        for pr in repo.pulls.values():
            if (pr.state == "open" and pr.head == head and pr.base == base):
                return None, "A pull request already exists for %s" % head, 422
        number = repo.next_number
        repo.next_number += 1
        pr = Pull(STORE.new_id(), number, title, body, head, base,
                  head_tip, base_tip, STORE.new_seq())
        repo.pulls[number] = pr
        return pr, None, 201


def merge_pr_op(repo, number, method="squash"):
    """Returns (sha, error_message, status)."""
    with STORE.lock:
        pr = repo.pulls.get(number)
        if pr is None:
            return None, "Not Found", 404
        if pr.merged:
            return None, "Pull request is already merged", 405
        if pr.state != "open":
            return None, "Pull request is closed", 405
        base_tip = repo.refs.get("refs/heads/" + pr.base)
        head_tip = repo.refs.get("refs/heads/" + pr.head)
        if base_tip is None or head_tip is None:
            return None, "head or base branch not found", 404
        head_commit = repo.objects.get(head_tip)
        base_commit = repo.objects.get(base_tip)
        if head_commit is None or base_commit is None:
            return None, "head or base commit not found", 404
        head_tree = parse_commit(head_commit[1])[0]
        base_tree = parse_commit(base_commit[1])[0]
        mb = merge_base(repo, head_tip, base_tip)
        if mb is None:
            return None, "no merge base", 405
        mb_tree = parse_commit(repo.objects[mb][1])[0]
        merged_flat, conflict = three_way_merge(repo, mb_tree, head_tree,
                                                base_tree)
        if conflict:
            return None, "Merge conflict", 405
        merged_tree = build_tree_from_flat(repo, merged_flat)
        msg = pr.title + "\n"
        commit_data = build_commit(merged_tree, [base_tip], msg)
        sha = hash_object("commit", commit_data)
        repo.objects[sha] = ("commit", commit_data)
        repo.refs["refs/heads/" + pr.base] = sha
        repo.version += 1
        pr.state = "closed"
        pr.merged = True
        pr.merged_at = FIXED_TS
        pr.merge_commit_sha = sha
        return sha, None, 200


def resolve_ref(repo, ref):
    """Resolve a branch name or commit sha to a tip commit oid (or None)."""
    if ref is None:
        return repo.head_tip()
    if ref in repo.objects and repo.objects[ref][0] == "commit":
        return ref
    return repo.refs.get("refs/heads/" + ref)


def get_file_at_commit(repo, commit_oid, path):
    """-> (blob_oid, blob_bytes) for a path at a commit, or None."""
    entry = repo.objects.get(commit_oid)
    if entry is None or entry[0] != "commit":
        return None
    tree_oid = parse_commit(entry[1])[0]
    flat = flatten_tree(repo, tree_oid)
    hit = flat.get(path)
    if hit is None:
        return None
    _mode, blob_oid = hit
    blob = repo.objects.get(blob_oid)
    if blob is None:
        return None
    return blob_oid, blob[1]


def write_contents_op(repo, path, content_bytes, message, branch, sha):
    """PUT /contents semantics. Returns (result_dict, error, status)."""
    with STORE.lock:
        branch = branch or repo.default_branch
        tip = repo.refs.get("refs/heads/" + branch)
        if tip is None and branch != repo.default_branch:
            return None, "branch not found", 404
        parent_tree = None
        parents = []
        if tip is not None:
            tip_entry = repo.objects.get(tip)
            if tip_entry is None or tip_entry[0] != "commit":
                return None, "branch tip not a commit", 404
            parent_tree = parse_commit(tip_entry[1])[0]
            parents = [tip]
        flat = flatten_tree(repo, parent_tree) if parent_tree else {}
        existing = flat.get(path)
        blob_oid = hash_object("blob", content_bytes)
        if existing is not None:
            if sha is not None and sha != existing[1]:
                return None, "sha mismatch", 409
            if sha is None:
                return None, "sha required to update existing file", 409
            status = 200
        else:
            status = 201
        repo.objects[blob_oid] = ("blob", content_bytes)
        flat[path] = (b"100644", blob_oid)
        tree_oid = build_tree_from_flat(repo, flat)
        commit_data = build_commit(tree_oid, parents, message + "\n")
        commit_oid = hash_object("commit", commit_data)
        repo.objects[commit_oid] = ("commit", commit_data)
        repo.refs["refs/heads/" + branch] = commit_oid
        repo.version += 1
        return {
            "content": {
                "name": path.rsplit("/", 1)[-1],
                "path": path,
                "sha": blob_oid,
                "size": len(content_bytes),
                "encoding": "base64",
                "type": "file",
            },
            "commit": {"sha": commit_oid, "message": message},
        }, None, status


def delete_contents_op(repo, path, message, sha):
    """DELETE /contents semantics. Returns (result_dict, error, status)."""
    with STORE.lock:
        tip = repo.head_tip()
        if tip is None:
            return None, "Not Found", 404
        tip_entry = repo.objects.get(tip)
        tree_oid = parse_commit(tip_entry[1])[0]
        flat = flatten_tree(repo, tree_oid)
        existing = flat.get(path)
        if existing is None:
            return None, "Not Found", 404
        if sha is not None and sha != existing[1]:
            return None, "sha mismatch", 409
        del flat[path]
        tree_oid = build_tree_from_flat(repo, flat)
        commit_data = build_commit(tree_oid, [tip], message + "\n")
        commit_oid = hash_object("commit", commit_data)
        repo.objects[commit_oid] = ("commit", commit_data)
        repo.refs["refs/heads/" + repo.default_branch] = commit_oid
        repo.version += 1
        return {"commit": {"sha": commit_oid, "message": message}}, None, 200


def list_commits(repo, ref):
    """Newest-first list of {sha, commit:{message}} from a ref."""
    tip = resolve_ref(repo, ref)
    if tip is None:
        return None
    out = []
    seen = set()
    stack = [tip]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        entry = repo.objects.get(cur)
        if entry is None or entry[0] != "commit":
            continue
        _tree, parents, _a, _c, msg = parse_commit(entry[1])
        out.append({"sha": cur,
                    "commit": {"message": msg[:-1] if msg.endswith("\n") else msg,
                               "author": {"name": VIEWER_NAME},
                               "committer": {"name": VIEWER_NAME}}})
        stack.extend(parents)
    return out


def graphql_state(issue):
    return "CLOSED" if issue.state == "closed" else "OPEN"


def graphql_pr_state(pr):
    if pr.merged:
        return "MERGED"
    return "CLOSED" if pr.state == "closed" else "OPEN"


def pr_mergeable(repo, pr):
    """MERGEABLE / CONFLICTING / UNKNOWN for a PR."""
    head_tip = repo.refs.get("refs/heads/" + pr.head)
    base_tip = repo.refs.get("refs/heads/" + pr.base)
    if head_tip is None or base_tip is None:
        return "UNKNOWN"
    head_entry = repo.objects.get(head_tip)
    base_entry = repo.objects.get(base_tip)
    if head_entry is None or base_entry is None:
        return "UNKNOWN"
    mb = merge_base(repo, head_tip, base_tip)
    if mb is None:
        return "UNKNOWN"
    mb_tree = parse_commit(repo.objects[mb][1])[0]
    head_tree = parse_commit(head_entry[1])[0]
    base_tree = parse_commit(base_entry[1])[0]
    _merged, conflict = three_way_merge(repo, mb_tree, head_tree, base_tree)
    return "CONFLICTING" if conflict else "MERGEABLE"

# ------------------------------------------------------------- HTTP layer

class _FastHeaders(dict):
    """Case-insensitive header mapping for the fast request parser.

    The stdlib parses request headers with the email parser (~0.2 ms
    per request); the well-formed requests the suite sends are plain
    "Name: value" lines, and this mapping stores them lower-cased.
    Only .get() is used by the handlers (Content-Length, Authorization,
    Transfer-Encoding, Connection, Expect); duplicate names keep the
    first value, as email.message.Message.get() does.
    """

    def get(self, key, default=None):
        return super().get(key.lower(), default)

    def __getitem__(self, key):
        return super().__getitem__(key.lower())

    def __contains__(self, key):
        return super().__contains__(key.lower())


# Per-second cache for the Date response header: format_datetime costs
# ~30 us per call and the value only changes once a second.
_DATE_CACHE = [0, ""]


# ---------------------------------------------------------------- raw socket
# transport (v3)
#
# The stdlib ThreadingHTTPServer costs a thread spawn (~0.5-1 ms) per
# connection and a socket.makefile pair per connection, and its
# BaseHTTPRequestHandler runs every request through handle_one_request's
# method chain. The suite's timed workloads are latency-bound on that
# plumbing, not on the application logic (measured: a read GET costs
# 0.024 ms of application time against a 0.96 ms client-observed
# round-trip; a clone fetch 0.07 ms against a ~5 ms round-trip share).
# So v3 serves on raw sockets: a pre-spawned worker pool (no spawn per
# connection), one buffered reader per connection (bytes.find for line
# ends, C speed), and a single sendall per response. The application
# logic (ForgeHandler's route/handle_git/handle_rest/...) is inherited
# unchanged, so the wire behaviour is byte-identical to v2.

class RawReader:
    """Buffered socket reader with the readline/read interface the
    handler's fast parser uses. One recv per request in the common
    (non-pipelined) case; leftover bytes stay buffered for keep-alive."""

    __slots__ = ("sock", "buf", "pos", "eof")

    def __init__(self, sock):
        self.sock = sock
        self.buf = b""
        self.pos = 0
        self.eof = False

    def _fill(self):
        if self.eof:
            return False
        try:
            data = self.sock.recv(65536)
        except OSError:
            self.eof = True
            return False
        if not data:
            self.eof = True
            return False
        if self.pos:
            self.buf = self.buf[self.pos:] + data
            self.pos = 0
        else:
            self.buf += data
        return True

    def readline(self, limit=-1):
        while True:
            idx = self.buf.find(b"\n", self.pos)
            if idx != -1:
                end = idx + 1
                if limit > 0 and end - self.pos > limit:
                    end = self.pos + limit
                line = self.buf[self.pos:end]
                self.pos = end
                if self.pos == len(self.buf):
                    self.buf = b""
                    self.pos = 0
                return line
            if limit > 0 and len(self.buf) - self.pos >= limit:
                line = self.buf[self.pos:self.pos + limit]
                self.pos += limit
                if self.pos == len(self.buf):
                    self.buf = b""
                    self.pos = 0
                return line
            if not self._fill():
                line = self.buf[self.pos:]
                self.buf = b""
                self.pos = 0
                return line

    def read(self, n=-1):
        if n is None or n < 0:
            out = bytearray(self.buf[self.pos:])
            self.buf = b""
            self.pos = 0
            while not self.eof:
                if not self._fill():
                    break
                out += self.buf
                self.buf = b""
                self.pos = 0
            return bytes(out)
        while len(self.buf) - self.pos < n:
            if not self._fill():
                break
        end = self.pos + n
        if end > len(self.buf):
            end = len(self.buf)
        data = self.buf[self.pos:end]
        self.pos = end
        if self.pos == len(self.buf):
            self.buf = b""
            self.pos = 0
        return data

    def close(self):
        pass


class RawWriter:
    """Unbuffered socket writer: one sendall per response."""

    __slots__ = ("sock",)

    def __init__(self, sock):
        self.sock = sock

    def write(self, data):
        self.sock.sendall(data)
        return len(data)

    def flush(self):
        pass

    def close(self):
        pass


class RawServer:
    """Accept loop; one daemon thread per connection (the stdlib's
    threading model, but without socket.makefile). A FIXED WORKER POOL
    DOES NOT WORK here: the suite's undici client pools keep-alive
    connections and never closes them, so a pool's workers all end up
    parked on idle connections and new connections queue (measured on
    the pool build: busy=64, qsize=19, clone 0 pts). A thread per
    connection is unbounded, and the spawn (~0.5 ms) is paid once per
    connection — the client reuses connections, so it is not on the
    per-request path."""

    def __init__(self, addr):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(addr)
        self.sock.listen(128)
        self.server_address = self.sock.getsockname()
        self._shutdown = threading.Event()

    def _serve_conn(self, conn):
        try:
            RawHandler(conn, ("127.0.0.1", 0), self)
        except Exception:
            pass
        finally:
            try:
                conn.close()
            except Exception:
                pass

    def serve_forever(self):
        while not self._shutdown.is_set():
            try:
                conn, _ = self.sock.accept()
            except OSError:
                break
            try:
                conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            except OSError:
                pass
            t = threading.Thread(target=self._serve_conn, args=(conn,),
                                 daemon=True)
            t.start()

    def shutdown(self):
        self._shutdown.set()
        try:
            self.sock.close()
        except Exception:
            pass

    def server_close(self):
        try:
            self.sock.close()
        except Exception:
            pass


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "github-core-clone/1.0.0"

    # -- plumbing ---------------------------------------------------------
    def log_message(self, fmt, *args):
        pass

    def setup(self):
        super().setup()
        # Nagle + delayed ACK costs ~40 ms per small response on
        # localhost; disable it so keep-alive request/response pairs
        # complete in well under a millisecond.
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP,
                                       socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def date_time_string(self, timestamp=None):
        # The Date header has one-second resolution; cache the formatted
        # value per second instead of re-running format_datetime per reply.
        if timestamp is None:
            now = int(time.time())
            if now != _DATE_CACHE[0]:
                _DATE_CACHE[0] = now
                _DATE_CACHE[1] = super().date_time_string(now)
            return _DATE_CACHE[1]
        return super().date_time_string(timestamp)

    def parse_request(self):
        """Fast path for a well-formed "METHOD SP path SP HTTP/1.x" line.

        BaseHTTPRequestHandler.parse_request spends ~0.2 ms per request
        in the email header parser; the suite's requests are plain
        "Name: value" headers, parsed here with str operations. Anything
        that is not exactly that shape falls back to the stdlib parser
        (headers untouched at decision time, so the fallback re-reads the
        same raw request line), and any odd header line falls back to
        http.client.parse_headers over the buffered raw lines, so error
        behaviour (400/431/505, Expect: 100-continue, Connection) is
        identical to the stdlib.
        """
        try:
            line = self.raw_requestline.decode("iso-8859-1").rstrip("\r\n")
        except Exception:
            return super().parse_request()
        words = line.split()
        if len(words) == 3:
            command, path, version = words
            if (command in ("GET", "POST", "PUT", "PATCH", "DELETE", "HEAD")
                    and version in ("HTTP/1.0", "HTTP/1.1")
                    and path.startswith("/")
                    and "://" not in path
                    and path.isascii()
                    and not any(ord(c) < 32 or ord(c) == 127 for c in path)):
                return self._parse_request_fast(line, command, path, version)
        return super().parse_request()

    def _parse_request_fast(self, line, command, path, version):
        self.command = command
        self.requestline = line
        self.request_version = version
        self.close_connection = (version == "HTTP/1.0")
        if path.startswith("//"):
            path = "/" + path.lstrip("/")
        self.path = path
        raw_lines = []
        try:
            while True:
                hline = self.rfile.readline(65537)
                if len(hline) > 65536:
                    raise http.client.LineTooLong("line too long")
                if hline in (b"\r\n", b"\n", b""):
                    break
                raw_lines.append(hline)
                if len(raw_lines) > 100:
                    raise http.client.HTTPException(
                        "got more than 100 headers")
        except http.client.LineTooLong as err:
            self.send_error(431, "Line too long", str(err))
            return False
        except http.client.HTTPException as err:
            self.send_error(431, "Too many headers", str(err))
            return False
        clean = True
        for hline in raw_lines:
            if hline[:1] in (b" ", b"\t") or b":" not in hline:
                clean = False
                break
            name = hline.split(b":", 1)[0]
            if not name or b" " in name or b"\t" in name:
                clean = False
                break
        if clean:
            headers = _FastHeaders()
            for hline in raw_lines:
                name, _, value = hline.partition(b":")
                headers.setdefault(
                    name.decode("iso-8859-1").strip().lower(),
                    value.decode("iso-8859-1").strip())
            self.headers = headers
        else:
            try:
                self.headers = http.client.parse_headers(
                    io.BytesIO(b"".join(raw_lines)),
                    _class=self.MessageClass)
            except http.client.LineTooLong as err:
                self.send_error(431, "Line too long", str(err))
                return False
            except http.client.HTTPException as err:
                self.send_error(431, "Too many headers", str(err))
                return False
        conntype = self.headers.get("Connection", "")
        if conntype.lower() == "close":
            self.close_connection = True
        elif (conntype.lower() == "keep-alive"
              and self.protocol_version >= "HTTP/1.1"):
            self.close_connection = False
        expect = self.headers.get("Expect", "")
        if (expect.lower() == "100-continue"
                and self.protocol_version >= "HTTP/1.1"
                and self.request_version >= "HTTP/1.1"):
            if not self.handle_expect_100():
                return False
        return True

    def read_body(self):
        length = self.headers.get("Content-Length")
        if length is not None:
            try:
                n = int(length)
            except ValueError:
                n = 0
            return self.rfile.read(n) if n > 0 else b""
        if self.headers.get("Transfer-Encoding", "").lower() == "chunked":
            out = bytearray()
            while True:
                line = self.rfile.readline(65536).strip()
                try:
                    n = int(line.split(b";")[0], 16)
                except ValueError:
                    break
                if n == 0:
                    self.rfile.readline(65536)
                    break
                out += self.rfile.read(n)
                self.rfile.readline(65536)
            return bytes(out)
        return b""

    def send_bytes(self, status, body, ctype="application/json",
                   extra_headers=None):
        if isinstance(body, str):
            body = body.encode()
        # HTTP/0.9: no status line or headers, body only (as the stdlib).
        if self.request_version == "HTTP/0.9":
            if body and self.command != "HEAD":
                self.wfile.write(body)
            return
        msg = _STATUS_MSG.get(status)
        if msg is None:
            # Unusual status: fall back to the stdlib path.
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            if extra_headers:
                for k, v in extra_headers:
                    self.send_header(k, v)
            self.end_headers()
            if body and self.command != "HEAD":
                self.wfile.write(body)
            return
        # One bytes object, one write: status line, Server, Date,
        # Content-Type, Content-Length, extra headers, blank line, body.
        # Same bytes the stdlib path produced, same order.
        out = bytearray()
        out += self.protocol_version.encode("latin-1")
        out += b" "
        out += str(status).encode("latin-1")
        out += b" "
        out += msg
        out += b"\r\n"
        out += _SERVER_HDR
        out += b"Date: "
        out += self.date_time_string().encode("latin-1")
        out += b"\r\nContent-Type: "
        out += ctype.encode("latin-1")
        out += b"\r\nContent-Length: "
        out += str(len(body)).encode("latin-1")
        out += b"\r\n"
        if extra_headers:
            for k, v in extra_headers:
                out += k.encode("latin-1")
                out += b": "
                out += v.encode("latin-1")
                out += b"\r\n"
        out += b"\r\n"
        if body and self.command != "HEAD":
            out += body
        self.wfile.write(bytes(out))

    def send_json(self, status, obj, extra_headers=None):
        headers = [("X-GitHub-Request-Id", STORE.next_req_id())]
        if extra_headers:
            headers.extend(extra_headers)
        self.send_bytes(status, json.dumps(obj), "application/json", headers)

    def send_json_bytes(self, status, body_bytes, extra_headers=None):
        """Send already-serialized JSON (skips json.dumps)."""
        headers = [("X-GitHub-Request-Id", STORE.next_req_id())]
        if extra_headers:
            headers.extend(extra_headers)
        self.send_bytes(status, body_bytes, "application/json", headers)

    def json_error(self, status, message):
        self.send_json(status, {"message": message})

    def parse_json_body(self, raw):
        """-> (obj, error_message). Empty body -> {}."""
        if not raw:
            return {}, None
        try:
            obj = json.loads(raw.decode("utf-8"))
        except Exception:
            return None, "Problems parsing JSON"
        if not isinstance(obj, dict):
            return None, "JSON body must be an object"
        return obj, None

    def bearer_ok(self):
        auth = self.headers.get("Authorization", "")
        if not auth.startswith("Bearer "):
            return False
        token = auth[7:].strip()
        if not token:
            return False
        expected = env_token()
        if expected:
            return token == expected
        return True

    # -- routing ----------------------------------------------------------
    def do_GET(self):
        self.route()

    def do_POST(self):
        self.route()

    def do_PUT(self):
        self.route()

    def do_PATCH(self):
        self.route()

    def do_DELETE(self):
        self.route()

    def do_HEAD(self):
        self.route()

    def route(self):
        try:
            # Fast path: origin-form paths need no urlparse; parse_qs only
            # when a query string is present. Anything else (absolute
            # form, fragment) takes the stdlib parse, as before.
            raw_path = self.path
            if (raw_path.startswith("/") and "://" not in raw_path
                    and "#" not in raw_path):
                if "?" in raw_path:
                    path, _, qs = raw_path.partition("?")
                    query = parse_qs(qs)
                else:
                    path, query = raw_path, {}
            else:
                parsed = urlparse(self.path)
                path = parsed.path
                query = parse_qs(parsed.query)
            body = self.read_body() if self.command in (
                "POST", "PUT", "PATCH", "DELETE") else b""
            if path == "/healthz":
                self.send_json(200, {"ok": True})
                return
            if path == "/api/graphql":
                if self.command != "POST":
                    self.json_error(405, "Method Not Allowed")
                    return
                self.handle_graphql(body)
                return
            if path == "/mcp":
                self.handle_mcp(body)
                return
            if path.startswith("/api/v3"):
                self.handle_rest(path, query, body)
                return
            m = re.match(r"^/([^/]+)/([^/]+)\.git/(.+)$", path)
            if m:
                owner, repo, sub = m.group(1), m.group(2), m.group(3)
                self.handle_git(owner, repo, sub, query, body)
                return
            self.json_error(404, "Not Found")
        except BrokenPipeError:
            pass
        except Exception as exc:  # never kill the server on a bad request
            try:
                self.json_error(500, "Internal Server Error: %s" % exc)
            except Exception:
                pass

    # -- git smart HTTP ---------------------------------------------------
    def handle_git(self, owner, repo_name, sub, query, body):
        repo = STORE.get_repo(owner, repo_name)
        if repo is None:
            self.json_error(404, "Not Found")
            return
        if sub == "info/refs":
            service = query.get("service", [None])[0]
            self.git_info_refs(repo, service)
            return
        if sub == "git-upload-pack":
            if self.command == "POST":
                self.git_upload_pack(repo, body)
            else:
                self.json_error(405, "Method Not Allowed")
            return
        if sub == "git-receive-pack":
            if self.command == "POST":
                self.git_receive_pack(repo, body)
            else:
                self.json_error(405, "Method Not Allowed")
            return
        self.json_error(404, "Not Found")

    def git_ref_lines(self, repo, caps, for_receive=False):
        """v0 advertisement ref lines (without the service preamble)."""
        out = bytearray()
        tip = repo.head_tip()
        first = True

        def line(oid, name):
            nonlocal first
            text = "%s %s" % (oid, name)
            if first:
                text += "\0" + caps
                first = False
            return pkt(text + "\n")

        if tip is None:
            out += line(ZERO_OID, "capabilities^{}")
            out += pkt_flush()
            return bytes(out)
        out += line(tip, "HEAD")
        for name in sorted(repo.refs):
            if name == "HEAD":
                continue
            oid = repo.refs[name]
            out += line(oid, name)
            entry = repo.objects.get(oid)
            if entry is not None and entry[0] == "tag":
                target, _t, _n, _g, _m = parse_tag(entry[1])
                peeled = peel_to_commit(repo, oid)
                if peeled:
                    out += line(peeled, name + "^{}")
        out += pkt_flush()
        return bytes(out)

    def git_info_refs(self, owner_repo, service):
        repo = owner_repo
        proto = self.headers.get("Git-Protocol", "")
        ctype_up = "application/x-git-upload-pack-advertisement"
        ctype_rc = "application/x-git-receive-pack-advertisement"
        if service == "git-upload-pack":
            if proto == "version=2":
                out = bytearray()
                out += pkt("# service=git-upload-pack\n")
                out += pkt_flush()
                out += pkt("version 2\n")
                out += pkt("ls-refs=unborn\n")
                out += pkt("fetch=shallow wait-for-done\n")
                out += pkt("object-format=sha1\n")
                out += pkt("agent=github-core-clone/1.0.0\n")
                out += pkt_flush()
                self.send_bytes(200, bytes(out), ctype_up)
                return
            caps = ("symref=HEAD:refs/heads/main side-band-64k thin-pack "
                    "ofs-delta multi_ack shallow")
            out = bytearray()
            out += pkt("# service=git-upload-pack\n")
            out += pkt_flush()
            out += self.git_ref_lines(repo, caps)
            self.send_bytes(200, bytes(out), ctype_up)
            return
        if service == "git-receive-pack":
            caps = ("report-status report-status-v2 side-band-64k "
                    "delete-refs ofs-delta "
                    "symref=HEAD:refs/heads/main")
            out = bytearray()
            out += pkt("# service=git-receive-pack\n")
            out += pkt_flush()
            out += self.git_ref_lines(repo, caps, for_receive=True)
            self.send_bytes(200, bytes(out), ctype_rc)
            return
        self.json_error(400, "Unknown service")

    def git_upload_pack(self, repo, body):
        ctype = "application/x-git-upload-pack-result"
        try:
            lines = parse_pkt_lines(body)
        except ValueError:
            self.send_bytes(400, b"bad pkt-line\n", "text/plain")
            return
        if not lines or lines[0][0] != "data":
            self.send_bytes(400, b"empty request\n", "text/plain")
            return
        first = lines[0][1].decode("utf-8", "surrogateescape")
        if first.startswith("command=ls-refs"):
            self.git_ls_refs(repo, lines, ctype)
            return
        if first.startswith("command=fetch"):
            self.git_fetch_v2(repo, lines, ctype)
            return
        if first.startswith("want "):
            self.git_fetch_v0(repo, lines, body, ctype)
            return
        self.send_bytes(400, b"unknown command\n", "text/plain")

    def git_ls_refs(self, repo, lines, ctype):
        peel = False
        symrefs = False
        unborn = False
        prefixes = []
        for kind, payload in lines[1:]:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape").rstrip("\n")
            if text == "peel":
                peel = True
            elif text == "symrefs":
                symrefs = True
            elif text == "unborn":
                unborn = True
            elif text.startswith("ref-prefix "):
                prefixes.append(text[len("ref-prefix "):])
        with STORE.lock:
            refs_snapshot = dict(repo.refs)
        out = bytearray()
        tip = refs_snapshot.get("refs/heads/main")
        # HEAD is only listed when no ref-prefix filter is given, or when
        # a prefix matches it; a refs/heads/ filter must not return HEAD.
        head_wanted = (not prefixes
                       or any("HEAD".startswith(p) for p in prefixes))
        if symrefs and head_wanted:
            if tip:
                out += pkt("%s HEAD symref-target:refs/heads/main\n" % tip)
            elif unborn:
                out += pkt("unborn HEAD symref-target:refs/heads/main\n")
        for name in sorted(refs_snapshot):
            if prefixes and not any(name.startswith(p) for p in prefixes):
                continue
            oid = refs_snapshot[name]
            text = "%s %s" % (oid, name)
            # Peel needs only this one object's type; the objects dict is
            # never copied (a clone repo holds 600 objects and this runs
            # once per clone). Objects are only ever added, so a direct
            # lookup is safe without the lock.
            if peel:
                entry = repo.objects.get(oid)
                if entry is not None and entry[0] == "tag":
                    peeled = peel_to_commit(repo, oid)
                    if peeled:
                        text += " peeled:%s" % peeled
            out += pkt(text + "\n")
        out += pkt_flush()
        self.send_bytes(200, bytes(out), ctype)

    def _fetch_wants(self, repo, lines):
        """Parse a v2 fetch request. -> (wants, haves, shallows, depth)."""
        wants, haves, shallows = [], [], []
        depth = None
        for kind, payload in lines[1:]:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape").rstrip("\n")
            if text.startswith("want "):
                wants.append(text[5:].strip())
            elif text.startswith("have "):
                haves.append(text[5:].strip())
            elif text.startswith("shallow "):
                shallows.append(text[8:].strip())
            elif text.startswith("deepen "):
                try:
                    depth = int(text[7:].strip())
                except ValueError:
                    depth = None
        return wants, haves, shallows, depth

    def git_fetch_v2(self, repo, lines, ctype):
        wants, haves, shallows, depth = self._fetch_wants(repo, lines)
        with STORE.lock:
            version = repo.version
        key = (repo.id, version, tuple(wants), tuple(haves),
               tuple(shallows), depth)
        cached = fetch_cache_get(key)
        if cached is None:
            with _FETCH_COMPUTE_LOCK:
                cached = fetch_cache_get(key)
                if cached is None:
                    wanted, shallow_lines, unshallow_lines = self._compute_fetch(
                        repo, wants, haves, shallows, depth, None)
                    out = bytearray()
                    out += pkt("acknowledgments\n")
                    out += pkt("NAK\n")
                    out += pkt_delim()
                    if shallow_lines or unshallow_lines:
                        out += pkt("shallow-info\n")
                        for oid in shallow_lines:
                            out += pkt("shallow %s\n" % oid)
                        for oid in unshallow_lines:
                            out += pkt("unshallow %s\n" % oid)
                        out += pkt_delim()
                    if wanted:
                        pack = write_pack([(repo.objects[o][0], repo.objects[o][1])
                                           for o in wanted])
                        out += pkt("packfile\n")
                        out += sideband_pack(pack)
                    out += pkt_flush()
                    cached = bytes(out)
                    fetch_cache_put(key, cached)
        self.send_bytes(200, cached, ctype)

    def _compute_fetch(self, repo, wants, haves, shallows, depth,
                       refs_snapshot):
        """-> (ordered wanted oids, shallow oids, unshallow oids)."""
        if not wants:
            return [], [], []
        have_reachable = collect_reachable(repo, haves)
        # A shallow commit in the request means the client holds the
        # commit and its tree/blobs but NOT its ancestors: subtract the
        # ancestors of every shallow boundary from what it is assumed to
        # hold, or a deepen fetch would deliver nothing.
        for s in shallows:
            entry = repo.objects.get(s)
            if entry is not None and entry[0] == "commit":
                _t, parents, _a, _c, _m = parse_commit(entry[1])
                have_reachable -= collect_reachable(repo, parents)
        wanted_set = set()
        shallow_out = []
        unshallow_out = []
        if depth is None:
            wanted_set = collect_reachable(repo, wants) - have_reachable
        else:
            # depth-limited reachable from wants: commits at generations
            # 0..depth-1 plus their trees/blobs. The shallow boundary is
            # the generation depth-1 commits themselves (their parents are
            # cut off), not the parents.
            gen0 = []
            for w in wants:
                entry = repo.objects.get(w)
                if entry is not None and entry[0] == "commit":
                    gen0.append(w)
                elif entry is not None and entry[0] == "tag":
                    c = peel_to_commit(repo, w)
                    if c:
                        gen0.append(c)
            depth_reachable = set()
            gen_of = {}
            queue = [(w, 0) for w in gen0]
            qi = 0
            seen_commits = set()
            while qi < len(queue):
                oid, gen = queue[qi]
                qi += 1
                if oid in seen_commits:
                    continue
                seen_commits.add(oid)
                gen_of[oid] = gen
                entry = repo.objects.get(oid)
                if entry is None or entry[0] != "commit":
                    continue
                tree, parents, _a, _c, _m = parse_commit(entry[1])
                if tree:
                    collect_tree(repo, tree, depth_reachable)
                depth_reachable.add(oid)
                if gen + 1 < depth:
                    for p in parents:
                        queue.append((p, gen + 1))
            # tags among wants: include the tag objects themselves
            for w in wants:
                entry = repo.objects.get(w)
                if entry is not None and entry[0] == "tag":
                    depth_reachable.add(w)
            wanted_set = depth_reachable - have_reachable
            # shallow boundary: deepest fetched commits that have parents
            boundary = set()
            for oid, gen in gen_of.items():
                if gen != depth - 1:
                    continue
                entry = repo.objects.get(oid)
                if entry is not None and entry[0] == "commit":
                    _t, parents, _a, _c, _m = parse_commit(entry[1])
                    if parents:
                        boundary.add(oid)
            shallow_out = sorted(boundary - have_reachable)
            # unshallow: old shallow boundaries now included as full commits
            for s in shallows:
                if s in seen_commits and s not in boundary:
                    unshallow_out.append(s)
            unshallow_out = sorted(set(unshallow_out))
        # deterministic order: BFS from wants, only through wanted
        # objects (never walk the full history just to order a shallow
        # fetch — that turns a depth-1 clone into an O(history) scan).
        ordered = []
        seen = set()
        queue = list(wants)
        qi = 0
        while qi < len(queue):
            oid = queue[qi]
            qi += 1
            if oid not in wanted_set or oid in seen:
                continue
            seen.add(oid)
            ordered.append(oid)
            entry = repo.objects.get(oid)
            if entry is None:
                continue
            if entry[0] == "commit":
                tree, parents, _a, _c, _m = parse_commit(entry[1])
                if tree:
                    queue.append(tree)
                queue.extend(parents)
            elif entry[0] == "tag":
                obj, _t, _n, _g, _m = parse_tag(entry[1])
                if obj:
                    queue.append(obj)
            elif entry[0] == "tree":
                for _mode, _name, child in parse_tree(entry[1]):
                    queue.append(child)
        for oid in sorted(wanted_set - seen):
            ordered.append(oid)
        return ordered, shallow_out, unshallow_out

    def git_fetch_v0(self, repo, lines, body, ctype):
        wants, haves = [], []
        shallows = []
        depth = None
        section = 0
        for kind, payload in lines:
            if kind == "flush":
                section += 1
                continue
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape").rstrip("\n")
            if section == 0:
                if text.startswith("want "):
                    wants.append(text.split()[1])
                elif text.startswith("shallow "):
                    shallows.append(text[8:].strip())
                elif text.startswith("deepen "):
                    try:
                        depth = int(text[7:].strip())
                    except ValueError:
                        depth = None
            else:
                if text.startswith("have "):
                    haves.append(text[5:].strip())
        with STORE.lock:
            refs_snapshot = dict(repo.refs)
        wanted, shallow_lines, _un = self._compute_fetch(
            repo, wants, haves, shallows, depth, refs_snapshot)
        out = bytearray()
        out += pkt("NAK\n")
        for oid in shallow_lines:
            out += pkt("shallow %s\n" % oid)
        if wanted:
            pack = write_pack([(repo.objects[o][0], repo.objects[o][1])
                               for o in wanted])
            out += sideband_pack(pack)
        out += pkt_flush()
        self.send_bytes(200, bytes(out), ctype)

    def git_receive_pack(self, repo, body):
        ctype = "application/x-git-receive-pack-result"
        try:
            pre, pack_bytes = split_pack_after_flush(body)
            cmd_lines = parse_pkt_lines(pre)
        except ValueError:
            self.send_bytes(400, b"bad pkt-line\n", "text/plain")
            return
        commands = []
        for kind, payload in cmd_lines:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape")
            # first line may carry "\0" + capabilities
            if "\0" in text:
                text = text.split("\0", 1)[0]
            text = text.rstrip("\n")
            parts = text.split(" ")
            if len(parts) >= 3:
                commands.append((parts[0], parts[1], parts[2]))
        unpack_ok = True
        unpack_err = ""
        new_objects = {}
        if pack_bytes:
            try:
                new_objects = read_pack(pack_bytes)
            except ValueError as exc:
                unpack_ok = False
                unpack_err = str(exc)
        results = []  # (ref, ok, reason)
        with STORE.lock:
            if unpack_ok and new_objects:
                repo.objects.update(new_objects)
            for old_oid, new_oid, ref in commands:
                if not unpack_ok:
                    results.append((ref, False, "unpack failed"))
                    continue
                current = repo.refs.get(ref)
                if new_oid == ZERO_OID:
                    # delete
                    if current is None:
                        results.append((ref, False, "non-fast-forward"))
                    elif old_oid != ZERO_OID and old_oid != current:
                        results.append((ref, False, "non-fast-forward"))
                    else:
                        del repo.refs[ref]
                        results.append((ref, True, ""))
                    continue
                if new_oid not in repo.objects:
                    results.append((ref, False, "object not found"))
                    continue
                if current is None:
                    if old_oid != ZERO_OID:
                        results.append((ref, False, "non-fast-forward"))
                        continue
                    repo.refs[ref] = new_oid
                    results.append((ref, True, ""))
                    continue
                if old_oid != current:
                    results.append((ref, False, "non-fast-forward"))
                    continue
                if new_oid == current:
                    results.append((ref, True, ""))
                    continue
                if is_ancestor(repo, current, new_oid):
                    repo.refs[ref] = new_oid
                    results.append((ref, True, ""))
                else:
                    results.append((ref, False, "non-fast-forward"))
            if unpack_ok and (new_objects or commands):
                repo.version += 1
        report = []
        if unpack_ok:
            report.append("unpack ok\n")
        else:
            report.append("unpack %s\n" % unpack_err)
        for ref, ok, reason in results:
            if ok:
                report.append("ok %s\n" % ref)
            else:
                report.append("ng %s %s\n" % (ref, reason))
        out = sideband_lines(report)
        out += pkt_flush()
        self.send_bytes(200, out, ctype)

    # -- REST v3 ----------------------------------------------------------
    def handle_rest(self, path, query, body):
        # Public: root + meta. Everything else needs a valid token.
        if path not in ("/api/v3/", "/api/v3/meta") and not self.bearer_ok():
            self.json_error(401, "Bad credentials")
            return
        rest = path[len("/api/v3"):]
        parts = [p for p in rest.split("/") if p != ""]
        method = self.command

        def q(name, default=None):
            vals = query.get(name)
            return vals[0] if vals else default

        # root / meta -----------------------------------------------------
        if not parts:
            self.send_json(200, {
                "current_user_url": "/api/v3/user",
                "repository_url": "/api/v3/repos/{owner}/{repo}",
                "user_url": "/api/v3/users/{user}",
            }, [("X-OAuth-Scopes", "repo, read:org")])
            return
        if parts == ["meta"]:
            if method != "GET":
                self.json_error(405, "Method Not Allowed")
                return
            self.send_json(200, {"installed_version": SERVER_VERSION})
            return
        if parts == ["user"]:
            if method != "GET":
                self.json_error(405, "Method Not Allowed")
                return
            self.send_json(200, {
                "login": VIEWER_LOGIN, "id": VIEWER_ID,
                "name": VIEWER_NAME, "email": VIEWER_EMAIL,
                "type": "User",
            })
            return
        if parts == ["user", "repos"]:
            if method == "POST":
                obj, err = self.parse_json_body(body)
                if err:
                    self.json_error(400, err)
                    return
                name = obj.get("name")
                if not name or not isinstance(name, str):
                    self.json_error(422, "name is required")
                    return
                with STORE.lock:
                    repo = STORE.create_repo(
                        name, obj.get("description", ""),
                        obj.get("private", False))
                if repo is None:
                    self.json_error(422, "Repository already exists")
                    return
                self.send_json(201, repo_json(repo))
                return
            if method == "GET":
                per_page = _int_or(q("per_page"), 30)
                page = _int_or(q("page"), 1)
                with STORE.lock:
                    mine = sorted(
                        (r for r in STORE.repos.values()
                         if r.owner == VIEWER_LOGIN),
                        key=lambda r: r.id)
                total = len(mine)
                start = (page - 1) * per_page
                items = mine[start:start + per_page]
                headers = []
                if start + per_page < total:
                    host = self.headers.get("Host", "127.0.0.1")
                    nxt = ("http://%s/api/v3/user/repos?per_page=%d&page=%d"
                           % (host, per_page, page + 1))
                    headers.append(("Link", '<%s>; rel="next"' % nxt))
                self.send_json(200, [repo_json(r) for r in items], headers)
                return
            self.json_error(405, "Method Not Allowed")
            return

        if len(parts) >= 2 and parts[0] == "repos":
            owner, name = parts[1], parts[2] if len(parts) > 2 else None
            if name is None:
                self.json_error(404, "Not Found")
                return
            repo = STORE.get_repo(owner, name)
            # repo object -------------------------------------------------
            if len(parts) == 3:
                if repo is None or repo.owner != VIEWER_LOGIN:
                    self.json_error(404, "Not Found")
                    return
                if method == "GET":
                    self.send_json(200, repo_json(repo))
                    return
                if method == "PATCH":
                    obj, err = self.parse_json_body(body)
                    if err:
                        self.json_error(400, err)
                        return
                    with STORE.lock:
                        if "description" in obj:
                            repo.description = obj["description"]
                        if "private" in obj:
                            repo.private = bool(obj["private"])
                    self.send_json(200, repo_json(repo))
                    return
                if method == "DELETE":
                    STORE.delete_repo(owner, name)
                    self.send_bytes(204, b"", "application/json",
                                    [("X-GitHub-Request-Id",
                                      STORE.next_req_id())])
                    return
                self.json_error(405, "Method Not Allowed")
                return
            sub = parts[3]
            if repo is None or repo.owner != VIEWER_LOGIN:
                self.json_error(404, "Not Found")
                return
            if sub == "branches":
                if method != "GET":
                    self.json_error(405, "Method Not Allowed")
                    return
                if len(parts) == 4:
                    with STORE.lock:
                        branches = sorted(
                            n for n in repo.refs
                            if n.startswith("refs/heads/"))
                    out = [{"name": b[len("refs/heads/"):],
                            "commit": {"sha": repo.refs[b]}}
                           for b in branches]
                    self.send_json(200, out)
                    return
                branch = "/".join(parts[4:])
                tip = repo.refs.get("refs/heads/" + branch)
                if tip is None:
                    self.json_error(404, "Not Found")
                    return
                self.send_json(200, {"name": branch,
                                     "commit": {"sha": tip}})
                return
            if sub == "git" and len(parts) >= 5 and parts[4] == "refs":
                if method == "POST" and len(parts) == 5:
                    obj, err = self.parse_json_body(body)
                    if err:
                        self.json_error(400, err)
                        return
                    ref = obj.get("ref")
                    sha = obj.get("sha")
                    if not ref or not sha:
                        self.json_error(422, "ref and sha are required")
                        return
                    with STORE.lock:
                        if ref in repo.refs:
                            self.json_error(422,
                                            "Reference already exists")
                            return
                        entry = repo.objects.get(sha)
                        if entry is None or entry[0] != "commit":
                            self.json_error(422, "sha is not a commit")
                            return
                        repo.refs[ref] = sha
                    self.send_json(201, {"ref": ref,
                                         "object": {"sha": sha,
                                                    "type": "commit"}})
                    return
                if method == "GET" and len(parts) >= 6:
                    ref = "/".join(parts[5:])
                    oid = repo.refs.get(ref)
                    if oid is None:
                        self.json_error(404, "Not Found")
                        return
                    self.send_json(200, {"ref": ref,
                                         "object": {"sha": oid,
                                                    "type": "commit"}})
                    return
                self.json_error(405, "Method Not Allowed")
                return
            if sub == "commits":
                if method != "GET":
                    self.json_error(405, "Method Not Allowed")
                    return
                commits = list_commits(repo, q("sha"))
                if commits is None:
                    self.json_error(404, "Not Found")
                    return
                self.send_json(200, commits)
                return
            if sub == "contents":
                if len(parts) < 5:
                    # root directory listing
                    if method != "GET":
                        self.json_error(405, "Method Not Allowed")
                        return
                    tip = resolve_ref(repo, q("ref"))
                    if tip is None:
                        self.json_error(404, "Not Found")
                        return
                    tree_oid = parse_commit(repo.objects[tip][1])[0]
                    out = []
                    for mode, name, child in parse_tree(
                            repo.objects[tree_oid][1]):
                        out.append({
                            "type": "dir" if mode == b"40000" else "file",
                            "name": name.decode("utf-8",
                                                "surrogateescape"),
                            "path": name.decode("utf-8",
                                                "surrogateescape"),
                            "sha": child,
                        })
                    out.sort(key=lambda e: e["name"])
                    self.send_json(200, out)
                    return
                cpath = "/".join(unquote(p) for p in parts[4:])
                if method == "GET":
                    tip = resolve_ref(repo, q("ref"))
                    if tip is None:
                        self.json_error(404, "Not Found")
                        return
                    tree_oid = parse_commit(repo.objects[tip][1])[0]
                    found = _tree_entry_at(repo, tree_oid, cpath)
                    if found is None:
                        self.json_error(404, "Not Found")
                        return
                    kind, oid, _mode = found
                    if kind == "file":
                        data = repo.objects[oid][1]
                        self.send_json(200, {
                            "type": "file", "encoding": "base64",
                            "content": base64.b64encode(data).decode(),
                            "sha": oid, "size": len(data),
                            "name": cpath.rsplit("/", 1)[-1], "path": cpath,
                        })
                        return
                    entries = []
                    for mode, name, child in parse_tree(
                            repo.objects[oid][1]):
                        entries.append({
                            "type": "dir" if mode == b"40000" else "file",
                            "name": name.decode("utf-8",
                                                "surrogateescape"),
                            "path": cpath + "/" + name.decode(
                                "utf-8", "surrogateescape"),
                            "sha": child,
                        })
                    entries.sort(key=lambda e: e["name"])
                    self.send_json(200, entries)
                    return
                obj, err = self.parse_json_body(body)
                if err:
                    self.json_error(400, err)
                    return
                if method == "PUT":
                    message = obj.get("message", "")
                    content = obj.get("content", "")
                    try:
                        raw = base64.b64decode(
                            "".join(content.split()))
                    except Exception:
                        self.json_error(400, "content is not valid base64")
                        return
                    result, err, status = write_contents_op(
                        repo, cpath, raw, message, obj.get("branch"),
                        obj.get("sha"))
                    if err:
                        self.json_error(status, err)
                        return
                    self.send_json(status, result)
                    return
                if method == "DELETE":
                    result, err, status = delete_contents_op(
                        repo, cpath, obj.get("message", ""),
                        obj.get("sha"))
                    if err:
                        self.json_error(status, err)
                        return
                    self.send_json(status, result)
                    return
                self.json_error(405, "Method Not Allowed")
                return
            if sub == "labels":
                if method != "POST":
                    self.json_error(405, "Method Not Allowed")
                    return
                obj, err = self.parse_json_body(body)
                if err:
                    self.json_error(400, err)
                    return
                name = obj.get("name")
                if not name:
                    self.json_error(422, "name is required")
                    return
                with STORE.lock:
                    color = obj.get("color", "000000")
                    if name in repo.labels:
                        color = repo.labels[name]
                    else:
                        repo.labels[name] = color
                self.send_json(201, {"name": name, "color": color})
                return
            if sub == "issues":
                if len(parts) == 4:
                    if method == "POST":
                        obj, err = self.parse_json_body(body)
                        if err:
                            self.json_error(400, err)
                            return
                        labels = obj.get("labels", [])
                        if isinstance(labels, list):
                            labels = [l.get("name") if isinstance(l, dict)
                                      else l for l in labels]
                        issue, err = create_issue_op(
                            repo, obj.get("title", ""), obj.get("body", ""),
                            labels)
                        if err:
                            self.json_error(422, err)
                            return
                        self.send_json(201, issue_json(issue))
                        return
                    if method == "GET":
                        state = q("state", "open")
                        direction = q("direction", "desc")
                        per_page = _int_or(q("per_page"), 30)
                        page = _int_or(q("page"), 1)
                        with STORE.lock:
                            issues = list(repo.issues.values())
                        if state in ("open", "closed"):
                            issues = [i for i in issues
                                      if i.state == state]
                        issues.sort(key=lambda i: i.created_seq,
                                    reverse=(direction != "asc"))
                        start = (page - 1) * per_page
                        page_items = issues[start:start + per_page]
                        self.send_json(200, [issue_json(i)
                                             for i in page_items])
                        return
                    self.json_error(405, "Method Not Allowed")
                    return
                try:
                    number = int(parts[4])
                except ValueError:
                    self.json_error(404, "Not Found")
                    return
                if len(parts) == 6 and parts[5] == "comments":
                    issue = repo.issues.get(number)
                    if issue is None:
                        self.json_error(404, "Not Found")
                        return
                    if method == "POST":
                        obj, err = self.parse_json_body(body)
                        if err:
                            self.json_error(400, err)
                            return
                        with STORE.lock:
                            cid = repo.next_comment_id
                            repo.next_comment_id += 1
                            issue.comments.append((cid, obj.get("body", "")))
                            issue._json = None
                        self.send_json(201, {
                            "id": cid, "body": obj.get("body", ""),
                            "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                            "created_at": FIXED_TS,
                            "updated_at": FIXED_TS,
                        })
                        return
                    if method == "GET":
                        self.send_json(200, [{
                            "id": cid, "body": b,
                            "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                            "created_at": FIXED_TS,
                        } for cid, b in issue.comments])
                        return
                    self.json_error(405, "Method Not Allowed")
                    return
                if len(parts) == 5:
                    issue = repo.issues.get(number)
                    if issue is None:
                        self.json_error(404, "Not Found")
                        return
                    if method == "GET":
                        self.send_json_bytes(200, issue_json_bytes(issue))
                        return
                    if method == "PATCH":
                        obj, err = self.parse_json_body(body)
                        if err:
                            self.json_error(400, err)
                            return
                        with STORE.lock:
                            if "state" in obj:
                                issue.state = obj["state"]
                            if "title" in obj:
                                issue.title = obj["title"]
                            if "body" in obj:
                                issue.body = obj["body"]
                            issue._json = None
                        self.send_json(200, issue_json(issue))
                        return
                    self.json_error(405, "Method Not Allowed")
                    return
                self.json_error(404, "Not Found")
                return
            if sub == "pulls":
                if len(parts) == 4:
                    if method == "POST":
                        obj, err = self.parse_json_body(body)
                        if err:
                            self.json_error(400, err)
                            return
                        pr, err, status = create_pr_op(
                            repo, obj.get("title", ""), obj.get("body", ""),
                            obj.get("head", ""), obj.get("base", ""))
                        if err:
                            self.json_error(status, err)
                            return
                        self.send_json(201, pr_json(pr))
                        return
                    if method == "GET":
                        state = q("state", "open")
                        with STORE.lock:
                            pulls = list(repo.pulls.values())
                        if state == "open":
                            pulls = [p for p in pulls if p.state == "open"]
                        elif state == "closed":
                            pulls = [p for p in pulls
                                     if p.state == "closed"]
                        pulls.sort(key=lambda p: p.created_seq)
                        self.send_json(200, [pr_json(p) for p in pulls])
                        return
                    self.json_error(405, "Method Not Allowed")
                    return
                try:
                    number = int(parts[4])
                except ValueError:
                    self.json_error(404, "Not Found")
                    return
                if len(parts) == 6 and parts[5] == "files":
                    pr = repo.pulls.get(number)
                    if pr is None:
                        self.json_error(404, "Not Found")
                        return
                    head_tip = repo.refs.get("refs/heads/" + pr.head)
                    base_tip = repo.refs.get("refs/heads/" + pr.base)
                    if head_tip is None or base_tip is None:
                        self.json_error(404, "Not Found")
                        return
                    mb = merge_base(repo, head_tip, base_tip)
                    mb_tree = (parse_commit(repo.objects[mb][1])[0]
                               if mb else None)
                    head_tree = parse_commit(repo.objects[head_tip][1])[0]
                    self.send_json(200, diff_files(repo, mb_tree, head_tree))
                    return
                if len(parts) == 6 and parts[5] == "merge":
                    if method != "PUT":
                        self.json_error(405, "Method Not Allowed")
                        return
                    obj, _err = self.parse_json_body(body)
                    method_name = (obj or {}).get("merge_method", "squash")
                    sha, err, status = merge_pr_op(repo, number, method_name)
                    if err:
                        self.json_error(status, err)
                        return
                    pr = repo.pulls[number]
                    self.send_json(200, {
                        "merged": True, "sha": sha,
                        "message": pr.title,
                    })
                    return
                if len(parts) == 5:
                    pr = repo.pulls.get(number)
                    if pr is None:
                        self.json_error(404, "Not Found")
                        return
                    if method == "GET":
                        self.send_json(200, pr_json(pr))
                        return
                    self.json_error(405, "Method Not Allowed")
                    return
                self.json_error(404, "Not Found")
                return
        self.json_error(404, "Not Found")



# -- GraphQL ----------------------------------------------------------
    def handle_graphql(self, body):
        if not self.bearer_ok():
            self.json_error(401, "Bad credentials")
            return
        try:
            payload = json.loads(body.decode("utf-8"))
        except Exception:
            self.send_json(400, {"errors": [{"message": "Invalid JSON"}]})
            return
        if isinstance(payload, list):
            results = [self.execute_graphql(op) for op in payload]
            self.send_json(200, results)
            return
        if isinstance(payload, dict):
            self.send_json(200, self.execute_graphql(payload))
            return
        self.send_json(400, {"errors": [{"message": "Invalid request"}]})

    def execute_graphql(self, op):
        if not isinstance(op, dict):
            return {"data": None,
                    "errors": [{"message": "Invalid operation"}]}
        query = op.get("query", "")
        variables = op.get("variables") or {}
        operation_name = op.get("operationName")
        try:
            doc = gql_parse(query)
        except ValueError as exc:
            return {"data": None, "errors": [{"message": str(exc)}]}
        fragments = {}
        operations = []
        for definition in doc:
            if definition["kind"] == "fragment":
                fragments[definition["name"]] = definition
            else:
                operations.append(definition)
        chosen = None
        if operation_name:
            for o in operations:
                if o.get("name") == operation_name:
                    chosen = o
                    break
        if chosen is None:
            chosen = operations[0] if operations else None
        if chosen is None:
            return {"data": None,
                    "errors": [{"message": "No operation provided"}]}
        errors = []
        root_type = "Query" if chosen["operation"] == "query" else "Mutation"
        root = {"__typename": root_type}
        data = gql_resolve(root, root_type, chosen["selections"],
                           variables, fragments, errors,
                           chosen.get("variable_definitions", {}))
        out = {"data": data}
        if errors:
            out["errors"] = errors
        return out

# -- MCP --------------------------------------------------------------
    def handle_mcp(self, body):
        if self.command == "DELETE":
            self.send_bytes(204, b"", "application/json",
                            [("X-GitHub-Request-Id", STORE.next_req_id())])
            return
        if self.command != "POST":
            self.json_error(405, "Method Not Allowed")
            return
        if not self.bearer_ok():
            self.send_json(401, {
                "jsonrpc": "2.0", "id": None,
                "error": {"code": -32001, "message": "Unauthorized"},
            })
            return
        try:
            req = json.loads(body.decode("utf-8"))
        except Exception:
            self.send_json(400, {
                "jsonrpc": "2.0", "id": None,
                "error": {"code": -32700, "message": "Parse error"},
            })
            return
        if not isinstance(req, dict) or "method" not in req:
            self.send_json(400, {
                "jsonrpc": "2.0", "id": req.get("id") if isinstance(req, dict) else None,
                "error": {"code": -32600, "message": "Invalid Request"},
            })
            return
        req_id = req.get("id")
        method = req.get("method")
        params = req.get("params") or {}
        # notifications have no id: answer 202 with an empty body
        if req_id is None:
            self.send_bytes(202, b"", "application/json")
            return

        def result(payload):
            self.send_json(200, {"jsonrpc": "2.0", "id": req_id,
                                 "result": payload})

        def rpc_error(code, message):
            self.send_json(200, {"jsonrpc": "2.0", "id": req_id,
                                 "error": {"code": code,
                                           "message": message}})

        server_info = {"name": SERVER_NAME, "version": SERVER_VERSION}
        if method == "server/discover":
            result({
                "supportedVersions": ["2026-07-28"],
                "capabilities": {"tools": {}},
                "serverInfo": server_info,
                "instructions": "GitHub-compatible forge tools.",
                "_meta": {"io.modelcontextprotocol/serverInfo":
                          server_info},
            })
            return
        if method == "initialize":
            offered = None
            if isinstance(params, dict):
                offered = params.get("protocolVersion")
            result({
                "protocolVersion": offered or "2025-11-25",
                "capabilities": {"tools": {}},
                "serverInfo": server_info,
            })
            return
        if method == "ping":
            result({})
            return
        if method == "tools/list":
            result({"tools": MCP_TOOLS})
            return
        if method == "tools/call":
            name = params.get("name", "")
            arguments = params.get("arguments") or {}
            tool = MCP_TOOL_MAP.get(name)
            if tool is None:
                rpc_error(-32602, "Unknown tool: %s" % name)
                return
            missing = [p for p in tool["inputSchema"].get("required", [])
                       if p not in arguments or arguments[p] is None]
            if missing:
                result({
                    "content": [{"type": "text",
                                 "text": "Missing required argument(s): "
                                         + ", ".join(missing)}],
                    "isError": True,
                })
                return
            payload, is_error = mcp_call_tool(name, arguments)
            result({
                "content": [{"type": "text",
                             "text": json.dumps(payload)}],
                "structuredContent": payload,
                "isError": bool(is_error),
            })
            return
        rpc_error(-32601, "Method not found: %s" % method)

class RawHandler(ForgeHandler):
    """ForgeHandler's application logic on a raw socket. Inherits every
    handler method (route, handle_git, handle_rest, handle_graphql,
    handle_mcp, send_bytes, parse_request, read_body); only the
    transport setup is replaced — no makefile, no per-connection
    thread spawn (the pool owns the threads)."""

    def __init__(self, conn, client_address, server):
        self.connection = conn
        self.client_address = client_address
        self.server = server
        self.setup()
        try:
            self.handle()
        finally:
            self.finish()

    def setup(self):
        self.rfile = RawReader(self.connection)
        self.wfile = RawWriter(self.connection)
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP,
                                       socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def handle(self):
        # Tight keep-alive loop: bypasses
        # BaseHTTPRequestHandler.handle_one_request (method lookup,
        # hasattr/getattr dispatch, per-request flush) and dispatches
        # straight to the do_* handler. parse_request sets
        # close_connection from the HTTP version / Connection header,
        # so the loop ends exactly when the stdlib's would.
        self.close_connection = True
        while True:
            line = self.rfile.readline(65537)
            if not line:
                return
            if len(line) > 65536:
                self.send_error(414, "Request-URI Too Long")
                return
            self.raw_requestline = line
            if not self.parse_request():
                return
            cmd = self.command
            if cmd == "GET":
                self.do_GET()
            elif cmd == "POST":
                self.do_POST()
            elif cmd == "PUT":
                self.do_PUT()
            elif cmd == "PATCH":
                self.do_PATCH()
            elif cmd == "DELETE":
                self.do_DELETE()
            elif cmd == "HEAD":
                self.do_HEAD()
            else:
                self.send_error(501, "Unsupported method (%r)" % cmd)
                return
            if self.close_connection:
                return

    def finish(self):
        pass


def _tree_entry_at(repo, tree_oid, path):
    """Walk a tree by path. -> (kind, oid, mode) where kind is 'file',
    'dir' or None if the path does not exist."""
    parts = [p for p in path.split("/") if p != ""]
    cur = tree_oid
    for i, part in enumerate(parts):
        entry = repo.objects.get(cur)
        if entry is None or entry[0] != "tree":
            return None
        found = None
        for mode, name, child in parse_tree(entry[1]):
            if name.decode("utf-8", "surrogateescape") == part:
                found = (mode, child)
                break
        if found is None:
            return None
        mode, child = found
        if i == len(parts) - 1:
            return ("dir" if mode == b"40000" else "file", child, mode)
        if mode != b"40000":
            return None
        cur = child
    return ("dir", cur, b"40000")


def _int_or(value, default):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


# ------------------------------------------------------- GraphQL parsing

def gql_tokenize(text):
    tokens = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n,":
            i += 1
            continue
        if c == "#":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == ".":
            if text[i:i + 3] == "...":
                tokens.append(("...", "..."))
                i += 3
                continue
            raise ValueError("Unexpected character '.'")
        if c in "!$():=@[]{}|&":
            tokens.append((c, c))
            i += 1
            continue
        if c == '"':
            if text[i:i + 3] == '"""':
                j = text.find('"""', i + 3)
                if j < 0:
                    raise ValueError("Unterminated block string")
                tokens.append(("string", text[i + 3:j]))
                i = j + 3
                continue
            j = i + 1
            buf = []
            while j < n and text[j] != '"':
                if text[j] == "\\":
                    esc = text[j + 1] if j + 1 < n else ""
                    mapping = {"n": "\n", "t": "\t", "r": "\r",
                               "b": "\b", "f": "\f", '"': '"',
                               "\\": "\\", "/": "/"}
                    if esc == "u":
                        buf.append(chr(int(text[j + 2:j + 6], 16)))
                        j += 6
                        continue
                    buf.append(mapping.get(esc, esc))
                    j += 2
                    continue
                buf.append(text[j])
                j += 1
            if j >= n:
                raise ValueError("Unterminated string")
            tokens.append(("string", "".join(buf)))
            i = j + 1
            continue
        if c.isdigit() or (c == "-" and i + 1 < n and text[i + 1].isdigit()):
            j = i
            if text[j] == "-":
                j += 1
            while j < n and (text[j].isdigit() or text[j] in ".eE+-"):
                j += 1
            raw = text[i:j]
            if any(ch in raw for ch in ".eE"):
                tokens.append(("float", float(raw)))
            else:
                tokens.append(("int", int(raw)))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            tokens.append(("name", text[i:j]))
            i = j
            continue
        raise ValueError("Unexpected character %r" % c)
    tokens.append(("eof", None))
    return tokens


class _GqlParser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect(self, kind):
        tok = self.next()
        if tok[0] != kind:
            raise ValueError("Expected %s, got %r" % (kind, tok[0]))
        return tok[1]

    def expect_name(self, value=None):
        tok = self.next()
        if tok[0] != "name":
            raise ValueError("Expected name, got %r" % (tok[0],))
        if value is not None and tok[1] != value:
            raise ValueError("Expected %s, got %s" % (value, tok[1]))
        return tok[1]

    def parse_document(self):
        defs = []
        while self.peek()[0] != "eof":
            defs.append(self.parse_definition())
        return defs

    def parse_definition(self):
        tok = self.peek()
        if tok[0] == "{":
            return {"kind": "operation", "operation": "query",
                    "name": None, "variable_definitions": {},
                    "selections": self.parse_selection_set()}
        if tok[0] == "name" and tok[1] in ("query", "mutation",
                                           "subscription"):
            op = self.next()[1]
            name = None
            if self.peek()[0] == "name":
                name = self.next()[1]
            var_defs = {}
            if self.peek()[0] == "(":
                var_defs = self.parse_variable_definitions()
            # skip directives
            while self.peek()[0] == "@":
                self.parse_directive()
            return {"kind": "operation", "operation": op, "name": name,
                    "variable_definitions": var_defs,
                    "selections": self.parse_selection_set()}
        if tok[0] == "name" and tok[1] == "fragment":
            self.next()
            name = self.expect_name()
            self.expect_name("on")
            type_cond = self.expect_name()
            while self.peek()[0] == "@":
                self.parse_directive()
            return {"kind": "fragment", "name": name,
                    "type_condition": type_cond,
                    "selections": self.parse_selection_set()}
        raise ValueError("Unexpected token %r" % (tok,))

    def parse_directive(self):
        self.expect("@")
        self.expect_name()
        if self.peek()[0] == "(":
            self.parse_arguments()

    def parse_variable_definitions(self):
        self.expect("(")
        defs = {}
        while self.peek()[0] != ")":
            self.expect("$")
            name = self.expect_name()
            self.expect(":")
            vtype = self.parse_type()
            default = None
            if self.peek()[0] == "=":
                self.next()
                default = self.parse_value(is_const=True)
            defs[name] = {"type": vtype, "default": default}
        self.expect(")")
        return defs

    def parse_type(self):
        tok = self.peek()
        if tok[0] == "[":
            self.next()
            inner = self.parse_type()
            self.expect("]")
            t = "[" + inner + "]"
        elif tok[0] == "name":
            t = self.next()[1]
        else:
            raise ValueError("Expected type, got %r" % (tok,))
        if self.peek()[0] == "!":
            self.next()
            t += "!"
        return t

    def parse_selection_set(self):
        self.expect("{")
        sels = []
        while self.peek()[0] != "}":
            sels.append(self.parse_selection())
        self.expect("}")
        return sels

    def parse_selection(self):
        tok = self.peek()
        if tok[0] == "...":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_cond = self.expect_name()
                while self.peek()[0] == "@":
                    self.parse_directive()
                return {"kind": "inline_fragment",
                        "type_condition": type_cond,
                        "selections": self.parse_selection_set()}
            if self.peek()[0] == "name":
                name = self.next()[1]
                while self.peek()[0] == "@":
                    self.parse_directive()
                return {"kind": "fragment_spread", "name": name}
            while self.peek()[0] == "@":
                self.parse_directive()
            return {"kind": "inline_fragment", "type_condition": None,
                    "selections": self.parse_selection_set()}
        name = self.expect_name()
        alias = None
        if self.peek()[0] == ":":
            self.next()
            alias = name
            name = self.expect_name()
        args = {}
        if self.peek()[0] == "(":
            args = self.parse_arguments()
        while self.peek()[0] == "@":
            self.parse_directive()
        selections = None
        if self.peek()[0] == "{":
            selections = self.parse_selection_set()
        return {"kind": "field", "name": name, "alias": alias,
                "arguments": args, "selections": selections}

    def parse_arguments(self):
        self.expect("(")
        args = {}
        while self.peek()[0] != ")":
            name = self.expect_name()
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self, is_const=False):
        tok = self.peek()
        if tok[0] == "$":
            self.next()
            return {"__var__": self.expect_name()}
        if tok[0] == "int" or tok[0] == "float":
            return self.next()[1]
        if tok[0] == "string":
            return self.next()[1]
        if tok[0] == "name":
            word = self.next()[1]
            if word == "true":
                return True
            if word == "false":
                return False
            if word == "null":
                return None
            return {"__enum__": word}
        if tok[0] == "[":
            self.next()
            vals = []
            while self.peek()[0] != "]":
                vals.append(self.parse_value(is_const))
            self.expect("]")
            return vals
        if tok[0] == "{":
            self.next()
            obj = {}
            while self.peek()[0] != "}":
                name = self.expect_name()
                self.expect(":")
                obj[name] = self.parse_value(is_const)
            self.expect("}")
            return obj
        raise ValueError("Unexpected value token %r" % (tok,))


def gql_parse(text):
    return _GqlParser(gql_tokenize(text)).parse_document()


def gql_resolve_value(value, variables):
    """Resolve variables/enums in a parsed argument value."""
    if isinstance(value, dict):
        if "__var__" in value:
            return variables.get(value["__var__"])
        if "__enum__" in value:
            return value["__enum__"]
        return {k: gql_resolve_value(v, variables)
                for k, v in value.items()}
    if isinstance(value, list):
        return [gql_resolve_value(v, variables) for v in value]
    return value


# ---------------------------------------------------- GraphQL execution

GQL_FIELDS = {
    "Query": {"viewer", "repository", "node", "__type", "__schema"},
    "Mutation": {"createIssue", "closeIssue", "createPullRequest",
                 "mergePullRequest", "addComment"},
    "Repository": {"id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission",
                   "hasIssuesEnabled", "description", "isPrivate",
                   "private", "createdAt", "updatedAt", "url", "issue",
                   "issues", "pullRequests", "pullRequest"},
    "Issue": {"id", "number", "title", "body", "state", "createdAt",
              "updatedAt", "author", "labels", "comments", "url"},
    "PullRequest": {"id", "number", "title", "body", "state", "merged",
                    "headRefName", "baseRefName", "headRefOid",
                    "baseRefOid", "mergeable", "files", "author",
                    "createdAt", "updatedAt"},
    "User": {"login", "id", "name"},
    "IssueConnection": {"nodes", "edges", "pageInfo", "totalCount"},
    "PullRequestConnection": {"nodes", "edges", "pageInfo", "totalCount"},
    "IssueEdge": {"node", "cursor"},
    "PullRequestEdge": {"node", "cursor"},
    "PageInfo": {"hasNextPage", "hasPreviousPage", "startCursor",
                 "endCursor"},
    "PullRequestChangedFile": {"path", "additions", "deletions",
                               "changes"},
    "PullRequestChangedFileConnection": {"nodes", "edges", "pageInfo",
                                        "totalCount"},
    "PullRequestChangedFileEdge": {"node", "cursor"},
    "IssueComment": {"id", "body", "author", "createdAt", "updatedAt"},
    "IssueCommentConnection": {"nodes", "edges", "pageInfo",
                               "totalCount"},
    "IssueCommentEdge": {"node", "cursor"},
    "Label": {"id", "name", "color"},
    "LabelConnection": {"nodes", "edges", "pageInfo", "totalCount"},
    "LabelEdge": {"node", "cursor"},
    "Ref": {"name", "target"},
    "__Type": {"name", "kind", "fields", "enumValues", "description"},
    "__Field": {"name", "description", "args", "type"},
    "__EnumValue": {"name", "description"},
    "CreateIssuePayload": {"issue", "clientMutationId"},
    "CloseIssuePayload": {"issue", "clientMutationId"},
    "CreatePullRequestPayload": {"pullRequest", "clientMutationId"},
    "MergePullRequestPayload": {"pullRequest", "clientMutationId"},
    "AddCommentPayload": {"commentEdge", "comment", "clientMutationId"},
    "Commit": {"oid", "message"},
}

GQL_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body", "createdAt",
              "updatedAt", "author", "labels", "comments", "url"],
    "PullRequest": ["id", "number", "title", "body", "state", "merged",
                    "headRefName", "baseRefName", "headRefOid",
                    "baseRefOid", "mergeable", "files", "author",
                    "createdAt", "updatedAt"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission",
                   "hasIssuesEnabled", "description", "isPrivate",
                   "createdAt", "updatedAt", "url", "issue", "issues",
                   "pullRequests", "pullRequest"],
    "User": ["login", "id", "name"],
    "Commit": ["oid", "message"],
    "IssueComment": ["id", "body", "author", "createdAt", "updatedAt"],
    "Label": ["id", "name", "color"],
    "Ref": ["name", "target"],
}

GQL_ENUM_VALUES = {
    "SearchType": ["COMMIT", "DISCUSSION", "ISSUE", "PACKAGE",
                   "PULL_REQUEST", "REPOSITORY", "TOPIC", "USER"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "MergeMethod": ["MERGE", "SQUASH", "REBASE"],
    "OrderDirection": ["ASC", "DESC"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
}


def _page(items, first, after):
    """Cursor pagination over a list. -> (page_items, page_info, offset)."""
    offset = cursor_decode(after) if after else 0
    if first is None:
        first = len(items)
    page_items = items[offset:offset + first]
    end = offset + len(page_items)
    page_info = {
        "__typename": "PageInfo",
        "hasNextPage": end < len(items),
        "hasPreviousPage": offset > 0,
        "startCursor": cursor_encode(offset) if page_items else None,
        "endCursor": cursor_encode(end) if page_items else None,
    }
    return page_items, page_info, offset


def _connection(items, first, after, item_type, edge_type, conn_type):
    page_items, page_info, offset = _page(items, first, after)
    return {
        "__typename": conn_type,
        "nodes": page_items,
        "edges": [{"__typename": edge_type, "node": it,
                   "cursor": cursor_encode(offset + i)}
                  for i, it in enumerate(page_items)],
        "pageInfo": page_info,
        "totalCount": len(items),
        "_node_type": item_type,
    }


def gql_issue_obj(repo, issue):
    return {"__typename": "Issue", "_repo": repo, "_issue": issue,
            "id": gid("Issue", repo.id, issue.number),
            "number": issue.number, "title": issue.title,
            "body": issue.body, "state": graphql_state(issue),
            "createdAt": FIXED_TS, "updatedAt": FIXED_TS,
            "url": "https://example.invalid/%s/issues/%d"
                   % (repo.full_name(), issue.number)}


def gql_pr_obj(repo, pr):
    return {"__typename": "PullRequest", "_repo": repo, "_pr": pr,
            "id": gid("PullRequest", repo.id, pr.number),
            "number": pr.number, "title": pr.title, "body": pr.body,
            "state": graphql_pr_state(pr), "merged": pr.merged,
            "headRefName": pr.head, "baseRefName": pr.base,
            "headRefOid": pr.head_sha, "baseRefOid": pr.base_sha,
            "createdAt": FIXED_TS, "updatedAt": FIXED_TS}


def gql_repo_obj(repo):
    return {"__typename": "Repository", "_repo": repo,
            "id": gid("Repository", repo.id), "databaseId": repo.id,
            "name": repo.name, "nameWithOwner": repo.full_name(),
            "viewerPermission": "ADMIN", "hasIssuesEnabled": True,
            "description": repo.description, "isPrivate": repo.private,
            "private": repo.private, "createdAt": FIXED_TS,
            "updatedAt": FIXED_TS,
            "url": "https://example.invalid/%s" % repo.full_name()}


def gql_user_obj(login):
    return {"__typename": "User", "login": login,
            "id": gid("User", VIEWER_ID), "name": VIEWER_NAME}


def gql_field(obj, type_name, field, args, errors):
    """-> (value, child_type_name_or_None)."""
    if type_name == "Query":
        if field == "viewer":
            return gql_user_obj(VIEWER_LOGIN), "User"
        if field == "repository":
            repo = STORE.get_repo(args.get("owner", ""),
                                  args.get("name", ""))
            if repo is None or repo.owner != VIEWER_LOGIN:
                return None, "Repository"
            return gql_repo_obj(repo), "Repository"
        if field == "node":
            decoded = ungid(args.get("id"))
            if decoded is None:
                return None, None
            kind, parts = decoded
            if kind == "Repository" and len(parts) == 1:
                repo = STORE.repos_by_id.get(int(parts[0]))
                if repo is None:
                    return None, None
                return gql_repo_obj(repo), "Repository"
            if kind == "Issue" and len(parts) == 2:
                repo = STORE.repos_by_id.get(int(parts[0]))
                issue = repo.issues.get(int(parts[1])) if repo else None
                if issue is None:
                    return None, None
                return gql_issue_obj(repo, issue), "Issue"
            if kind == "PullRequest" and len(parts) == 2:
                repo = STORE.repos_by_id.get(int(parts[0]))
                pr = repo.pulls.get(int(parts[1])) if repo else None
                if pr is None:
                    return None, None
                return gql_pr_obj(repo, pr), "PullRequest"
            return None, None
        if field == "__type":
            name = args.get("name")
            if name in GQL_TYPE_FIELDS:
                return {"__typename": "__Type", "name": name,
                        "kind": "OBJECT", "_type": name}, "__Type"
            if name in GQL_ENUM_VALUES:
                return {"__typename": "__Type", "name": name,
                        "kind": "ENUM", "_type": name}, "__Type"
            return None, "__Type"
        if field == "__schema":
            return {"__typename": "__Schema"}, "__Schema"
        return None, None
    if type_name == "Mutation":
        return gql_mutation(obj, field, args, errors)
    if type_name == "Repository":
        repo = obj["_repo"]
        if field == "owner":
            return gql_user_obj(repo.owner), "User"
        if field == "defaultBranchRef":
            tip = repo.head_tip()
            if tip is None:
                return None, "Ref"
            return {"__typename": "Ref", "name": repo.default_branch,
                    "target": {"__typename": "Commit", "oid": tip,
                               "message": ""}}, "Ref"
        if field == "issue":
            issue = repo.issues.get(args.get("number"))
            if issue is None:
                return None, "Issue"
            return gql_issue_obj(repo, issue), "Issue"
        if field == "issues":
            with STORE.lock:
                issues = list(repo.issues.values())
            states = args.get("states")
            if states:
                wanted = {"closed" if s == "CLOSED" else "open"
                          for s in states}
                issues = [i for i in issues if i.state in wanted]
            order_by = args.get("orderBy") or {}
            direction = order_by.get("direction", "ASC")
            issues.sort(key=lambda i: i.created_seq,
                        reverse=(direction == "DESC"))
            return _connection(
                [gql_issue_obj(repo, i) for i in issues],
                args.get("first"), args.get("after"),
                "Issue", "IssueEdge", "IssueConnection"), "IssueConnection"
        if field == "pullRequests":
            with STORE.lock:
                pulls = list(repo.pulls.values())
            states = args.get("states")
            if states:
                pulls = [p for p in pulls
                         if graphql_pr_state(p) in states]
            pulls.sort(key=lambda p: p.created_seq)
            return _connection(
                [gql_pr_obj(repo, p) for p in pulls],
                args.get("first"), args.get("after"),
                "PullRequest", "PullRequestEdge",
                "PullRequestConnection"), "PullRequestConnection"
        if field == "pullRequest":
            pr = repo.pulls.get(args.get("number"))
            if pr is None:
                return None, "PullRequest"
            return gql_pr_obj(repo, pr), "PullRequest"
        return obj.get(field), None
    if type_name == "Issue":
        repo = obj["_repo"]
        issue = obj["_issue"]
        if field == "author":
            return gql_user_obj(VIEWER_LOGIN), "User"
        if field == "labels":
            nodes = [{"__typename": "Label",
                      "id": gid("Label", repo.id, n), "name": n,
                      "color": repo.labels.get(n, "000000")}
                     for n in issue.labels]
            return _connection(nodes, args.get("first"),
                               args.get("after"), "Label", "LabelEdge",
                               "LabelConnection"), "LabelConnection"
        if field == "comments":
            nodes = [{"__typename": "IssueComment",
                      "id": gid("IssueComment", repo.id, issue.number, cid),
                      "body": body, "createdAt": FIXED_TS,
                      "updatedAt": FIXED_TS}
                     for cid, body in issue.comments]
            return _connection(nodes, args.get("first"),
                               args.get("after"), "IssueComment",
                               "IssueCommentEdge",
                               "IssueCommentConnection"), \
                "IssueCommentConnection"
        return obj.get(field), None
    if type_name == "PullRequest":
        repo = obj["_repo"]
        pr = obj["_pr"]
        if field == "mergeable":
            return pr_mergeable(repo, pr), None
        if field == "author":
            return gql_user_obj(VIEWER_LOGIN), "User"
        if field == "files":
            head_tip = repo.refs.get("refs/heads/" + pr.head)
            base_tip = repo.refs.get("refs/heads/" + pr.base)
            if head_tip is None or base_tip is None:
                files = []
            else:
                mb = merge_base(repo, head_tip, base_tip)
                mb_tree = (parse_commit(repo.objects[mb][1])[0]
                           if mb else None)
                head_tree = parse_commit(repo.objects[head_tip][1])[0]
                files = [{"__typename": "PullRequestChangedFile",
                          "path": d["filename"],
                          "additions": d["additions"],
                          "deletions": d["deletions"],
                          "changes": d["changes"]}
                         for d in diff_files(repo, mb_tree, head_tree)]
            return _connection(files, args.get("first"),
                               args.get("after"),
                               "PullRequestChangedFile",
                               "PullRequestChangedFileEdge",
                               "PullRequestChangedFileConnection"), \
                "PullRequestChangedFileConnection"
        return obj.get(field), None
    if type_name == "__Type":
        name = obj.get("_type")
        if field == "fields":
            names = GQL_TYPE_FIELDS.get(name, [])
            return [{"__typename": "__Field", "name": n,
                     "description": None, "args": [], "type": None}
                    for n in names], "__Field"
        if field == "enumValues":
            values = GQL_ENUM_VALUES.get(name, [])
            return [{"__typename": "__EnumValue", "name": v,
                     "description": None} for v in values], "__EnumValue"
        return obj.get(field), None
    if type_name in ("IssueConnection", "PullRequestConnection",
                     "LabelConnection", "IssueCommentConnection",
                     "PullRequestChangedFileConnection"):
        if field == "nodes":
            return obj.get("nodes", []), obj.get("_node_type")
        if field == "edges":
            node_type = obj.get("_node_type", "")
            return obj.get("edges", []), node_type + "Edge"
        if field == "pageInfo":
            return obj.get("pageInfo"), "PageInfo"
        return obj.get(field), None
    if type_name.endswith("Edge"):
        if field == "node":
            node = obj.get("node")
            if isinstance(node, dict):
                return node, node.get("__typename")
            return node, None
        return obj.get(field), None
    value = obj.get(field)
    if isinstance(value, dict) and "__typename" in value:
        return value, value["__typename"]
    return value, None


def gql_mutation(obj, field, args, errors):
    """Mutations return (payload_dict, payload_type)."""
    inp = args.get("input") or {}
    if field == "createIssue":
        decoded = ungid(inp.get("repositoryId"))
        if decoded is None or decoded[0] != "Repository":
            errors.append({"message": "repositoryId is invalid"})
            return None, "CreateIssuePayload"
        repo = STORE.repos_by_id.get(int(decoded[1][0]))
        if repo is None:
            errors.append({"message": "Repository not found"})
            return None, "CreateIssuePayload"
        issue, err = create_issue_op(repo, inp.get("title", ""),
                                     inp.get("body", ""), [])
        if err:
            errors.append({"message": err})
            return None, "CreateIssuePayload"
        return {"__typename": "CreateIssuePayload",
                "issue": gql_issue_obj(repo, issue),
                "clientMutationId": inp.get("clientMutationId")}, \
            "CreateIssuePayload"
    if field == "closeIssue":
        decoded = ungid(inp.get("issueId"))
        if decoded is None or decoded[0] != "Issue":
            errors.append({"message": "issueId is invalid"})
            return None, "CloseIssuePayload"
        repo = STORE.repos_by_id.get(int(decoded[1][0]))
        issue = (repo.issues.get(int(decoded[1][1]))
                 if repo else None)
        if issue is None:
            errors.append({"message": "Issue not found"})
            return None, "CloseIssuePayload"
        close_issue_op(repo, issue.number)
        return {"__typename": "CloseIssuePayload",
                "issue": gql_issue_obj(repo, issue),
                "clientMutationId": inp.get("clientMutationId")}, \
            "CloseIssuePayload"
    if field == "createPullRequest":
        decoded = ungid(inp.get("repositoryId"))
        if decoded is None or decoded[0] != "Repository":
            errors.append({"message": "repositoryId is invalid"})
            return None, "CreatePullRequestPayload"
        repo = STORE.repos_by_id.get(int(decoded[1][0]))
        if repo is None:
            errors.append({"message": "Repository not found"})
            return None, "CreatePullRequestPayload"
        pr, err, _status = create_pr_op(
            repo, inp.get("title", ""), inp.get("body", ""),
            inp.get("headRefName", ""), inp.get("baseRefName", ""))
        if err:
            errors.append({"message": err})
            return None, "CreatePullRequestPayload"
        return {"__typename": "CreatePullRequestPayload",
                "pullRequest": gql_pr_obj(repo, pr),
                "clientMutationId": inp.get("clientMutationId")}, \
            "CreatePullRequestPayload"
    if field == "mergePullRequest":
        decoded = ungid(inp.get("pullRequestId"))
        if decoded is None or decoded[0] != "PullRequest":
            errors.append({"message": "pullRequestId is invalid"})
            return None, "MergePullRequestPayload"
        repo = STORE.repos_by_id.get(int(decoded[1][0]))
        pr = repo.pulls.get(int(decoded[1][1])) if repo else None
        if pr is None:
            errors.append({"message": "Pull request not found"})
            return None, "MergePullRequestPayload"
        _sha, err, _status = merge_pr_op(repo, pr.number, "squash")
        if err:
            errors.append({"message": err})
            return None, "MergePullRequestPayload"
        return {"__typename": "MergePullRequestPayload",
                "pullRequest": gql_pr_obj(repo, pr),
                "clientMutationId": inp.get("clientMutationId")}, \
            "MergePullRequestPayload"
    if field == "addComment":
        decoded = ungid(inp.get("subjectId"))
        if decoded is None or decoded[0] != "Issue":
            errors.append({"message": "subjectId is invalid"})
            return None, "AddCommentPayload"
        repo = STORE.repos_by_id.get(int(decoded[1][0]))
        issue = (repo.issues.get(int(decoded[1][1]))
                 if repo else None)
        if issue is None:
            errors.append({"message": "Issue not found"})
            return None, "AddCommentPayload"
        with STORE.lock:
            cid = repo.next_comment_id
            repo.next_comment_id += 1
            issue.comments.append((cid, inp.get("body", "")))
            issue._json = None
        node = {"__typename": "IssueComment",
                "id": gid("IssueComment", repo.id, issue.number, cid),
                "body": inp.get("body", ""), "createdAt": FIXED_TS,
                "updatedAt": FIXED_TS}
        return {"__typename": "AddCommentPayload",
                "commentEdge": {"__typename": "IssueCommentEdge",
                                "node": node,
                                "cursor": cursor_encode(0)},
                "comment": node,
                "clientMutationId": inp.get("clientMutationId")}, \
            "AddCommentPayload"
    errors.append({"message": "Unknown mutation '%s'" % field})
    return None, None


def gql_resolve(obj, type_name, selections, variables, fragments, errors,
                var_defs=None):
    """Resolve a selection set against an object dict. Returns a plain
    dict (no internal keys)."""
    result = {}
    if var_defs:
        for name, spec in var_defs.items():
            if name not in variables and spec.get("default") is not None:
                variables = dict(variables)
                variables[name] = gql_resolve_value(spec["default"],
                                                    variables)
    for sel in selections:
        kind = sel["kind"]
        if kind == "fragment_spread":
            frag = fragments.get(sel["name"])
            if frag is None:
                errors.append({"message": "Unknown fragment '%s'"
                                          % sel["name"]})
                continue
            sub = gql_resolve(obj, type_name, frag["selections"],
                              variables, fragments, errors)
            result.update(sub)
            continue
        if kind == "inline_fragment":
            cond = sel.get("type_condition")
            if cond is None or cond == type_name:
                sub = gql_resolve(obj, type_name, sel["selections"],
                                  variables, fragments, errors)
                result.update(sub)
            continue
        fname = sel["name"]
        key = sel.get("alias") or fname
        if fname == "__typename":
            result[key] = type_name
            continue
        if fname not in GQL_FIELDS.get(type_name, set()):
            errors.append({"message": "Field '%s' doesn't exist on type "
                                      "'%s'" % (fname, type_name)})
            continue
        args = {k: gql_resolve_value(v, variables)
                for k, v in (sel.get("arguments") or {}).items()}
        value, child_type = gql_field(obj, type_name, fname, args, errors)
        if value is None:
            result[key] = None
            continue
        sub_sels = sel.get("selections")
        if sub_sels and isinstance(value, dict):
            result[key] = gql_resolve(value, child_type, sub_sels,
                                      variables, fragments, errors)
        elif sub_sels and isinstance(value, list):
            result[key] = [
                gql_resolve(v, child_type, sub_sels, variables,
                            fragments, errors)
                if isinstance(v, dict) else v
                for v in value]
        else:
            if isinstance(value, dict):
                value = {k: v for k, v in value.items()
                         if not k.startswith("_")}
            result[key] = value
    return result


MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository owned by the viewer.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string",
                         "description": "Repository name"},
                "description": {"type": "string",
                                "description": "Repository description"},
                "private": {"type": "boolean",
                            "description": "Whether the repository is "
                                         "private"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "title": {"type": "string", "description": "Issue title"},
                "body": {"type": "string", "description": "Issue body"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List issues in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "state": {"type": "string",
                          "description": "Issue state: open, closed, all"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Create a pull request in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "title": {"type": "string",
                          "description": "Pull request title"},
                "head": {"type": "string",
                         "description": "Head branch name"},
                "base": {"type": "string",
                         "description": "Base branch name"},
                "body": {"type": "string",
                         "description": "Pull request body"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "pull_number": {"type": "integer",
                                "description": "Pull request number"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]

MCP_TOOL_MAP = {t["name"]: t for t in MCP_TOOLS}


def mcp_call_tool(name, arguments):
    """-> (payload, is_error). Payload is JSON-serialisable."""
    if name == "create_repo":
        with STORE.lock:
            repo = STORE.create_repo(
                arguments["name"], arguments.get("description", ""),
                arguments.get("private", False))
        if repo is None:
            return {"error": "Repository already exists"}, True
        return repo_json(repo), False
    owner = arguments.get("owner", "")
    repo_name = arguments.get("repo", "")
    repo = STORE.get_repo(owner, repo_name)
    if repo is None or repo.owner != VIEWER_LOGIN:
        return {"error": "Not Found"}, True
    if name == "get_repo":
        return repo_json(repo), False
    if name == "create_issue":
        issue, err = create_issue_op(
            repo, arguments.get("title", ""), arguments.get("body", ""), [])
        if err:
            return {"error": err}, True
        return issue_json(issue), False
    if name == "list_issues":
        state = arguments.get("state", "open")
        with STORE.lock:
            issues = list(repo.issues.values())
        if state in ("open", "closed"):
            issues = [i for i in issues if i.state == state]
        issues.sort(key=lambda i: i.created_seq)
        return [issue_json(i) for i in issues], False
    if name == "create_pull_request":
        pr, err, _status = create_pr_op(
            repo, arguments.get("title", ""), arguments.get("body", ""),
            arguments.get("head", ""), arguments.get("base", ""))
        if err:
            return {"error": err}, True
        return pr_json(pr), False
    if name == "merge_pull_request":
        try:
            number = int(arguments.get("pull_number"))
        except (TypeError, ValueError):
            return {"error": "pull_number must be an integer"}, True
        sha, err, _status = merge_pr_op(repo, number, "squash")
        if err:
            return {"error": err}, True
        pr = repo.pulls[number]
        out = pr_json(pr)
        out["sha"] = sha
        return out, False
    return {"error": "Unknown tool: %s" % name}, True


# -------------------------------------------------------------- lifecycle

def http_post_json(url, payload, timeout=10):
    data = json.dumps(payload).encode()
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("Content-Type", "application/json")
    req.add_header("Content-Length", str(len(data)))
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read()
    except Exception as exc:
        return 0, str(exc).encode()


def http_get_json(url, timeout=10):
    req = urllib.request.Request(url, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read()
    except Exception as exc:
        return 0, str(exc).encode()


def run_lifecycle(server):
    """Register with the suite env, serve until it reports done."""
    if not ENV_URL:
        return
    env_base = ENV_URL.rstrip("/")
    port = server.server_address[1]
    deadline = time.time() + 20
    while time.time() < deadline:
        status, _body = http_post_json(env_base + "/register",
                                       {"port": port}, timeout=5)
        if status == 200:
            break
        if status == 409:
            # another entry won; keep waiting for done
            time.sleep(0.5)
            continue
        time.sleep(0.25)
    # poll /done with backoff (250ms -> 2000ms), 30s per poll
    interval = 0.25
    while True:
        status, body = http_get_json(env_base + "/done", timeout=30)
        if status == 200:
            try:
                if json.loads(body.decode("utf-8")).get("done"):
                    return
            except Exception:
                pass
        time.sleep(interval)
        interval = min(interval * 2, 2.0)


def main():
    server = RawServer(("0.0.0.0", FORGE_PORT))
    port = server.server_address[1]
    if ENV_URL:
        thread = threading.Thread(target=server.serve_forever,
                                  daemon=True)
        thread.start()
        try:
            run_lifecycle(server)
        finally:
            server.shutdown()
            server.server_close()
    else:
        sys.stderr.write("github-core-clone listening on %d\n" % port)
        sys.stderr.flush()
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        finally:
            server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
