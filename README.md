# makefun-github-forge-v3

A standalone GitHub-compatible git forge in a single Python file
(`main.py`, standard library only — no git binary, no packages, no
outside service). One process serves four surfaces from its own
in-memory store:

- **git smart HTTP** — protocol v2 `upload-pack` (ls-refs, fetch,
  shallow/deepen) and v0 `receive-pack` (report-status, side-band-64k,
  fast-forward rules, mixed push reports), with a from-scratch pack
  reader/writer (plain, OFS_DELTA, REF_DELTA) and sideband framing.
- **REST v3 API** (`/api/v3`) — repositories, branches, refs, commits,
  contents, labels, issues (+ comments) and pull requests (create,
  files, squash merge with three-way conflict detection).
- **GraphQL v4** (`/api/graphql`) — hand-written parser + executor for
  the repository / issue / pull-request queries and mutations `gh` and
  `github-mcp-server` send, including introspection (`__type`),
  cursor pagination, global ids and batched operations.
- **MCP** (`/mcp`) — modern `server/discover` era (2026-07-28) with an
  `initialize` fallback; six tools: `create_repo`, `get_repo`,
  `create_issue`, `list_issues`, `create_pull_request`,
  `merge_pull_request`.

## Running

```sh
python3 main.py
```

Without `MAKEFUN_ENV_URL` it serves forever on `FORGE_PORT` (default:
an ephemeral port, printed to stderr). With `MAKEFUN_ENV_URL` set it
binds an ephemeral port, registers it with the suite environment, and
exits when the environment reports done. Authentication is
`Authorization: Bearer $MAKEFUN_SHOP_TOKEN`; when that variable is
unset any non-empty bearer token is accepted (local development).

The authenticated viewer is `adaiversen`. All timestamps are fixed
(`2025-01-01T00:00:00Z`) and ids are assigned in creation order, so
two runs on the same instance leave the same state export.

## Local conformance

```sh
MAKEFUN_SHOP_TOKEN=test-token FORGE_PORT=18080 python3 main.py &
node --experimental-strip-types <kit>/sdk/run.ts \
  --url http://127.0.0.1:18080 --token test-token --perf
```

Built for the make.fun `github-core-clone-01` bounty.

## v2 performance work (on top of the v1 optimized entry, score 961)

- **Single-write responses** — `send_bytes` builds one bytes object
  (status line, Server, Date, Content-Type, Content-Length, extra
  headers, body) and writes once, instead of the stdlib's
  send_response / send_header / end_headers / write sequence. `wfile`
  is unbuffered, so every `write()` is a syscall; this removes one
  syscall and several method calls per response.
- **Cached issue JSON** — the read workload GETs the same issue 2,000
  times; the serialized bytes are cached on the `Issue` and
  invalidated on any mutation (PATCH, comment add, close).
- **ls-refs no longer copies the objects dict** — it only snapshots
  `refs` (1–2 entries) and looks up peel targets on demand; a clone
  repo holds 600 objects and this ran once per clone.

Measured server CPU per request (load-independent, `/proc` utime):
read 0.165 → 0.118 ms (−28%), write 0.25 → 0.20 ms (−20%).

## v3 — raw-socket transport

Same application logic and API behaviour as v2. The server layer is
rebuilt on raw sockets: one daemon thread per connection (the stdlib
threading model, but without `socket.makefile`), a buffered byte reader
(`RawReader`), an unbuffered single-`sendall` writer (`RawWriter`), and
a tight keep-alive request loop in `RawHandler` that dispatches straight
to the `do_*` handlers. A fixed worker pool was tried first and removed:
the suite's undici client pools keep-alive connections and never closes
them, so a pool's workers all park on idle connections and new
connections queue (measured busy=64, qsize=19, clone 0 pts).
