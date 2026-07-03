# Astrolabe — Knowledge Network Visualizer

Next.js app (frontend + `/api` Route Handlers, all Node — there is no separate
backend and no Python anywhere in the stack).

## Sync with the Astrolabe (Tauri) repo

This `web/` is the **canonical, actively-developed** Astrolabe frontend.
`MathNetwork/Astrolabe` (the Tauri desktop app) is kept in sync **from here**, one
way, by the `.github/workflows/sync-astrolabe-ui.yml` workflow: every push to
`main` touching `web/src/**` mirrors the shared **UI core** into that repo and
opens a `sync/openga-ui` PR for review.

- **Synced (UI core):** the whole of `src/panels/`, `src/plugins/`,
  `src/components/mdx/`, `src/stores/`, plus the individual files
  `components/MarkdownRenderer.tsx`, `components/ParticleBackground.tsx`,
  `components/ProjectStatus.tsx`, `lib/entryColor.ts`, `lib/refView.ts`,
  `lib/sortColors.ts`.
- **NOT synced (per-app):** the data/API layer (`lib/apiBase.ts`, `lib/server/`,
  `app/api/`, `hooks/`), the site shell (`app/page.tsx`, `app/layout.tsx`,
  `Navbar`, `ThemeToggle`, `app/docs/`, `components/docs/`, `components/site/`),
  and `content/` / `projects/` (data).

So: edit shared UI under the synced paths and it flows to the Tauri build; keep
app-specific behaviour behind the `apiBase` seam in the non-synced paths. The
sync needs the `ASTROLABE_SYNC_TOKEN` repo secret (Contents + Pull-requests
write on `MathNetwork/Astrolabe`).

## How AI Should Work With the Store

**Edit files directly.** Modify the per-node `.md` files (one file per node,
named by its hash) and the `.mdx` docs, the same way a human would. The app
re-reads the store on each request. For anything beyond a trivial edit, script
against `web/src/lib/server/storeOps.ts` — it computes hashes, writes/deletes
node files, and repoints every reference (other nodes' `ref`, inline hashes in
records, and the docs) when a hash changes.

**The web API is read-only.** The `/api` routes only read the store; all writes
go through `storeOps` or direct file edits.

**Validate after editing:** `cd web && npx vitest run`.

---

## Store Layouts

`lib/server/store.ts` (`loadStore`) supports two layouts:

- **Legacy, self-contained**: `.astrolabe/{atoms,edges}` inside the project
  (`projects/riemannian-geometry`). Having its own `atoms/` marks a project as
  private — it reads nothing else.
- **Hypergraph-sharing**: a project without its own `atoms/` reads the union of
  the shared pool `<projectsRoot>/hypergraph/{atoms,edges}` (sibling of the
  project folder) and its optional project layer
  `.astrolabe/hypergraph/{atoms,edges}`. Content-addressing makes the union
  conflict-free (same hash ⇒ same bytes); on overlap the project layer wins.

## Core Data Model

Each node is one `.md` file: YAML front-matter + body. Conceptually each entry is
```json
{ "<12-char-hash>": { "ref": ["<hash>", ...], "record": { ... } } }
```

Two record formats on disk:

- **Nested (current, hypergraph pool)**: front-matter is `{ ref, record: {...} }`
  with everything — including the prose, as `record.content` — inside `record`.
- **Flat (legacy, riemannian-geometry)**: record fields sit at front-matter top
  level next to `ref`, prose in the file body (surfaced as `notes` by the reader).

### Hash Computation

Implemented in `lib/server/storeOps.ts`; `canon(record)` is JSON with sorted
keys, `", "` / `": "` separators, non-ASCII left as-is.

- **Atom** (`ref = [own hash]`): `SHA256("__self__" ‖ 0x00 ‖ canon(record))[:12 hex]`
  — the self-hash cannot include itself, so a fixed placeholder stands in.
- **Edge**: `SHA256(ref₁ ‖ 0x00 ‖ … ‖ refₖ ‖ 0x00 ‖ canon(record))[:12 hex]`.

The function is fixed; what varies between eras is *which record* was hashed:

- **Legacy riemannian atoms** are pinned to an identity subset — tex atoms hash
  over `{source, src, dcref}`, lean atoms over `{source, name}` — so text/state
  edits keep the hash (the stored record is larger than the hashed one).
- **Hypergraph-pool cards** are purely content-addressed: the full record is
  hashed, any change produces a new hash, and `storeOps.updateContent` repoints
  every reference. Provenance lives in a `from` pointer inside the record
  (`{ref: <bib-atom hash>, at: "0.2"}` — source work + statement number there).
- **Edges** hash the full record in both eras.

### Well-Formedness — ALL FIVE MUST HOLD
1. **Atom self-reference**: if `len(ref) == 1`, then `ref[0] == own hash`
2. **Identity uniqueness**: distinct entries have distinct hashes
3. **Referential closure**: every hash in `ref` must exist in the store
4. **Non-empty ref**: `len(ref) >= 1`
5. **Distinct refs**: if `len(ref) > 1`, no duplicate hashes in `ref`

### Degree and Stage
- `degree = len(ref) - 1` — atom is degree 0, edge is degree 1
- Stage: atoms = stage 0; entry whose all refs have stage ≤ m gets stage m+1
- Cyclic entries get stage -1

---

## Record Convention

| Field | Values |
|-------|--------|
| `source` | `tex`, `lean`, `bib` |
| `sort` | `definition`, `theorem`, `lemma`, `proposition`, `corollary`, `proof`, `ref`, … (atoms); legacy edges store a pair label like `(lean, tex)` |
| `from` | `{ref, at}` provenance pointer to a bib atom (hypergraph cards) |
| `title` | display name (no hardcoded numbers) |
| `content` / `notes` | statement text with LaTeX + `\entryref{hash}`, or Lean source |
| `state` | `proven` or `sorry` (lean only) |
| `rel` | edge relation: `uses`, `references`, `formalizes`, `corollary-of`, … |

Source works are bib atoms (`source: bib`); `\cite` becomes an inline
`\entryref`, cross-references stay edges.

## MDX Convention

Docs live in `.astrolabe/docs/*.mdx` and compose cards by hash:

- `\entryblock{hash}` — block display with auto-numbering (`{collapsible}` variant)
- `\entryref{hash}{text}` — manual inline link; `\entryref{hash}` — auto "Sort N.M"

Numbering is **derived, never stored** (`components/mdx/numbering.ts`): chapter
from the doc's `# Chapter N` title (else filename prefix), section = ordinal of
the `## ` heading, item counter per section, first occurrence of a hash wins.
Proofs are not numbered. Never hardcode numbers.

---

## Architecture

- **Frontend**: Next.js + React + d3-force (deployed on Vercel)
- **API**: Next.js Route Handlers in `src/app/api/*` (Node, read-only) —
  `astrolabe/{entries,mtime,ref-graph}`, `docs/{list,read}`, `file`,
  `plugins/leannets/graph`, `project/{files,file-content}`
- **Store mechanics**: `lib/server/store.ts` (read) + `lib/server/storeOps.ts`
  (write) — byte-compatible with the original Python implementation (now living
  in MathNetwork/Astrolabe's backend), hash-for-hash

## Rules

- Web dev: `npm run dev` (no backend to start)
- Tests: `cd web && npx vitest run`
- Communicate with user in Chinese
