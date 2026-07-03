<h1 align="center">Astrolabe</h1>

<p align="center">
  A web app for reading, visualizing, and interacting with content-addressed
  mathematical knowledge networks.
</p>

<p align="center">
  <a href="https://arxiv.org/abs/2604.10435"><img alt="Paper" src="https://img.shields.io/badge/paper-arXiv%3A2604.10435-b31b1b" /></a>
  <a href="LICENSE"><img alt="License: AGPL-3.0" src="https://img.shields.io/badge/license-AGPL--3.0-blue" /></a>
</p>

---

## What is this?

The canonical Astrolabe frontend: a Next.js app (React frontend + Node `/api`
Route Handlers, no separate backend) that serves the knowledge networks under
`../projects/`. Each project is a content-addressed store of mathematical
statements, formal Lean declarations, and typed relations between them.

- **ReadView** — render `.astrolabe/docs/*.mdx` with LaTeX, entry blocks, and cross-references
- **NetworkView** — visualize the entry graph with d3-force simulation
- **DetailView** — inspect entries with structured record rendering
- **Plugin system** — extensible analysis and visualization (see `src/plugins/leannets/`)

## The store

One `.md` file per node (YAML front-matter + body), named by its hash.
Conceptually each entry is:

```json
{ "<12-char-hash>": { "ref": ["<hash>", ...], "record": { ... } } }
```

- **ref** — an ordered list of hashes. `|ref| - 1` is the width of the entry:
  width 0 (`ref = [self_hash]`) is an atom, width 1 (`ref = [A, B]`) a binary
  relation, width k a higher-dimensional relation.
- **record** — structured content (`sort`, `source`, `title`, statement text,
  Lean source, …), interpreted by plugins.
- **hash** — content-address over the canonical record (JSON with sorted keys,
  `", "` / `": "` separators):
  - atom: `SHA256("__self__" ‖ 0x00 ‖ canon(record))[:12 hex]`
  - edge: `SHA256(ref₁ ‖ 0x00 ‖ … ‖ refₖ ‖ 0x00 ‖ canon(record))[:12 hex]`

Two layouts: a self-contained project keeps `.astrolabe/{atoms,edges}` of its
own; a hypergraph-sharing project reads the shared pool
`<projectsRoot>/hypergraph/{atoms,edges}` unioned with its optional
`.astrolabe/hypergraph/*` layer (project layer wins). Read path:
`src/lib/server/store.ts`; write path: `src/lib/server/storeOps.ts`. The full
model is documented in `CLAUDE.md` and `content/data-model.mdx`.

Docs use `\entryref{hash}` and `\entryblock{hash}` macros in `.mdx` files to
cross-reference and inline entries; `$...$` LaTeX is rendered via KaTeX.

## Develop

```bash
npm install
npm run dev        # http://localhost:3000

npx vitest run     # tests
npx tsc --noEmit   # typecheck
```

## License

[AGPL-3.0](LICENSE)
