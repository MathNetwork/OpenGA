# Astrolabe — Knowledge Network Visualizer

## Sync with the Astrolabe (Tauri) repo

This `web/` is the **canonical, actively-developed** Astrolabe frontend.
`MathNetwork/Astrolabe` (the Tauri desktop app) is kept in sync **from here**, one
way, by the `.github/workflows/sync-astrolabe-ui.yml` workflow: every push to
`main` touching `web/src/**` mirrors the shared **UI core** into that repo and
opens a `sync/openga-ui` PR for review.

- **Synced (UI core):** `src/panels/`, `src/plugins/`, `src/components/mdx/`,
  `src/stores/`, `src/components/MarkdownRenderer.tsx`,
  `src/components/ParticleBackground.tsx`, `src/lib/refView.ts`,
  `src/lib/sortColors.ts`.
- **NOT synced (per-app):** the data/API layer (`lib/api.ts`, `lib/apiBase.ts`,
  `lib/server/`, `app/api/`, `hooks/`), the site shell (`app/page.tsx`,
  `app/layout.tsx`, `Navbar`, `ThemeToggle`, `app/docs/`, `components/docs/`),
  and `content/` / `projects/` (data).

So: edit shared UI under the synced paths and it flows to the Tauri build; keep
app-specific behaviour behind the `apiBase` seam in the non-synced paths. The
sync needs the `ASTROLABE_SYNC_TOKEN` repo secret (Contents + Pull-requests
write on `MathNetwork/Astrolabe`).

## How AI Should Work With Astrolabe

**Edit files directly.** Modify the per-node `.md` files in `.astrolabe/atoms/` and `.astrolabe/edges/`, and the `.mdx` files in `.astrolabe/docs/`, the same way a human would. The app re-reads the store on each request.

**The web API is read-only.** The Next.js `/api` routes only read the store; writes happen by editing files (the CLI tools use `tools/astrolabe_store.py`).

**Validate after editing.** `python3 -c "import sys; sys.path.insert(0,'tools'); from astrolabe_store import AstrolabeStorage, validate_store; validate_store(AstrolabeStorage('<project-dir>').all_entries())"`

---

## Core Data Model (Paper §2)

The store is a content-addressable set of entries — one `.md` file per node
(`.astrolabe/atoms/<hash>.md`, `.astrolabe/edges/<hash>.md`: YAML front-matter +
body). Conceptually each entry is:
```json
{
  "<12-char-hash>": { "ref": ["<hash>", ...], "record": "<JSON string>" }
}
```

### Hash Computation
`SHA256(ref₁ || 0x00 || ref₂ || 0x00 || ... || record)[:12 hex]`

### Well-Formedness (Definition 2.2) — ALL FIVE MUST HOLD
1. **Atom self-reference**: if `len(ref) == 1`, then `ref[0] == own hash`
2. **Identity uniqueness**: distinct entries have distinct hashes
3. **Referential closure**: every hash in `ref` must exist in the store
4. **Non-empty ref**: `len(ref) >= 1`
5. **Distinct refs**: if `len(ref) > 1`, no duplicate hashes in `ref`

### Degree and Stage
- `degree = len(ref) - 1` — atom is degree 0, edge is degree 1
- Stage: atoms = stage 0; entry whose all refs have stage ≤ m gets stage m+1
- Cyclic entries get stage -1

### Hash Propagation
Modify record → hash changes → all entries referencing old hash (in ref or record text) are recursively updated and re-hashed.

---

## LeanNets Record Convention (Paper §4)

Record is a **JSON string**. Fields:

| Field | Required | Values |
|-------|----------|--------|
| `sort` | yes | `definition`, `theorem`, `lemma`, `proposition`, `corollary`, `proof`, `instance`, `citation` |
| `source` | yes | `tex`, `lean`, `bib` |
| `title` | no | Display name (no hardcoded numbers) |
| `notes` | no | Content text with LaTeX + `\entryref{hash}` |
| `content` | no | Lean source code |
| `state` | no | `proven` or `sorry` (lean only) |
| `key` | no | Citation key (bib only) |

### Edge Convention
Edge (`ref = [A, B]`): sort inherited as pair `"(sort_A, sort_B)"`, notes describe dependency.
Cross-source edge: one tex + one lean atom = formalization correspondence.

---

## MDX Convention

Files: `.astrolabe/docs/00-index.mdx`, `01-intro.mdx`, `02-topic.mdx`, etc.

- `\entryblock{hash}` — block display with auto-numbering
- `\entryblock{hash}{collapsible}` — collapsible
- `\entryref{hash}{text}` — manual inline link
- `\entryref{hash}` — auto "Sort N.M" display

Numbering: section from filename prefix, proof excluded, never hardcode numbers.

---

## Architecture

- **Frontend**: Next.js + React + d3-force (deployed on Vercel)
- **API**: Next.js Route Handlers in `src/app/api/*` (Node) — read the `.md` store; no separate server
- **CLI tools**: Python scripts in `tools/` for the Lean → store pipeline, using `tools/astrolabe_store.py` (system `python3`, no venv needed)

## Rules

- Web dev: `npm run dev` (no backend to start)
- Communicate with user in Chinese
