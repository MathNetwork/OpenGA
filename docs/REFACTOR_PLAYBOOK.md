# Refactor Playbook

Source of truth for refactor workflows. Sister to `scripts/` (codemods) and CLAUDE.md (architectural stance). Goal: **same operation never costs more than the first time**.

## Decision: pick the right tool

| Refactor | Tool |
|---|---|
| Rename a single identifier | VSCode F2 (Lean LSP, semantic, skips docstrings) |
| Rewrite an import path prefix | `scripts/rewrite-import.sh OLD NEW` |
| Move file or directory | `git mv` then `scripts/rewrite-import.sh` |
| Introduce or migrate notation | Hand-write a 5-line example file FIRST (verify parsing, typeclass inference, simp interaction), then bulk-migrate, then audit docstrings (sed catches them too) |
| Change a typeclass cascade | Manual, incremental, git checkpoints |
| AST-aware (rename in code only, find theorems referencing X, audit `@[simp]` shapes) | Lake script (`import Lean`, use `Lean.Environment` etc.) |
| Bulk delete dead content | `git rm -r` then `scripts/lean-grep.sh` for dangling refs |
| Consolidate sub-files into one anchor | See "Verifiable-object consolidation" below |

## Pitfalls (from this lib's history)

1. **`sed` corrupts docstrings.** Matches inside `/-- ... -/` too. After bulk migration, `scripts/lean-grep.sh '<old form>'` and clean residual mentions.
2. **`open scoped X` requires the namespace to exist via imports.** Otherwise "unknown namespace X" build error. Verify with `scripts/lean-grep.sh 'open scoped'`.
3. **Notation prefix conflicts with built-in syntax.** `T[x]` clashes with array indexing; `T x` (identifier prefix) loses to function application. Use paren form (`Ric(X, Y)`) or non-identifier prefix (`∇[X]`, where `∇` is Unicode `Sm`, not `Lu`).
4. **Notation requires eta-reduction.** `fun x => f x` in notation RHS breaks simp pattern matches. Always `notation X => f`, never `notation X => fun x => f x`.
5. **Typeclass inference fails through `_` in notation.** `notation "Tan(" x ")" => TangentSpace _ x` gets stuck when Lean can't pin the implicit. Either keep the verbose form or make the implicit explicit in the notation.
6. **Library-wide section deletion needs Python, not sed.** Different end-markers (`end XYZTest`) need per-line scanning with backwards-match for the closing token. BSD `sed -i` patterns are too fragile.
7. **Bulk attribution-paragraph strip needs paragraph-level matching.** `Inspired by ...` blocks span multiple lines ending at blank line / `-/` / next `## `. Line-level grep+replace only catches one line.
8. **Force-pushing doesn't fully remove a pushed `Co-Authored-By` trailer.** GitHub's contributor cache retains the orphan commit. Don't push to a public repo with a trailer you'd regret.

## Verifiable-object consolidation

Turn a textbook-chapter-shaped split (`Foo/{Basic, Riesz, Smooth}.lean` + `Foo.lean` facade) into one anchor `Foo.lean` containing the full public API.

**Use when:** sub-files correspond to workflow stages, not sub-objects; every consumer needs the union; the facade is just `import; import; import`; sub-files share the same `variable` block.

**Don't use when:** sub-files are genuinely separate math objects; the split provides real asymmetric modularity; the sub-file has its own life cycle (Mathlib-bridge, experimental).

**Procedure:**

1. **Audit consumers.** `scripts/lean-grep.sh '\b(symbol1|symbol2|...)\b'`. Mark public vs internal-only (the latter → `private` after merge).
2. **Audit imports.** `scripts/lean-grep.sh 'import OpenGALib.Foo\.'`. List consumer files to redirect.
3. **Write the unified file.** Single import block, single variable block, sections ordered by dependency, internal helpers `private`.
4. **Redirect imports** in consumer files (collapse multi-imports to one).
5. **Delete sub-files**, then `lake build OpenGALib.<TopNamespace>` to verify.

For 2000+ line merges, automate steps 3-5 with a Python script: walk sub-files in dep order, dedupe imports/opens, strip per-file docstring + namespace wrappers, post-pass regex to tag `private`.

### Pitfalls specific to consolidation

- **No `Internal.lean` split.** Tempting to extract engineering into `Foo/Internal.lean` and re-import — produces cyclic deps. Use `private` + sections inside the anchor instead.
- **`where`-aux blocks can't cross-reference.** Extract helpers as top-level `private theorem`s, not `where`-aux at the bottom.
- **`set_option backward.isDefEq.respectTransparency false`** must come *with* each instance/theorem that needs it, not at file top.
- **`unused section variable` after consolidation:** a single `variable [g : RiemannianMetric I M]` block covers typeclass-needing and typeclass-free theorems; add `omit [g] in` before each unaffected theorem.
- **`quotPrecheck` on Unicode notation prefix.** Lean rejects `𝒞` (Unicode category `Lu`) as identifier head. Fall back to ASCII (`cF[V]`) or category-`Sm` symbols (`∇`, `⟦⟧`).
- **`sed` self-substitution on notation lines.** `sed 's|RHS|cF[V]|g'` rewrites the notation declaration too. Exclude the declaration line or use Edit-tool with `replace_all=false`.
- **BSD vs GNU `sed -i`.** `\b` word boundary doesn't work on macOS. Use the Edit tool for cross-platform identifier renames.
