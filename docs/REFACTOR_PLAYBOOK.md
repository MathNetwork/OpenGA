# Refactor Playbook

Source of truth for OpenGALib refactor workflows. Sister to `scripts/` (reusable codemods) and the project's CLAUDE.md (architectural stance). Goal: **same operation never costs more than the first time**.

## Decision tree

```
What's the refactor about?
├─ Rename a single identifier (def, theorem, structure field)?
│   └─ VSCode F2 (Rename Symbol).
│      Lean LSP scans the import graph semantically.
│      Doesn't touch docstrings/comments. Safest possible.
│
├─ Rewrite an import path prefix across many files?
│   └─ scripts/rewrite-import.sh OLD_PREFIX NEW_PREFIX
│      Idempotent, refuses dirty working tree, prefix-match.
│
├─ Move file or directory?
│   └─ git mv first, then scripts/rewrite-import.sh.
│      git mv preserves rename detection in history.
│
├─ Introduce or migrate notation?
│   └─ Hand-write a 5-line example file FIRST. Verify parsing,
│      typeclass inference, simp interaction — before any sweep.
│      THEN bulk-migrate via perl/sed AND audit docstrings
│      (text replace catches them too — see Pitfalls #2).
│
├─ Change a typeclass cascade or generic signature?
│   └─ Manual. No bulk tool helps. Build incrementally.
│      Use git checkpoints between each step.
│
├─ Need an AST-aware operation (rename only in code, not in
│   docstrings; find all theorems referencing X; etc.)?
│   └─ Lake script. See "Lake script vs bash" below.
│
├─ Bulk delete dead content (e.g., a sub-package being removed)?
│   └─ git rm -r + scripts/lean-grep.sh to find dangling refs +
│      manual cleanup of those refs.
│
└─ Consolidate textbook-style sub-files into a single verifiable
   object (e.g., `Metric/{Basic, Riesz, Smooth, RieszSmooth}.lean`
   → `Metric.lean`)?
   └─ See "Verifiable-object consolidation" below.
      Merge + private engineering + section organization +
      redirect downstream imports + delete sub-files.
```

## Pitfalls (encountered, in this lib's history)

1. **Text-level sed corrupts docstrings.** `sed 's/X/Y/g'` on `.lean`
   files matches `X` inside `/-- ... -/` blocks too. After bulk
   migration, search docstrings with `scripts/lean-grep.sh '<old form>'`
   and clean residual mentions. Or use VSCode F2 (semantic) when
   available.

2. **`open scoped X` requires the namespace to exist via imports.**
   Adding `open scoped X` to a file whose import graph doesn't reach a
   `namespace X` declaration produces "unknown namespace X" build
   error. After any sweep that adds scoped opens, verify with
   `scripts/lean-grep.sh 'open scoped'`.

3. **Notation prefix conflicts with built-in syntax.**
   - `T[x]` clashes with Lean's array indexing (`term[term]`)
   - `T x` (where `T` is an identifier) is parsed as function
     application, beating a `notation:max "T " x:max` pattern
   - Solutions that work: paren form (`Tan(x)`, like `Ric(X, Y)`),
     bracket form with non-identifier prefix (`∇[X]`, since `∇` is in
     Unicode category `Sm`, not `Lu`).

4. **Notation requires careful eta-reduction.** `fun x => f x`
   wrappers in notation RHS create lambdas that don't beta-reduce in
   simp's normal form, breaking pattern matches in subsequent rewrites.
   Always eta-reduce: `notation X => f` not `notation X => fun x => f x`.

5. **Typeclass inference can fail through `_` in notation.** A
   `notation:max "Tan(" x ")" => TangentSpace _ x` gets stuck when
   Lean can't pin the implicit `I : ModelWithCorners` from
   surrounding context. If this happens repeatedly, either:
   (a) keep the original verbose form `TangentSpace I x`, or
   (b) make `I` explicit in the notation.
   `abbrev`-based shorthands hit similar issues.

6. **Library-wide section deletion needs Python, not sed.** When deleting
   a section bracketed by patterns like `^/-! ## UXTest` ... `^end XYZTest`
   across many files, BSD `sed -i` patterns get fragile (different test
   sections have different end-marker names). Python with `re.match` per
   line, plus a backwards search for the matching `end XYZTest`, is
   reliable and self-explaining. See `/tmp/strip_uxtest.py` style:
   collect target files via `glob`, walk lines, locate start/end, splice.

7. **Bulk attribution-paragraph strip needs paragraph-level matching.**
   Phase A external ports left `**Inspired by** <repo>/...` paragraphs
   (multi-line, ending at blank line or `-/`). A line-level grep+replace
   only catches one line; you need to walk lines and skip from
   `Inspired by` line through next blank line / `-/` / next `## ` heading.

8. **Force-pushing to remove an oversight is partially effective.**
   `Co-Authored-By: ...` trailers, once pushed to a public repo,
   remain in GitHub's contributor cache even after the commit is
   force-pushed away. The orphan commit is still server-side. Lesson:
   **don't push to a public repo with a trailer you'd regret**.

---

## Verifiable-object consolidation

The refactor that turns a *textbook-chapter*-shaped split (`Foo/Basic.lean`
+ `Foo/Riesz.lean` + `Foo/Smooth.lean` + ... + `Foo.lean` facade) into
a single *verifiable-object*-shaped file (one `Foo.lean` containing the
full public API of one math object).

Performed for: `Riemannian/Curvature.lean`, `Riemannian/Gradient.lean`,
`Riemannian/Operators/{Hessian, Laplacian}.lean` (rename + doc cleanup,
no merge), `Riemannian/Metric.lean` (5 → 1 merge),
`Riemannian/TangentBundle.lean` (4 → 1 merge),
`Riemannian/HessianLie.lean` (4 → 1 merge),
`Riemannian/Connection.lean` (5 → 1 merge, ~2100 line single file).

### When to use

* The current split corresponds to a workflow stage (`Basic` →
  `Riesz` → `Smooth`), not to a sub-object boundary.
* Every consumer needs the union of two or more sub-files anyway
  (e.g., `LeviCivita.lean` needed both `Riesz` and `RieszSmooth`).
* The facade is just `import Sub1; import Sub2; import Sub3` with
  re-export semantics, no value beyond namespace bundling.
* Sub-files share the same `variable` block — duplication is itself
  a smell.

### When NOT to use

* The sub-files correspond to genuinely separate math objects
  (e.g., `riemannCurvature` vs `ricci` could plausibly be split if
  consumers diverge — though currently they don't).
* The split provides actual modularity (consumer A imports only
  the lightweight typeclass def, consumer B imports the heavy
  smoothness theorems). Check `lean-grep` for asymmetric usage
  before merging.
* Sub-file is a forward-compat / Mathlib-bridge / experimental
  layer with its own life cycle (`MathlibBridge.lean` stayed
  separate after the Metric refactor for this reason).

### Procedure

1. **Identify the object.** Read the sub-files. Confirm they're all
   API for the same math object (`RiemannianMetric` typeclass +
   inner + Riesz + smoothness = one object; not four).

2. **Audit external consumers.** For every public symbol in the
   sub-files, grep the entire repo for references outside the
   sub-files themselves:
   ```
   scripts/lean-grep.sh '\b(symbol1|symbol2|...)\b'
   ```
   Mark each as: (a) public, externally consumed; (b) internal
   only — candidate for `private`.

3. **Audit external imports.** For each sub-file, grep `import` of
   that path:
   ```
   scripts/lean-grep.sh 'import OpenGALib.Riemannian.Metric\.'
   ```
   List the consumer files. They will need their `import` lines
   redirected.

4. **Plan section structure.** Order by dependency / use flow,
   not by file-of-origin. For Metric: Typeclass → Inner +
   algebra → TangentSpace instances → Riesz → Smoothness.

5. **Write the unified file.** One `import` block (union),
   one `variable` block (factored across sections where
   applicable), section comments mark the structure. Engineering
   helpers get `private` if step 2 says they're internal-only.

6. **Redirect imports.** For each consumer file from step 3,
   replace `import OpenGALib.Foo.Sub1` (etc.) with the single
   `import OpenGALib.Foo`. Multiple sub-imports collapse to one
   line.

7. **Delete sub-files.** `rm OpenGALib/Foo/Sub*.lean`.

8. **Verify per-file.** `lake env lean OpenGALib/Foo.lean` (LSP
   diagnostics — silent = clean). Then each downstream consumer.
   Then full `lake build OpenGALib.<TopNamespace>`.

9. **Drop SelfTest sections.** Sub-file facades often have
   `example` blocks proving the typeclass cascade works. These
   are documentation, not tests — delete on consolidation.

10. **Module docstring.** Rewrite to `# Object` + 1-paragraph
    summary + `## Main definitions` + `## Main results` +
    `Reference: <book §X>`. Drop historical/phase-tracking
    narrative.

### Programmatic consolidation for large multi-file merges

For `Connection/{5 files}.lean` (2500 lines) and similar large refactors,
hand-writing a unified `.lean` file is too costly. Use a Python script:

1. Walk each sub-file in dep order (bottom-up: leaf first, facade last).
2. Collect imports / `open` / `open scoped` into sets (deduped at write time).
3. Strip per-sub-file leading docstring + `namespace X` / `end X` wrappers.
4. Detect notation-using lines that need denotation (e.g. `∇[X] Y` → `covDeriv X Y`)
   if the unified file imports nothing downstream — handle by inline regex *or*
   manual fix after build error report.
5. Tag known-internal symbols `private` via post-pass regex
   (`^(theorem|def|noncomputable\s+def) <name>` → prepend `private`).
6. Write unified file with one module docstring at top.

Pattern as run on Connection: ~50-line script, 90% mechanical, manual
fix-up of the 1-2 notation-bearing lines after first build attempt.
Saves ~30 min vs hand-writing.

### Pitfalls specific to consolidation

* **Cyclic import via `Internal.lean` split.** Tempted to put
  engineering in `Foo/Internal.lean` and re-import from
  `Foo.lean`? `Foo/Internal.lean` would need the typeclass
  defined in `Foo.lean` first. Solution: keep everything in
  `Foo.lean`, use `private` + sections instead of file split.
  (Tried during Metric refactor, abandoned.)

* **`where`-aux blocks don't cross-reference.** Tempted to extract
  proof helpers into `where`-aux at the bottom of a theorem? They
  can't see each other. If `helper2` references `helper1`'s type,
  `where`-aux won't compile. Solution: keep them inline as
  `have` clauses, or extract to top-level `private theorem`s
  outside the `where`-aux. (Tried during Curvature refactor on
  `ricciFormAt`, reverted.)

* **`backward.isDefEq.respectTransparency false` propagation.**
  TangentSpace instance bridges need this option in scope. When
  consolidating, the `set_option ... in` markers must come *with*
  each instance/theorem that needs them, not at file top
  (file-level `set_option` doesn't propagate transparently
  through subsequent `instance` decls in the way you'd expect).

* **Linter `unused section variable` after consolidation.** When
  merging, a single `variable [g : RiemannianMetric I M]` block
  covers both the typeclass-needing and typeclass-free theorems.
  The linter flags theorems where `g` is unused. Add `omit [g]
  in` (or `omit [IsManifold I ∞ M] in`, etc.) before each
  affected theorem.

* **Unicode notation `quotPrecheck` failure.** `local notation
  "𝒞[" V "]" => SmoothVectorField.const ...` failed because Lean
  rejects `𝒞` as an identifier head. Fall back to ASCII (`cF[V]`)
  or use a Unicode symbol that's category `Sm` (e.g. `∇`, `⟦⟧`).

* **`sed` double-substitution on `notation` lines.** `local
  notation "cF[" V "]" => SmoothVectorField.const X V` — running
  `sed 's|SmoothVectorField.const X V|cF[V]|g'` substitutes the
  RHS too, producing recursive `notation "cF[" V "]" => cF[V]`.
  Always exclude the notation declaration line from the sed
  pass, or use the Edit tool with `replace_all=false` to be
  surgical.

* **BSD `sed -i` differs from GNU.** `\b` word boundary doesn't
  work on macOS BSD sed. Use the Edit tool's `replace_all` mode
  for cross-platform identifier renames within a single file.

