# Naming and Style Convention

Lib-wide rules for definitions, theorems, file structure. Goal: code reads like
textbook math at the API surface, with engineering noise hidden.

This document is **enforced**: any file refactor pass must conform. New code
should conform from the start.

## 1. Object suffixes (definitions)

Use the smallest mathematical-meaning suffix that describes the object's *type*.

| Suffix | Meaning | Example |
|---|---|---|
| `Endo` | endomorphism `V → V` | `curvatureEndo`, `ricciEndo` |
| `Tensor` | tensor (typically `(0,k)`-tensor as bilinear form) | `ricciTensor`, `metricTensor` |
| `Bilin` | bilinear form, when `Tensor` is ambiguous | `koszulBilin` |
| `Sharp` | musical isomorphism $\sharp$ (raise indices via metric) | `ricciSharp` |
| `Flat` | musical isomorphism $\flat$ (lower indices via metric) | `gradFlat` |
| `Dual` | dual vector / dual operation | `metricDual` |
| `Form` | when the math name is "X form" | `quadraticForm` (avoid bare `Form` for tensors) |

**Avoid these engineering suffixes**:

* `TraceMap`, `Map`, `Func`, `Fn`, `Function`
* `At` / `AtPoint` / `Pt` (when the basepoint is just an argument)
* `Tower`, `Stack`, `Wrapper`, `Aux`, `Bundle` (when not literally a vector bundle)

If the object truly *is* a function, name it like the function (e.g. `gradient`,
not `gradientFunc`).

## 2. Theorem suffixes (Mathlib convention)

| Suffix | Meaning |
|---|---|
| `_self` | argument repeated in two slots, e.g. `inner_self` for `⟨v, v⟩` |
| `_zero`, `_one` | result equals 0 / 1 |
| `_add`, `_sub`, `_neg`, `_smul` | algebra slot |
| `_apply` | reduce to underlying function form |
| `_iff_X` | bidirectional |
| `_of_X` | implication |
| `_eq_X` | concrete equality |
| `_comm` | commutativity |
| `_assoc` | associativity |
| `_symm` | symmetry |
| `_antisymm` | antisymmetry |

Compose multiple: `riemannCurvature_inner_self_zero` (one-line inner-self
equality, RHS = 0).

**Avoid** descriptive prose in theorem names: not
`riemannCurvature_inner_diagonal_zero`, not `ricci_is_symmetric_in_arguments`.

## 3. Naming case

* `lowerCamelCase` for definitions and theorems: `riemannCurvature`, `metricInner`.
* `UpperCamelCase` for types and namespaces: `RiemannianMetric`, `SmoothVectorField`.
* No `snake_case` for identifiers; `_` only as theorem-component separator
  (`riemannCurvature_antisymm`, not `riemann_curvature_antisymm` or
  `RiemannCurvatureAntisymm`).

## 4. Boilerplate hiding via local notation

When a fully-qualified term `Foo.bar (x := X) (y := Y) v` appears 3+ times in a
file, introduce file-local notation:

```lean
local notation "𝒞[" V "]" => SmoothVectorField.const (I := I) (M := M) V
```

Use the resulting binding inside proofs. Limits noise to a one-line declaration
at the top of the section.

Common patterns:

* Constant section: `𝒞[V]` for `SmoothVectorField.const (I := I) (M := M) V`.
* Tangent vector at a point: `T[x]` or `Tx[x]` if the type spelling is verbose.
* Don't introduce notation for one-shot use.

## 5. Module docstring template

```lean
/-!
# <Module title — one line>

<Mathematical statement of what this module provides — textbook style.
Two to four short sentences; no Lean-implementation jargon.>

<Optional: layering / context — where in the lib stack this lives.>

## Main definitions

* `name1` — one-line gloss.
* `name2` — one-line gloss.

## Main results

* `theorem1` — one-line gloss.

Reference: <do Carmo §X / Simon §Y / Pitts §Z / etc.>
-/
```

**Removed** (avoid these in module docstrings):

* `Inspired by ...` / `Adapted from ...` — attribution belongs in the project
  `NOTICE.md` if relevant.
* `## Form` — use `## Main definitions` instead.
* `## Sorry status` — `sorry`s carry per-theorem closure-path comments.
* `## Ground truth` — replace with one-line `Reference:` per theorem.
* "Real `noncomputable def`" / "Mathlib upstream candidate" — internal labels,
  not user-facing docs.

## 6. Per-definition / per-theorem docstring

```lean
/-- <Mathematical statement, in display math when natural>.

Reference: do Carmo §X. -/
theorem name ... := by ...
```

Three rules:

1. First sentence is the statement (math or natural-language).
2. One reference at the end (or none if obvious).
3. No proof-strategy commentary, no "this is a Lean trick" notes. Engineering
   commentary goes inside the proof body if essential.

## 7. Engineering hiding

When a theorem or instance has a long, primarily mechanical proof (50+ lines):

* If the proof has no internal cross-reference: use `where`-aux to attach helpers
  to the parent definition.
* If helpers cross-reference each other: extract as file-level `private theorem`s
  before the consumer.
* If the engineering is genuinely implementation-detail (instance diamond
  workaround, `set_option` overrides): wrap in a small section near the top of
  the file, not interleaved with math API.

Aim: a reader scrolling the file should see the math API in the first 20–30%
of lines; engineering should be visibly "below the fold".

## 8. UXTest sections

Removed. The build is the regression guard. Per-file `example` blocks that
re-state the typeclass cascade clutter the math API surface.

If a typeclass-cascade test is essential, place it in a dedicated test file
under `test/` (or use `#guard_msgs` for diagnostic regressions).

## 9. `private` versus `protected` versus public

* Internal-only helper: `private` (file-local).
* Helper exposed to a closely related submodule but not user-facing: `protected`
  (namespace-prefixed access required).
* Public: no modifier.

Default to `private` for any helper without a clear API consumer.

## 10. Refactor process

When refactoring a file:

1. Apply object renames to the file (per §1).
2. Apply theorem suffix renames (per §2).
3. Introduce `local notation` for repeated boilerplate (per §4).
4. Rewrite module docstring (per §5).
5. Tighten per-definition docstrings (per §6).
6. Move long proofs to `where`-aux or `private` (per §7).
7. Remove UXTest section if present (per §8).
8. Add `private` modifiers to internal helpers (per §9).
9. Verify LSP clean.
10. Update any other file's docstring that references the old name.

The reference example for this process is `Riemannian/Curvature.lean`.
