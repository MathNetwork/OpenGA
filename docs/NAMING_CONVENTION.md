# Naming and Style Convention

Lib-wide rules for definitions, theorems, file structure. Goal: code reads like textbook math at the API surface, with engineering noise hidden. New code conforms from the start; any refactor pass must conform.

## 1. Object suffixes (definitions)

Use the smallest math-meaning suffix that describes the object's *type*.

| Suffix | Meaning | Example |
|---|---|---|
| `Endo` | endomorphism `V → V` | `curvatureEndo`, `ricciEndo` |
| `Tensor` | tensor (typically `(0,k)` as bilinear form) | `ricciTensor`, `metricTensor` |
| `Bilin` | bilinear form, when `Tensor` is ambiguous | `koszulBilin` |
| `Sharp` / `Flat` | musical iso $\sharp$ / $\flat$ | `ricciSharp`, `gradFlat` |
| `Dual` | dual vector / dual operation | `metricDual` |
| `Form` | when the math name is "X form" | `quadraticForm` |

Avoid engineering suffixes: `Map`, `Func`, `Fn`, `Function`, `At` / `AtPoint` / `Pt` (when basepoint is just an argument), `Tower`, `Stack`, `Wrapper`, `Aux`, `Bundle` (when not literally a vector bundle). If the object truly *is* a function, name it like one (`gradient`, not `gradientFunc`).

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

Compose multiple: `riemannCurvature_inner_self_zero` (one-line inner-self equality, RHS = 0).

**Avoid** descriptive prose in theorem names: not `riemannCurvature_inner_diagonal_zero`, not `ricci_is_symmetric_in_arguments`.

## 3. Naming case

* `lowerCamelCase` for definitions and theorems: `riemannCurvature`, `metricInner`.
* `UpperCamelCase` for types and namespaces: `RiemannianMetric`, `SmoothVectorField`.
* No `snake_case` for identifiers; `_` only as theorem-component separator (`riemannCurvature_antisymm`, not `riemann_curvature_antisymm`).

## 4. Boilerplate hiding via local notation

When a fully-qualified term `Foo.bar (x := X) (y := Y) v` appears 3+ times in a file, introduce file-local notation:

```lean
local notation "cF[" V "]" => SmoothVectorField.const (I := I) (M := M) V
```

Use the resulting binding inside proofs. Limits noise to a one-line declaration at the top of the section. Don't introduce notation for one-shot use.

## 5. Module docstring template

```lean
/-!
# <Module title — one line>

<Mathematical statement of what this module provides — textbook style.
Two to four short sentences; no Lean-implementation jargon.>

## Main definitions

* `name1` — one-line gloss.
* `name2` — one-line gloss.

## Main results

* `theorem1` — one-line gloss.

Reference: <do Carmo §X / Simon §Y / Pitts §Z / etc.>
-/
```

## 6. `private` versus `protected` versus public

* Internal-only helper: `private` (file-local).
* Helper exposed to a closely related submodule but not user-facing: `protected` (namespace-prefixed access required).
* Public: no modifier.

Default to `private` for any helper without a clear API consumer.
