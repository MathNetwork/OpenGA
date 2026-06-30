# OpenGA Conventions

Canonical conventions for the OpenGALib Lean library — both the **mathematical**
choices (sign conventions, definitions) and the **naming / style** rules. Each
math convention carries its textbook source; **non-negotiable once anchored** —
disagreements are answered by citation, and the Lean source is authoritative when
prose and code disagree. The naming rules apply lib-wide so the API surface reads
like textbook math with engineering noise hidden; new code conforms from the
start, and any refactor pass must conform.

---

## Mathematical conventions

### Curvature sign

OpenGA uses do Carmo's convention throughout Riemannian and Comparison:

$$R(X, Y) Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z.$$

Ricci is the trace of $R(\,\cdot\,, Y) Z$ in its first slot; sectional curvature of the 2-plane spanned by $X, Y$ is

$$K(X, Y) = \frac{\langle R(X, Y) Y, X \rangle}{\langle X, X \rangle \langle Y, Y \rangle - \langle X, Y \rangle^2}.$$

Ground truth: do Carmo, *Riemannian Geometry*, Ch. 4 §2–§3. Same convention as Petersen and Cheeger–Ebin.

Implementation: `OpenGALib/Riemannian/Curvature/RiemannCurvature.lean`.

### Length functional

Length of a continuous path in a pseudo-extended-metric space is the metric-side total variation:

$$\operatorname{pathLength}(\gamma) := \operatorname{eVariationOn}(\gamma, [0, 1]).$$

Ground truth: Burago–Burago–Ivanov §2.1.

Applies uniformly to metric spaces, Riemannian manifolds (via `Bridges/RiemannianToLength`), Alexandrov spaces, and limits. The Mathlib tangent-integral length `Manifold.pathELength` (used inside `IsRiemannianManifold`) is a *separate* concept; equality on `C¹` paths is the content of `IsRiemannianManifold.toLengthSpace`.

Implementation: `OpenGALib.pathLength` in `OpenGALib/MetricGeometry/LengthSpace.lean`, wrapping `eVariationOn`.

### Geodesic existence

`GeodesicSpace` = length space in which the path-length infimum is attained between every pair of points. Existence only — neither uniqueness nor regularity is part of the definition.

Ground truth: Burago–Burago–Ivanov §2.5.5. Hopf–Rinow (complete Riemannian ⇒ geodesic) belongs to Layer 3a; Layer 1 is metric-only.

Implementation: `OpenGALib.GeodesicSpace` in `OpenGALib/MetricGeometry/GeodesicSpace.lean`.

### Metric measure space

`MetricMeasureSpace M` = `structure` carrying a `PseudoEMetricSpace M` together with a `MeasureTheory.Measure M`. Both stored as data (not typeclasses), so a single carrier may host multiple metric-measure structures. No regularity / σ-finiteness / Radon hypotheses baked in — added at the use site, matching Mathlib's `MeasureTheory.Measure` discipline.

Ground truth: Gromov §3¹⁄₂.5 (mm-spaces); Burago–Burago–Ivanov §1.7.

Implementation: `MetricMeasureSpace` in `OpenGALib/MetricGeometry/MetricMeasureSpace.lean`.

---

## Naming & style

### Object suffixes (definitions)

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

### Theorem suffixes (Mathlib convention)

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

### Naming case

* `lowerCamelCase` for definitions and theorems: `riemannCurvature`, `metricInner`.
* `UpperCamelCase` for types and namespaces: `RiemannianMetric`, `SmoothVectorField`.
* No `snake_case` for identifiers; `_` only as theorem-component separator (`riemannCurvature_antisymm`, not `riemann_curvature_antisymm`).

### Boilerplate hiding via local notation

When a fully-qualified term `Foo.bar (x := X) (y := Y) v` appears 3+ times in a file, introduce file-local notation:

```lean
local notation "cF[" V "]" => SmoothVectorField.const (I := I) (M := M) V
```

Use the resulting binding inside proofs. Limits noise to a one-line declaration at the top of the section. Don't introduce notation for one-shot use.

### Module docstring template

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

### `private` versus `protected` versus public

* Internal-only helper: `private` (file-local).
* Helper exposed to a closely related submodule but not user-facing: `protected` (namespace-prefixed access required).
* Public: no modifier.

Default to `private` for any helper without a clear API consumer.
