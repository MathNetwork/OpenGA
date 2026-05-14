import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Bump functions

Bump-function infrastructure for partition-of-unity, cutoff, smoothing,
and test-section constructions, layered from scalar to manifold:

1. Scalar bumps on $\mathbb{R}$ (`expDamping`, `smoothStep`).
2. Radial bumps on a normed space (`radialBump = ContDiffBump`).
3. Manifold bumps (`manifoldBump = SmoothBumpFunction`).
4. Tangent vector field extension (`extendVectorField`): smooth section
   of $TM$ supported in a bump neighborhood of `x`, value `v` at `x`.

## Main definitions

* `expDamping`, `smoothStep` — re-exports of Mathlib primitives.
* `radialBump c` — `ContDiffBump c` (re-export).
* `manifoldBump c` — `SmoothBumpFunction I c` (re-export).
* `someBump c` — canonical accessor on a finite-dim manifold.
* `extendVectorField x v y` — bump-multiplied extension of $v \in T_xM$.

## Main results

* `extendVectorField_at` — value at center is `v`.
* `extendVectorField_zero_outside_support` — vanishes off the bump support.

Reference: Lee, *Smooth Manifolds*, §2.
-/

open scoped ContDiff Manifold

namespace Riemannian
namespace BumpFunction

/-! ## Scalar bumps on $\mathbb{R}$ -/

/-- **Math.** $\varphi(t) = e^{-1/t}$ for $t > 0$, zero for $t \le 0$.
The standard non-analytic-but-$C^\infty$ glue. -/
noncomputable abbrev expDamping : ℝ → ℝ := expNegInvGlue

theorem expDamping_contDiff {n : ℕ∞} : ContDiff ℝ n expDamping :=
  expNegInvGlue.contDiff

theorem expDamping_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : expDamping t = 0 :=
  expNegInvGlue.zero_of_nonpos h

theorem expDamping_pos_of_pos {t : ℝ} (h : 0 < t) : 0 < expDamping t :=
  expNegInvGlue.pos_of_pos h

theorem expDamping_nonneg (t : ℝ) : 0 ≤ expDamping t :=
  expNegInvGlue.nonneg t

/-- **Math.** Smooth transition: $0$ on $(-\infty, 0]$, $1$ on
$[1, \infty)$, $C^\infty$ everywhere. -/
noncomputable abbrev smoothStep : ℝ → ℝ := Real.smoothTransition

theorem smoothStep_contDiff {n : ℕ∞} : ContDiff ℝ n smoothStep :=
  Real.smoothTransition.contDiff

theorem smoothStep_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : smoothStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos h

theorem smoothStep_one_of_one_le {t : ℝ} (h : 1 ≤ t) : smoothStep t = 1 :=
  Real.smoothTransition.one_of_one_le h

theorem smoothStep_nonneg (t : ℝ) : 0 ≤ smoothStep t :=
  Real.smoothTransition.nonneg t

theorem smoothStep_le_one (t : ℝ) : smoothStep t ≤ 1 :=
  Real.smoothTransition.le_one t

/-! ## Radial bumps on a normed space -/

/-- **Math.** Smooth radial bump on a normed space, centered at `c`,
with prescribed inner/outer radii. -/
abbrev radialBump {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) : Type _ := ContDiffBump c

/-! ## Manifold bumps -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Math.** Smooth bump function on $M$ centered at `c`: $C^\infty$,
compactly supported in the chart at `c`, equal to $1$ near `c`, valued
in $[0, 1]$. -/
abbrev manifoldBump (c : M) : Type _ := SmoothBumpFunction I c

variable [FiniteDimensional ℝ E]

/-- **Math.** A canonical smooth bump function centred at $c$,
choice-extracted from the `Nonempty` instance. Used when a specific
radius is not required. -/
noncomputable def someBump (c : M) : SmoothBumpFunction I c :=
  Classical.choice inferInstance

/-! ## Tangent vector field extension -/

variable [IsManifold I ∞ M]

/-- **Math.** Given $v \in T_xM$, a smooth section $\widetilde{v}$ of
$TM$ supported in `(someBump x).tsupport` with $\widetilde{v}(x) = v$.
Used to construct test sections in Riesz extractions; locality of the
functional eliminates extension dependence. -/
noncomputable def extendVectorField (x : M) (v : TangentSpace I x) (y : M) :
    TangentSpace I y :=
  (((someBump x : SmoothBumpFunction I x) : M → ℝ) y) • (v : E)

omit [IsManifold I ∞ M] in
@[simp]
theorem extendVectorField_at [T2Space M] (x : M) (v : TangentSpace I x) :
    extendVectorField x v x = v := by
  show ((someBump x : SmoothBumpFunction I x) : M → ℝ) x • (v : E) = v
  rw [SmoothBumpFunction.eq_one]
  exact one_smul ℝ v

omit [IsManifold I ∞ M] in
theorem extendVectorField_zero_outside_support
    (x : M) (v : TangentSpace I x) (y : M)
    (h : y ∉ tsupport ((someBump x : SmoothBumpFunction I x) : M → ℝ)) :
    extendVectorField x v y = (0 : E) := by
  show ((someBump x : SmoothBumpFunction I x) : M → ℝ) y • (v : E) = 0
  rw [image_eq_zero_of_notMem_tsupport h, zero_smul]

end BumpFunction
end Riemannian
