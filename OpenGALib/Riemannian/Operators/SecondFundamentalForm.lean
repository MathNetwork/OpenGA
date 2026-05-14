import OpenGALib.Riemannian.Connection.LeviCivita
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Second fundamental form (codim-1)

For a hypersurface oriented by unit normal $\nu$, the **second fundamental
form** is the bilinear scalar
$$A(X, Y)(x) = \langle \nabla^M_X Y(x),\, \nu(x)\rangle.$$
Its trace and Frobenius norm give the **mean curvature** $H$ and
**squared norm** $|A|^2$.

The framework `RiemannianMetric` typeclass provides `metricInner` directly
on tangent vectors via `TangentSpace I x = E`, used here together with
`covDeriv` (Levi-Civita) and `stdOrthonormalBasis`.

## Main definitions

* `secondFundamentalFormScalar ν X Y x = ⟨∇^M_X Y, ν⟩(x)`.
* `secondFundamentalFormSqNorm ν x = ∑_{i,j} A(e_i, e_j)^2`.
* `meanCurvature ν x = ∑_i A(e_i, e_i)`.

## Main results

* `secondFundamentalFormSqNorm_nonneg`.

Reference: do Carmo, *Riemannian Geometry*, §6.2; Simon, *Geometric
Measure Theory*, §49.
-/

open Bundle
open scoped ContDiff Manifold Bundle

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Math.** $A(X, Y)(x) = \langle \nabla^M_X Y(x),\, \nu(x)\rangle$. -/
noncomputable def secondFundamentalFormScalar
    (ν X Y : VectorFieldSection I M) (x : M) : ℝ :=
  metricInner x (covDeriv X Y x) (ν x)

/-- **Math.** Notation `II(X, Y)` for the codim-1 second fundamental form
scalar, with the unit normal `ν` from context. -/
scoped[Riemannian] notation:max "II(" X ", " Y ")" =>
  secondFundamentalFormScalar X Y

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** $|A|^2(x) = \sum_{i,j} A(e_i, e_j)^2$ over the standard
orthonormal basis of `TangentSpace I x`. Basis-independent for
orthonormal frames. -/
noncomputable def secondFundamentalFormSqNorm
    (ν : VectorFieldSection I M) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, ∑ j, (secondFundamentalFormScalar (I := I) (M := M) ν
    (fun (_ : M) => (e i : TangentSpace I x))
    (fun (_ : M) => (e j : TangentSpace I x)) x) ^ 2

@[simp]
theorem secondFundamentalFormSqNorm_nonneg
    (ν : VectorFieldSection I M) (x : M) :
    0 ≤ secondFundamentalFormSqNorm ν x := by
  unfold secondFundamentalFormSqNorm
  positivity

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** $H(x) = \mathrm{tr}_g A(x) = \sum_i A(e_i, e_i)(x)$. -/
noncomputable def meanCurvature
    (ν : VectorFieldSection I M) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, secondFundamentalFormScalar (I := I) (M := M) ν
    (fun (_ : M) => (e i : TangentSpace I x))
    (fun (_ : M) => (e i : TangentSpace I x)) x

/-- **Math.** Notation `H_g[I] ν` for the mean curvature of a hypersurface
oriented by unit normal `ν`. -/
scoped[Riemannian] notation:max "H_g[" I "]" => meanCurvature (I := I)

end Riemannian
