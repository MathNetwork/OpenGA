import GeometricMeasureTheory.Varifold
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Trace

/-!
# AltRegularity.GMT.Variation.Divergence

Ambient divergence operator on the model normed space and the manifold.

This file collects the divergence operators previously living in
`Stationary.lean`. Phase 1.5 refactor: variation operators (divergence,
first variation, second variation) live under the `Variation/`
sub-namespace; the old `Stationary.lean` / `SecondVariation.lean` re-export
for backward compatibility.

**Used by**: `Variation.FirstVariation`, `Variation.SecondVariation`.
-/

open scoped ContDiff Manifold
open VectorField

namespace GeometricMeasureTheory.Variation

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Ambient divergence on a normed space**:
$\mathrm{div}\,V(y) := \mathrm{tr}(\mathrm{D}V(y))$
where $\mathrm{D}V(y) : E \to E$ is the Fréchet derivative of
$V : E \to E$. Implemented via `LinearMap.trace ℝ E ∘ fderiv ℝ V`.

Returns 0 if $V$ is not differentiable at $y$ (Mathlib convention),
or if $E$ is infinite-dimensional / has no finite basis. For
finite-dim ambients (paper §6 setting: ambient $M^{n+1}$ is a closed
Riemannian manifold), the def gives the standard ambient divergence.

**Ground truth**: standard differential calculus (Simon §38). -/
noncomputable def divergenceFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E → E) (y : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ V y).toLinearMap

/-- **Ambient divergence of a vector field on the manifold** $M$ at $x$,
computed via chart pullback to the model space $E$.

Concretely: pull back $X$ from $M$ to $E$ via the inverse chart at $x$
(using `VectorField.mpullbackWithin`), then take the flat-space
divergence at the chart image of $x$. For a flat ambient ($M$ open in
a normed space), this equals the standard divergence; for curved
ambients the value is chart-local (matching the Riemannian
divergence in normal coordinates). -/
noncomputable def divergenceM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (X : Π (x : M), TangentSpace I x) (x : M) : ℝ :=
  divergenceFlat
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I))
    ((extChartAt I x) x)

end GeometricMeasureTheory.Variation
