import OpenGALib.GeometricMeasureTheory.Variation.Divergence
import OpenGALib.GeometricMeasureTheory.HasNormal
import OpenGALib.Riemannian.Connection.LeviCivita
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# GMT.Variation.FirstVariation

Full-form first variation $\delta V(X)$ for codim-1 varifolds
carrying a unit normal field.

## Form

The full GMT first-variation formula for a varifold $V$ with codim-1
support and unit normal $\nu$:
$$\delta V(X) = \int (\mathrm{div}_M X - \langle \nu, \nabla_\nu X \rangle)\, d\|V\|.$$

The correction term $\langle \nu, \nabla_\nu X \rangle$ uses the
Levi-Civita connection on $M$ (`Riemannian.covDeriv`) and the
framework-owned inner product on `TangentSpace I x` (`metricInner`,
provided by `Riemannian.RiemannianMetric I M`).

The mass-only `Varifold` does not carry tangent-plane data; the unit
normal is supplied by `Varifold.HasNormal` typeclass.
## Relationship to existing `firstVariation`

The pre-Phase-1.5 `firstVariation` in `Stationary.lean` uses the
ambient form (without normal correction) — accurate for codim-0,
documented codim-1 caveat. `firstVariationFull` here is the codim-1
specialization with the correction term, requires `[HasNormal V]`.
-/

open scoped ContDiff Manifold
open Riemannian

namespace GeometricMeasureTheory.Variation

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Math.** **Codim-1 normal correction term** $\langle \nu(x), \nabla_\nu X(x) \rangle$
of the first variation, evaluated via the framework's `metricInner` and
`covDeriv` (Levi-Civita).

For a unit normal $\nu$ and a test vector field $X$, returns
$$\mathrm{normalCorrection}(I, X, \nu)(x) =
   \langle \nu(x), \nabla_{\nu(x)} X(x) \rangle_g$$
where $\nabla$ is the Levi-Civita connection and
$\langle\cdot, \cdot\rangle_g$ is the framework-owned `metricInner`.

**Ground truth**: Pitts 1981 §38; Simon 1983 §38 (codim-1 first
variation). -/
noncomputable def normalCorrection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [HasMetric I M]
    (g : RiemannianMetric I M)
    (X : TestVectorField I M)
    (ν : (x : M) → TangentSpace I x) (x : M) : ℝ :=
  g.metricInner x (ν x) (covDeriv g ν X.toFun x)

/-- **Math.** **Full-form first variation** $\delta V(X)$ for a codim-1 varifold:
$$\delta V(X) = \int (\mathrm{div}_M X - \langle \nu, \nabla_\nu X \rangle_g)\, d\|V\|.$$

Requires:
  * `[CompleteSpace E]`, `[FiniteDimensional ℝ E]` for the underlying
    `divergenceM` and Levi-Civita connection;
  * `[Riemannian.HasMetric I M]` providing the framework metric;
  * `[Varifold.HasNormal I V]` providing the unit normal field.

**Ground truth**: Pitts 1981 §38; Simon 1983 §38; codim-1 specialization
of $\delta V(X) = \int \mathrm{div}_S X\, dV(x, S)$.

For paper §6 codim-1 use, this is the paper-faithful first variation. -/
noncomputable def firstVariationFull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [HasMetric I M]
    (g : RiemannianMetric I M)
    (V : Varifold M) [hN : Varifold.HasNormal I V]
    (X : TestVectorField I M) : ℝ :=
  ∫ x, (divergenceM I X.toFun x - normalCorrection I g X hN.unitNormal x)
      ∂V.massMeasure

end GeometricMeasureTheory.Variation
