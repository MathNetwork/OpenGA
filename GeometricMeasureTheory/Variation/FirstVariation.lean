import GeometricMeasureTheory.Variation.Divergence
import GeometricMeasureTheory.HasNormal
import Riemannian.Connection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# AltRegularity.GMT.Variation.FirstVariation

Full-form first variation $\delta V(X)$ for codim-1 varifolds
carrying a unit normal field.

## Form

The full GMT first-variation formula for a varifold $V$ with codim-1
support and unit normal $\nu$:
$$\delta V(X) = \int (\mathrm{div}_M X - \langle \nu, \nabla_\nu X \rangle)\, d\|V\|.$$

The correction term $\langle \nu, \nabla_\nu X \rangle$ uses the
Levi-Civita connection on $M$ (`Riemannian.covDeriv`) and the
framework-owned inner product on `TangentSpace I x` (`metricInner`,
provided by `OpenGALib.RiemannianMetric I M`).

The mass-only `Varifold` does not carry tangent-plane data; the unit
normal is supplied by `Varifold.HasNormal` typeclass.

## Phase 4.7.6 migration

The Phase 1.5 placeholder `normalCorrection_exists` (vacuous existence
returning the zero function) is replaced by the real `noncomputable def`
`normalCorrection`, which evaluates to the textbook
$\langle \nu(x), \nabla_\nu X(x) \rangle_g$ via `metricInner x` and
`covDeriv`.

## Relationship to existing `firstVariation`

The pre-Phase-1.5 `firstVariation` in `Stationary.lean` uses the
ambient form (without normal correction) — accurate for codim-0,
documented codim-1 caveat. `firstVariationFull` here is the codim-1
specialization with the correction term, requires `[HasNormal V]`.
-/

open scoped ContDiff Manifold
open Riemannian OpenGALib

namespace GeometricMeasureTheory.Variation

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Codim-1 normal correction term** $\langle \nu(x), \nabla_\nu X(x) \rangle$
of the first variation, evaluated via the framework's `metricInner` and
`covDeriv` (Levi-Civita).

For a unit normal $\nu$ and a test vector field $X$, returns
$$\mathrm{normalCorrection}(I, X, \nu)(x) =
   \langle \nu(x), \nabla_{\nu(x)} X(x) \rangle_g$$
where $\nabla$ is the Levi-Civita connection (Phase 4.5.A) and
$\langle\cdot, \cdot\rangle_g$ is the framework-owned `metricInner`
(Phase 4.7.2). Replaces the pre-Phase-4.7 placeholder
`normalCorrection_exists` (vacuous existence over `True`).

**Ground truth**: Pitts 1981 §38; Simon 1983 §38 (codim-1 first
variation). -/
noncomputable def normalCorrection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X : TestVectorField I M)
    (ν : (x : M) → TangentSpace I x) (x : M) : ℝ :=
  metricInner x (ν x) (covDeriv ν X.toFun x)

/-- **Full-form first variation** $\delta V(X)$ for a codim-1 varifold:
$$\delta V(X) = \int (\mathrm{div}_M X - \langle \nu, \nabla_\nu X \rangle_g)\, d\|V\|.$$

Requires:
  * `[CompleteSpace E]`, `[FiniteDimensional ℝ E]` for the underlying
    `divergenceM` and Levi-Civita connection;
  * `[OpenGALib.RiemannianMetric I M]` providing the framework metric
    (Phase 4.7);
  * `[Varifold.HasNormal I V]` providing the unit normal field.

**Ground truth**: Pitts 1981 §38; Simon 1983 §38; codim-1 specialization
of $\delta V(X) = \int \mathrm{div}_S X\, dV(x, S)$.

For paper §6 codim-1 use, this is the paper-faithful first variation. -/
noncomputable def firstVariationFull
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (V : Varifold M) [hN : Varifold.HasNormal I V]
    (X : TestVectorField I M) : ℝ :=
  ∫ x, (divergenceM I X.toFun x - normalCorrection I X hN.unitNormal x)
      ∂V.massMeasure

end GeometricMeasureTheory.Variation
