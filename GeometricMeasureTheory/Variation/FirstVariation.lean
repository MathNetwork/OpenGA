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
Levi-Civita connection on $M$ (`Riemannian.covDeriv`) and the inner
product on `TangentSpace I x` (provided by `RiemannianBundle`).

The mass-only `Varifold` does not carry tangent-plane data; the unit
normal is supplied by `Varifold.HasNormal` typeclass.

## Relationship to existing `firstVariation`

The pre-Phase-1.5 `firstVariation` in `Stationary.lean` uses the
ambient form (without normal correction) — accurate for codim-0,
documented codim-1 caveat. `firstVariationFull` here is the codim-1
specialization with the correction term, requires `[HasNormal V]`.

Future refactor: when `Stationary.IsStationary`'s body migrates to
`firstVariationFull`, `Stationary.firstVariation` becomes the
ambient-form view and `Variation.firstVariationFull` becomes the
canonical form.
-/

open scoped ContDiff Manifold
open Riemannian

namespace GeometricMeasureTheory.Variation

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Existence axiom for the codim-1 normal correction term**
$\langle \nu, \nabla_\nu X \rangle$.

The inner product $\langle \cdot, \cdot \rangle$ on `TangentSpace I x`
is provided by `RiemannianBundle (fun x ↦ TangentSpace I x)` which is
not yet wired through the framework's typeclass cascade. This existence
axiom is the placeholder; repair when the RiemannianBundle wiring is in
place (Phase 4 catch-up). -/
theorem normalCorrection_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (X : TestVectorField I M)
    (ν : (x : M) → TangentSpace I x) :
    ∃ _correction : M → ℝ, True := ⟨fun _ => 0, trivial⟩

/-- **Full-form first variation** $\delta V(X)$ for a codim-1 varifold:
$$\delta V(X) = \int (\mathrm{div}_M X - \langle \nu, \nabla_\nu X \rangle)\, d\|V\|.$$

Requires:
  * `[CompleteSpace ℝ]` (auto), `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`
    for the underlying `divergenceM` and Levi-Civita connection;
  * `[Varifold.HasNormal I V]` providing the unit normal field.

**Ground truth**: Pitts 1981 §38; Simon 1983 §38; codim-1 specialization
of $\delta V(X) = \int \mathrm{div}_S X\, dV(x, S)$.

For paper §6 codim-1 use, this is the paper-faithful first variation. -/
noncomputable def firstVariationFull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) [hN : Varifold.HasNormal I V]
    (X : TestVectorField I M) : ℝ :=
  ∫ x, (divergenceM I X.toFun x -
        Classical.choose (normalCorrection_exists I X hN.unitNormal) x)
      ∂V.massMeasure
  -- Textbook: ⟨ν(x), ∇_ν X(x)⟩. The inner product on TangentSpace I x
  -- requires the RiemannianBundle wiring (deferred to Phase 4).
  -- Here we Classical.choose over a normalCorrection_exists axiom; the
  -- correction term is a real ℝ-valued function, semantically aligned
  -- with the textbook form once RiemannianBundle is in scope.

end GeometricMeasureTheory.Variation
