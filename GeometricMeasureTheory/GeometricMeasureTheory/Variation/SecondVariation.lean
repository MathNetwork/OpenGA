import GeometricMeasureTheory.HasNormal
import Riemannian.Curvature
import Riemannian.SecondFundamentalForm
import Riemannian.Gradient
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# AltRegularity.GMT.Variation.SecondVariation

Full-form second variation $\delta^2 V(\varphi)$ for codim-1 varifolds
in the Jacobi form.

## Form

The full GMT second-variation Jacobi formula for a varifold $V$ with
codim-1 support and unit normal $\nu$, ambient Riemannian manifold $M$:
$$\delta^2 V(\varphi) = \int_M
    \big(|\nabla^M \varphi|^2 -
         (|A|^2 + \mathrm{Ric}(\nu, \nu)) \varphi^2\big)\, d\|V\|.$$

Where:
  * $|\nabla^M \varphi|^2$ — squared norm of the manifold gradient
    (`Riemannian.manifoldGradientNormSq`);
  * $|A|^2$ — squared norm of the second fundamental form
    (`Riemannian.secondFundamentalFormSqNorm`);
  * $\mathrm{Ric}(\nu, \nu)$ — Ricci curvature in the normal direction
    (`Riemannian.ricci`).

## Relationship to existing `secondVariation`

The pre-Phase-1.5 `secondVariation` in `SecondVariation.lean` uses
the kinetic-only form (curvature term placeholdered as 0). The full
form here, `secondVariationFull`, restores the curvature contribution
by composing `Riemannian.secondFundamentalFormSqNorm + Riemannian.ricci`.
Both bodies depend on `Classical.choose` over existence axioms (PRE-PAPER);
the curvature contribution is non-vacuous when those existence axioms
are replaced with constructive defs (Phase 4 repair trigger).

**Ground truth**: Simon 1983 §49 (Jacobi formula); Schoen-Simon 1981
§1 (stable hypersurfaces); Wickramasekera 2014 §2.
-/

open scoped ContDiff Manifold
open Riemannian

namespace GeometricMeasureTheory.Variation

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Full-form second variation** $\delta^2 V(\varphi)$ in the Jacobi
form for a codim-1 varifold:
$$\delta^2 V(\varphi) = \int (|\nabla^M \varphi|^2 -
    (|A|^2 + \mathrm{Ric}(\nu, \nu)) \varphi^2)\, d\|V\|.$$

Requires:
  * `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`,
    `[NontriviallyNormedField ℝ]` for the underlying Riemannian primitives;
  * `[Varifold.HasNormal I V]` providing the unit normal field.

The kinetic term is `manifoldGradientNormSq`; the curvature term
combines `secondFundamentalFormSqNorm` and `ricci`. All three primitives
currently use `Classical.choose` over existence axioms (PRE-PAPER); the
real values come online when their existence axioms are replaced with
constructive defs (Phase 4 catch-up event with Mathlib's eventual
Riemannian curvature operators).

**Ground truth**: Simon 1983 §49; Schoen-Simon 1981 §1; Wic14 §2. -/
noncomputable def secondVariationFull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    (V : Varifold M) [hN : Varifold.HasNormal I V]
    (φ : M → ℝ) : ℝ :=
  ∫ x, (manifoldGradientNormSq I φ x -
        (secondFundamentalFormSqNorm hN.unitNormal x +
         ricci hN.unitNormal hN.unitNormal x) * φ x ^ 2)
      ∂V.massMeasure

end GeometricMeasureTheory.Variation
