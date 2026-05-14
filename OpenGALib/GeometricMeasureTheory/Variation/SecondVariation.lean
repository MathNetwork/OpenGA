import OpenGALib.GeometricMeasureTheory.HasNormal
import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Operators.SecondFundamentalForm
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Util.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# GMT.Variation.SecondVariation

Full-form second variation in Jacobi form for codim-1 varifolds with
unit normal $\nu$ in an ambient Riemannian manifold $M$:
$$\delta^2 V(\varphi) = \int_M
    \big(\|\nabla^M \varphi\|^2 -
         (|A|^2 + \mathrm{Ric}(\nu, \nu)) \varphi^2\big)\, d\|V\|.$$

Composes `‖grad_g[I] φ‖²_g`, `secondFundamentalFormSqNorm`, and `ricci`.

Distinct from the kinetic-only `secondVariation` in `SecondVariation.lean`
(curvature placeholdered as 0): `secondVariationFull` restores the
curvature contribution. Bodies use `Classical.choose` over existence
axioms (PRE-PAPER); curvature contribution becomes non-vacuous when
those axioms are replaced with constructive defs.

**Ground truth**: Simon 1983 §49 (Jacobi formula); Schoen-Simon 1981
§1 (stable hypersurfaces); Wickramasekera 2014 §2.
-/

open scoped ContDiff Manifold Riemannian
open Riemannian

namespace GeometricMeasureTheory.Variation

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Math.** **Full-form second variation** $\delta^2 V(\varphi)$ in the Jacobi
form for a codim-1 varifold:
$$\delta^2 V(\varphi) = \int (|\nabla^M \varphi|^2 -
    (|A|^2 + \mathrm{Ric}(\nu, \nu)) \varphi^2)\, d\|V\|.$$

Requires:
  * `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`,
    `[NontriviallyNormedField ℝ]` for the underlying Riemannian primitives;
  * `[Varifold.HasNormal I V]` providing the unit normal field.

The kinetic term is the polymorphic `‖grad_g[I] φ‖²_g`; the curvature
term combines `secondFundamentalFormSqNorm` and `ricci`. All three
primitives currently use `Classical.choose` over existence axioms
(PRE-PAPER); the real values come online when those existence axioms
are replaced with constructive defs.

**Ground truth**: Simon 1983 §49; Schoen-Simon 1981 §1; Wic14 §2. -/
noncomputable def secondVariationFull
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [Riemannian.HasMetric I M]
    (V : Varifold M) [hN : Varifold.HasNormal I V]
    (φ : M → ℝ) : ℝ :=
  -- PRE-PAPER: `Varifold.HasNormal.unitNormal` is raw
  -- `(x : M) → TangentSpace I x` without smoothness witness. Wrap with
  -- `sorry` for the smoothness fields until `HasNormal` is upgraded
  -- with a `unitNormal_smooth` field.
  let νSmooth : SmoothVectorField I M :=
    ⟨hN.unitNormal, sorry⟩
  ∫ x, (‖grad_g[I] φ‖²_g x -
        (secondFundamentalFormSqNorm hN.unitNormal x +
         ricci νSmooth νSmooth x) * φ x ^ 2)
      ∂V.massMeasure

end GeometricMeasureTheory.Variation
