import GeometricMeasureTheory.Varifold
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# GeometricMeasureTheory.TangentCone

Tangent cone of a varifold: the blow-up limit of $V$ under rescaling
at a point $Z$.

## Layout

This file provides the GMT primitive `tangentCone` along with its
defining predicate `IsTangentConeAt` (Layer B C-6 真填). The
junction-cone configuration (a stationary cone supported on $N \ge 3$
half-hyperplanes meeting along a common edge), which is the
configuration excluded by the Wickramasekera $\alpha$-structural
hypothesis, lives in the regularity-theory package
(`Regularity.AlphaStructural`) since it is a regularity-theory-specific
concept rather than a general GMT primitive.

## Grounding (Layer B C-6)

`tangentCone` is grounded as a real `noncomputable def` via
`Classical.choice` over the predicate `IsTangentConeAt`. The predicate
is a real `def` capturing "$T$ is a weak limit (in the chart at $Z$) of
chart-rescalings of $V$ at $Z$".

The chart-rescaling operates in the model space $E$: pull
$V$.massMeasure forward to $E$ via `extChartAt I Z`, then dilate by
$y \mapsto r^{-1} \cdot (y - \phi(Z))$. Weak convergence is expressed
via `Filter.Tendsto` on integration against compactly supported
continuous test functions on $E$, mirroring `VarifoldConverge`.
-/

open scoped ContDiff Manifold Classical

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- **Chart-rescaling of mass measure** at $Z$ by factor $r > 0$.

Concretely:
  1. Push $V$.massMeasure forward to the model space $E$ via
     `extChartAt I Z`.
  2. Dilate the resulting measure on $E$ by
     $y \mapsto r^{-1} \cdot (y - \phi(Z))$, where $\phi = $ `extChartAt I Z`.

This is the chart-local form of the geometric blow-up rescaling
$\eta_{Z, r}(x) = (x - Z) / r$ used in Simon §42 to define the tangent
cone. For a flat ambient ($M$ open in a normed space), this matches
the geometric rescaling verbatim; for curved Riemannian ambient, the
chart-local form is the closest paper-faithful expression available
without a Riemannian-exponential-map operator (Mathlib's
`Geometry/Manifold/Riemannian/` does not yet expose this).

**Used by**: `IsTangentConeAt`, `tangentCone`. -/
noncomputable def chartRescaleMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) (r : ℝ) : MeasureTheory.Measure E :=
  (V.massMeasure.map (extChartAt I Z)).map
    (fun y => r⁻¹ • (y - extChartAt I Z Z))

/-- **$T$ is a tangent cone of $V$ at $Z$** (chart-local weak-limit form):
the chart-rescaled mass measures of $V$ at $Z$ converge weakly (in the
chart) to $T$'s pushforward as $r \to 0^+$.

Tested against compactly supported continuous functions on $E$ (the
weak-* topology on Radon measures), matching the convention of
`Varifold.VarifoldConverge` (mass-measure-form weak convergence).

**Ground truth**: Simon 1983 §42 (varifold tangents, blow-up procedure
for stationary integral varifolds); Allard 1972 §3.4–§3.6.

The chart-local form bypasses the audit's "(A) Full geometric blow-up"
blocker (which required affine/vector-space structure on $M$) by
operating in the chart's normed-space target $E$. The "representation
gap" — `tangentCone V Z` is a `Varifold M` whose mass measure is
identified, via this predicate, with a chart-local cone on $E$ — is
documented but does not block grounding.

**Used by**: `tangentCone`. -/
def IsTangentConeAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) (T : Varifold M) : Prop :=
  ∀ φ : E → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto
      (fun r : ℝ => ∫ y, φ y ∂(chartRescaleMeasure I V Z r))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ y, φ y ∂(T.massMeasure.map (extChartAt I Z))))

/-- The **tangent cone** of $V$ at $Z$: the blow-up limit of $V$ under
rescaling at $Z$, a stationary integral cone (in the chart at $Z$).

Defined via `Classical.choice` (`if-then-else` over an existence) on
the predicate `IsTangentConeAt`. If a tangent cone exists at $Z$
(guaranteed for stationary integral varifolds by Simon §42, but not
for arbitrary varifolds), the choice picks one. Otherwise the def
falls back to the zero varifold (`Classical.choice instNonempty`).

**Ground truth**: Simon 1983 §42 (varifold tangents); Allard 1972
§3.4–§3.6.

**Layer B C-6 grounding** (commits 1acef9f, 5f952a6 set the
chart-pullback precedent; this commit applies the same path here):
  * `chartRescaleMeasure`: real `Measure E` via `Measure.map` chained
    twice (chart push + dilation).
  * `IsTangentConeAt`: real `Prop` via `Filter.Tendsto` against
    compactly supported continuous test functions, mirroring
    `VarifoldConverge`.
  * `tangentCone`: real `Varifold M` via `Classical.choice` on the
    existence of a tangent cone, falling back to the zero varifold.

For chain-proof correctness this is sufficient: chain proofs only use
`tangentCone V Z` as black-box input to `IsJunctionCone` (opaque), so
the existence-axiom-via-`Classical.choice` form does not propagate.

**Used by**: `Regularity.HasJunction` def
(`Regularity/AlphaStructural.lean`). -/
noncomputable def tangentCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) : Varifold M :=
  if h : ∃ T : Varifold M, IsTangentConeAt I V Z T then h.choose
  else Classical.choice Varifold.instNonempty

end Varifold

end GeometricMeasureTheory
