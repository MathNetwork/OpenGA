import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Metric
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_DifferentialGeometry_RiemannianDistance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Normalized Riemannian three-manifolds

Kleiner-Lott, *Notes on Perelman's papers*, https://arxiv.org/abs/math/0605667,
Definition 77.1 (p. 146):

> A compact Riemannian 3-manifold is normalized if `|Rm| ≤ 1` everywhere, and the
> volume of every unit ball is at least half the volume of the Euclidean unit ball.

This file records that definition for a smooth Riemannian metric on a compact
three-manifold modelled on `EuclideanSpace ℝ (Fin 3)`:

* `OpenGA.riemannianUnitBall g x` is the ball of radius one around `x` for the
  Riemannian distance of `g`;
* `OpenGA.IsNormalizedMetric g` is the conjunction of the pointwise curvature bound
  `|Rm|_g ≤ 1`, expressed through the squared `g`-norm of the `(0,4)` curvature tensor,
  and the volume bound `vol (B(x,1)) ≥ (1/2) · (4π/3)` for the Riemannian volume
  measure of `g`.

The Euclidean unit ball in `ℝ ^ 3` has volume `4π/3`, so half of it is `2π/3`.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace OpenGA

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) 1 M] [SigmaCompactSpace M]

/-- **Math.** The unit ball around `x` for the Riemannian distance of `g`. -/
def riemannianUnitBall (g : SmoothRiemannianMetric (𝓡 3) M) (x : M) : Set M :=
  {y : M | riemannianEDistOf (I := 𝓡 3) g x y < 1}

/-- **Math.** Kleiner-Lott, Definition 77.1: a compact Riemannian three-manifold is
*normalized* if `|Rm| ≤ 1` everywhere and every unit ball has volume at least half the
volume `4π/3` of the Euclidean unit ball. -/
def IsNormalizedMetric (g : SmoothRiemannianMetric (𝓡 3) M) : Prop :=
  (∀ x : M, normSq0S (I := 𝓡 3) g x 4 (metricRm04 (I := 𝓡 3) g x) ≤ 1) ∧
    (∀ x : M, ENNReal.ofReal (2 * Real.pi / 3) ≤
      riemannianVolumeMeasure (𝓡 3) M g (riemannianUnitBall g x))

end OpenGA
