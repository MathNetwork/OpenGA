import OpenGALib.ComparisonGeometry.MetricBall
import OpenGALib.ComparisonGeometry.VolumeMeasure

/-!
# Volumes of Riemannian balls

All volumes and distances are computed with the same explicit metric.
Compact closure of a ball suffices for finite volume, even without a complete
ambient manifold. This is the finiteness hypothesis needed in the local
Bishop-Gromov formulation used by the Poincare mission.

Reference: Xinze Li, *Lecture Notes on Comparison Geometry*,
https://arxiv.org/abs/2404.09792v2, Chapter 11. The complete-manifold comparison
is proved in that chapter; the elementary local measure statements here also
apply to incomplete manifolds.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Math.** The Riemannian volume of a geodesic ball for the same metric. -/
def ballVolume (g : RiemannianMetric I M) (p : M) (r : ℝ) : ℝ≥0∞ :=
  g.volumeMeasure (g.geodesicBall p r)

/-- **Math.** Ball volume is nondecreasing in the radius. -/
theorem ballVolume_mono (g : RiemannianMetric I M) (p : M) :
    Monotone (g.ballVolume p) := by
  intro r R hrR
  exact measure_mono (g.geodesicBall_mono p hrR)

/-- **Math.** Nonpositive-radius balls have zero volume. -/
theorem ballVolume_eq_zero (g : RiemannianMetric I M) (p : M)
    {r : ℝ} (hr : r ≤ 0) : g.ballVolume p r = 0 := by
  simp [ballVolume, g.geodesicBall_eq_empty p hr]

/-- **Math.** Every positive-radius ball has positive volume, without completeness
or a curvature assumption. -/
theorem ballVolume_pos (g : RiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r) :
    0 < g.ballVolume p r := by
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  exact (g.isOpen_geodesicBall p r).measure_pos g.volumeMeasure (g.geodesicBall_nonempty p hr)

/-- **Math.** A ball has positive volume exactly when its radius is positive. -/
@[simp] theorem ballVolume_pos_iff (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    0 < g.ballVolume p r ↔ 0 < r := by
  constructor
  · intro h
    by_contra hr
    rw [g.ballVolume_eq_zero p (le_of_not_gt hr)] at h
    exact (lt_irrefl _ h)
  · exact g.ballVolume_pos p

/-- **Math.** A ball with compact closure has finite volume; no completeness is needed. -/
theorem ballVolume_lt_top_of_isCompact_closure (g : RiemannianMetric I M)
    (p : M) {r : ℝ} (hc : IsCompact (closure (g.geodesicBall p r))) :
    g.ballVolume p r < ⊤ := by
  let : IsFiniteMeasureOnCompacts g.volumeMeasure := g.volumeMeasure_isFiniteMeasureOnCompacts
  exact lt_of_le_of_lt (measure_mono subset_closure) (hc.measure_lt_top (μ := g.volumeMeasure))

/-- **Math.** All smaller concentric balls have finite volume if the outer ball
has compact closure. -/
theorem ballVolume_lt_top_of_le_of_isCompact_closure (g : RiemannianMetric I M)
    (p : M) {r R : ℝ} (hrR : r ≤ R)
    (hc : IsCompact (closure (g.geodesicBall p R))) : g.ballVolume p r < ⊤ :=
  lt_of_le_of_lt (g.ballVolume_mono p hrR) (g.ballVolume_lt_top_of_isCompact_closure p hc)

end Riemannian.RiemannianMetric
