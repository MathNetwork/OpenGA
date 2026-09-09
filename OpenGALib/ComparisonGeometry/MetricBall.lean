import DifferentialGeometry.Geometry.Metric.DistanceScaling
import Mathlib.Geometry.Manifold.Metrizable
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Balls for an explicit Riemannian metric

The distance is the infimum of path lengths computed with the specified metric.
It may be infinite between components. No completeness or curvature assumption
is needed for the elementary ball properties below.

We reuse DifferentialGeometry's `riemannianEDistOf`; the existing OpenGA name
`Riemannian.RiemannianMetric.geodesicBall` is preserved.
Reference: Xinze Li, *Lecture Notes on Comparison Geometry*,
https://arxiv.org/abs/2404.09792v2, Chapter 11, pp. 191-199.
-/

noncomputable section
set_option autoImplicit false

open Bundle Set DifferentialGeometry
open scoped Manifold ContDiff ENNReal

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** The open ball for the distance induced by the specified metric. -/
def geodesicBall (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  {x | riemannianEDistOf (I := I) g p x < ENNReal.ofReal r}

/-- **Math.** Membership in a metric ball is the strict distance inequality. -/
@[simp] theorem mem_geodesicBall (g : RiemannianMetric I M) (p x : M) (r : ℝ) :
    x ∈ g.geodesicBall p r ↔ riemannianEDistOf (I := I) g p x < ENNReal.ofReal r :=
  Iff.rfl

/-- **Math.** A ball of nonpositive radius is empty. -/
theorem geodesicBall_eq_empty (g : RiemannianMetric I M) (p : M)
    {r : ℝ} (hr : r ≤ 0) : g.geodesicBall p r = ∅ := by
  ext x
  simp [geodesicBall, ENNReal.ofReal_of_nonpos hr]

/-- **Math.** Increasing the radius increases the ball. -/
theorem geodesicBall_mono (g : RiemannianMetric I M) (p : M) :
    Monotone (g.geodesicBall p) := by
  intro r R hrR x hx
  exact lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrR)

/-- **Math.** The center lies in precisely the positive-radius balls. -/
@[simp] theorem self_mem_geodesicBall (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    p ∈ g.geodesicBall p r ↔ 0 < r := by
  simp [geodesicBall, riemannianEDistOf_self]

/-- **Math.** A positive-radius ball is nonempty. -/
theorem geodesicBall_nonempty (g : RiemannianMetric I M) (p : M)
    {r : ℝ} (hr : 0 < r) : (g.geodesicBall p r).Nonempty :=
  ⟨p, (g.self_mem_geodesicBall p r).mpr hr⟩

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** Balls for the Riemannian distance are open in the manifold topology. -/
theorem isOpen_geodesicBall [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    IsOpen (g.geodesicBall p r) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  change IsOpen {x | edist p x < ENNReal.ofReal r}
  simpa only [Metric.eball, edist_comm] using
    (Metric.isOpen_eball : IsOpen (Metric.eball p (ENNReal.ofReal r)))

/-- **Math.** Enlarging the metric as a quadratic form shrinks each ball. -/
theorem geodesicBall_subset_of_metric_le (g h : RiemannianMetric I M)
    (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v) (p : M) (r : ℝ) :
    h.geodesicBall p r ⊆ g.geodesicBall p r := by
  intro x hx
  exact lt_of_le_of_lt (edistOf_mono g h hgh p x) hx

end Riemannian.RiemannianMetric
