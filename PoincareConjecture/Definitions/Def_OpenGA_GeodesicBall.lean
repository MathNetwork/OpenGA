/-
Reuses qinz1yang/differential-geometry, Copyright 2026 The DifferentialGeometry
contributors, Apache-2.0, commit 1b535dd102b94cc42b107cca27059687888f08b3.
The metric and distance are upstream/Mathlib constructions. The ball interface
is curated in OpenGA; source hypotheses and mathematical definitions are preserved.
-/
import Definitions.Def_DifferentialGeometry_RiemannianDistance

noncomputable section
set_option autoImplicit false

open Bundle Set DifferentialGeometry
open scoped Manifold ContDiff ENNReal

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

end Riemannian.RiemannianMetric
