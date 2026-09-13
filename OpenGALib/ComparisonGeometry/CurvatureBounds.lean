import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import OpenGALib.ComparisonGeometry.MetricBall

/-!
# Local Ricci lower bounds

`RicciBoundedBelowOn g s k` means `Ric_g(v,v) >= k * g(v,v)` at every point
of `s`. Here `k` is the Ricci coefficient, not the model sectional curvature:
the Bishop-Gromov hypothesis for model curvature `K` uses `k = (n - 1) * K`.
Taking `s = univ` recovers the upstream predicate exactly.

Reference: Xinze Li, *Lecture Notes on Comparison Geometry*,
https://arxiv.org/abs/2404.09792v2, Chapter 11, pp. 192, 196-197.
The tensor and sign convention are reused from DifferentialGeometry v0.1.2.
-/

noncomputable section
set_option autoImplicit false

open Bundle Set DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless]

/-- **Math.** A lower bound for the Ricci quadratic form restricted to a region. -/
def RicciBoundedBelowOn (g : RiemannianMetric I M) (s : Set M) (k : ℝ) : Prop :=
  ∀ x ∈ s, ∀ v : TangentSpace I x, k * g.inner x v v ≤ ricciTensor (I := I) g x v v

/-- **Math.** A Ricci lower bound restricts to any smaller region. -/
theorem RicciBoundedBelowOn.mono (g : RiemannianMetric I M) {s t : Set M} {k : ℝ}
    (ht : g.RicciBoundedBelowOn t k) (hst : s ⊆ t) : g.RicciBoundedBelowOn s k :=
  fun x hx v => ht x (hst hx) v

/-- **Math.** Decreasing the Ricci coefficient weakens a lower bound. -/
theorem RicciBoundedBelowOn.of_le (g : RiemannianMetric I M) {s : Set M} {k K : ℝ}
    (hK : g.RicciBoundedBelowOn s K) (hkK : k ≤ K) : g.RicciBoundedBelowOn s k := by
  intro x hx v
  have hv : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · subst v
      simp
    · exact (g.pos x v hv).le
  exact (mul_le_mul_of_nonneg_right hkK hv).trans (hK x hx v)

/-- **Math.** A lower bound on a union is equivalent to the bound on both regions. -/
theorem ricciBoundedBelowOn_union (g : RiemannianMetric I M) (s t : Set M) (k : ℝ) :
    g.RicciBoundedBelowOn (s ∪ t) k ↔
      g.RicciBoundedBelowOn s k ∧ g.RicciBoundedBelowOn t k := by
  constructor
  · intro h
    exact ⟨h.mono g subset_union_left, h.mono g subset_union_right⟩
  · rintro ⟨hs, ht⟩ x (hx | hx) v
    · exact hs x hx v
    · exact ht x hx v

/-- **Math.** On the whole manifold, the local definition is the upstream global bound. -/
@[simp] theorem ricciBoundedBelowOn_univ (g : RiemannianMetric I M) (k : ℝ) :
    g.RicciBoundedBelowOn univ k ↔
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g k := by
  simp [RicciBoundedBelowOn,
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow]

/-- **Math.** A Ricci bound on an outer ball holds on each smaller concentric ball. -/
theorem RicciBoundedBelowOn.geodesicBall_mono (g : RiemannianMetric I M)
    (p : M) {r R k : ℝ} (hRic : g.RicciBoundedBelowOn (g.geodesicBall p R) k)
    (hrR : r ≤ R) : g.RicciBoundedBelowOn (g.geodesicBall p r) k :=
  hRic.mono g (g.geodesicBall_mono p hrR)

end Riemannian.RiemannianMetric
