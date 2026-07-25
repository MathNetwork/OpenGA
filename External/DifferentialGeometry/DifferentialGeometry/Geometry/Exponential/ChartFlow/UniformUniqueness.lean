import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz



noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

section LipschitzOnCompact

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPhaseVF_exists_lipschitzOnWith_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {z : E × E} (hz : z ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 z, LipschitzOnWith L (chartPhaseVF (I := I) g α) t := by
  have hC1 : ContDiffOn ℝ 1 (chartPhaseVF (I := I) g α)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    (chartPhaseVF_contDiffOn (I := I) g α).of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hopen : IsOpen ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    isOpen_interior.prod isOpen_univ
  have hC1_at : ContDiffAt ℝ 1 (chartPhaseVF (I := I) g α) z :=
    hC1.contDiffAt (hopen.mem_nhds hz)
  exact hC1_at.exists_lipschitzOnWith

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPhaseVF_locallyLipschitzOn_of_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    LocallyLipschitzOn K (chartPhaseVF (I := I) g α) := by
  intro z hz
  obtain ⟨L, t, ht, hL⟩ :=
    chartPhaseVF_exists_lipschitzOnWith_at (I := I) g α (hK_subset hz)
  refine ⟨L, t, ?_, hL⟩
  exact mem_nhdsWithin_of_mem_nhds ht

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_lipschitzOnWith_of_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ L : ℝ≥0, LipschitzOnWith L (chartPhaseVF (I := I) g α) K :=
  (chartPhaseVF_locallyLipschitzOn_of_compact (I := I) g α
    hK_subset).exists_lipschitzOnWith_of_compact hK_compact

end LipschitzOnCompact

section UniformUniqueness

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_orbit_uniqueness_uniform_Ioo
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {T : ℝ} (hT_pos : 0 < T)
    {c₁ c₂ : ℝ → E × E}
    (hc₁_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s)
    (hc₂_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s)
    (hc₁_in_K : ∀ s ∈ Set.Ioo (-T) T, c₁ s ∈ K)
    (hc₂_in_K : ∀ s ∈ Set.Ioo (-T) T, c₂ s ∈ K)
    (h_eq_at_zero : c₁ 0 = c₂ 0) :
    ∀ s ∈ Set.Ioo (-T) T, c₁ s = c₂ s := by
  obtain ⟨L, hLip⟩ :=
    chartPhaseVF_lipschitzOnWith_of_compact (I := I) g α hK_compact hK_subset
  set v : ℝ → (E × E) → E × E := fun _ z => chartPhaseVF (I := I) g α z with hv_def
  set sSet : ℝ → Set (E × E) := fun _ => K with hsSet_def
  have hv_lip : ∀ t ∈ Set.Ioo (-T) T, LipschitzOnWith L (v t) (sSet t) := by
    intro t _
    exact hLip
  have h0_in : (0 : ℝ) ∈ Set.Ioo (-T) T :=
    ⟨by linarith, hT_pos⟩
  have hf : ∀ t ∈ Set.Ioo (-T) T,
      HasDerivAt c₁ (v t (c₁ t)) t ∧ c₁ t ∈ sSet t := by
    intro t ht
    exact ⟨hc₁_hasDeriv t ht, hc₁_in_K t ht⟩
  have hg : ∀ t ∈ Set.Ioo (-T) T,
      HasDerivAt c₂ (v t (c₂ t)) t ∧ c₂ t ∈ sSet t := by
    intro t ht
    exact ⟨hc₂_hasDeriv t ht, hc₂_in_K t ht⟩
  have hEqOn : Set.EqOn c₁ c₂ (Set.Ioo (-T) T) :=
    ODE_solution_unique_of_mem_Ioo (v := v) (s := sSet) (K := L) (t₀ := 0)
      (a := -T) (b := T) hv_lip h0_in hf hg h_eq_at_zero
  intro s hs
  exact hEqOn hs

end UniformUniqueness

section UniformAgainstFlow

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_solution_eq_chartFlowOrbit_on_Ioo
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {T : ℝ} (hT_pos : 0 < T)
    {c : ℝ → E × E} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E}
    (hc_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c (chartPhaseVF (I := I) g α (c s)) s)
    (hΦ_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun τ => Φ (z₀, τ))
        (chartPhaseVF (I := I) g α (Φ (z₀, s))) s)
    (hc_in_K : ∀ s ∈ Set.Ioo (-T) T, c s ∈ K)
    (hΦ_in_K : ∀ s ∈ Set.Ioo (-T) T, Φ (z₀, s) ∈ K)
    (h_eq_at_zero : c 0 = Φ (z₀, 0)) :
    ∀ s ∈ Set.Ioo (-T) T, c s = Φ (z₀, s) := by
  exact chartPhaseVF_orbit_uniqueness_uniform_Ioo (I := I) g α
    hK_compact hK_subset hT_pos
    (c₁ := c) (c₂ := fun τ => Φ (z₀, τ))
    hc_hasDeriv hΦ_hasDeriv hc_in_K hΦ_in_K h_eq_at_zero

end UniformAgainstFlow

section UniformOnClosedBall

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_orbit_uniqueness_uniform_Ioo_closedBall
    (g : SmoothRiemannianMetric I M) (α : M)
    {z₀ : E × E} {r : ℝ}
    (hr_subset : Metric.closedBall z₀ r ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {T : ℝ} (hT_pos : 0 < T)
    {c₁ c₂ : ℝ → E × E}
    (hc₁_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s)
    (hc₂_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s)
    (hc₁_in_ball : ∀ s ∈ Set.Ioo (-T) T, c₁ s ∈ Metric.closedBall z₀ r)
    (hc₂_in_ball : ∀ s ∈ Set.Ioo (-T) T, c₂ s ∈ Metric.closedBall z₀ r)
    (h_eq_at_zero : c₁ 0 = c₂ 0) :
    ∀ s ∈ Set.Ioo (-T) T, c₁ s = c₂ s :=
  chartPhaseVF_orbit_uniqueness_uniform_Ioo (I := I) g α
    (K := Metric.closedBall z₀ r)
    (isCompact_closedBall _ _) hr_subset hT_pos
    hc₁_hasDeriv hc₂_hasDeriv hc₁_in_ball hc₂_in_ball h_eq_at_zero

end UniformOnClosedBall

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
