import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FromZeroManifoldOrbit
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

open Set Function Filter Metric Bundle
open scoped Topology NNReal ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] in
set_option backward.isDefEq.respectTransparency false in

private theorem bareVel_to_chartDeriv
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (γ : ℝ → M) (s : Set ℝ) (t : ℝ)
    (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) :
    HasDerivWithinAt ((extChartAt I α) ∘ γ)
      (tangentCoordChange I (γ t) α (γ t) (X t (γ t))) s t := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) hd
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in

private theorem orbit_confine_source_ball (α : M) {a : ℝ} (ha : 0 < a) (γ : ℝ → M)
    (hγ0 : γ 0 = α)
    (hcw : ContinuousWithinAt γ (Set.Ici (0:ℝ)) 0) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ t ∈ Set.Icc (0:ℝ) δ',
      γ t ∈ (extChartAt I α).source ∧
        extChartAt I α (γ t) ∈ Metric.ball (extChartAt I α α) a := by
  set x₀ : E := extChartAt I α α with hx₀
  set U : Set M := (extChartAt I α).source ∩ (extChartAt I α) ⁻¹' (Metric.ball x₀ a) with hU
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt α).isOpen_inter_preimage
      (isOpen_extChartAt_source α) Metric.isOpen_ball
  have hα_U : α ∈ U := ⟨mem_extChartAt_source α, by
    rw [Set.mem_preimage, ← hx₀]; exact Metric.mem_ball_self ha⟩
  have hpre : γ ⁻¹' U ∈ 𝓝[Set.Ici (0:ℝ)] 0 := by
    apply hcw.preimage_mem_nhdsWithin
    rw [hγ0]; exact hU_open.mem_nhds hα_U
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
  obtain ⟨W, hW_nhds, hW_sub⟩ := hpre
  rw [Metric.mem_nhds_iff] at hW_nhds
  obtain ⟨ε, hε, hε_sub⟩ := hW_nhds
  refine ⟨ε/2, by linarith, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2]
  have hmem : γ t ∈ U := hW_sub ⟨hε_sub htball, ht.1⟩
  exact ⟨hmem.1, hmem.2⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
private theorem weak_datum_uniqueness_core
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    {a : ℝ≥0} {δ₀ : ℝ} {K : ℝ≥0} (ha_pos : 0 < (a:ℝ)) (hδ₀_pos : 0 < δ₀)
    (hlipdat : ∀ t ∈ Set.Icc (0 : ℝ) δ₀,
      LipschitzOnWith K (fromZeroChartField (I := I) X α t)
        (Metric.closedBall (extChartAt I α α) a))
    (γ₁ γ₂ : ℝ → M) {δ : ℝ} (hδ : 0 < δ)
    (hstart : γ₁ 0 = α) (hstart2 : γ₂ 0 = α)
    (hflow₁ : ∀ t ∈ Set.Ico (0:ℝ) δ,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ₁ (Set.Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ₁ t))))
    (hflow₂ : ∀ t ∈ Set.Ico (0:ℝ) δ,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ₂ (Set.Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ₂ t)))) :
    ∃ δ' : ℝ, 0 < δ' ∧ Set.EqOn γ₁ γ₂ (Set.Icc 0 δ') := by
  classical
  set x₀ : E := extChartAt I α α with hx₀
  set f₁ : ℝ → E := fun u => extChartAt I α (γ₁ u) with hf₁
  set f₂ : ℝ → E := fun u => extChartAt I α (γ₂ u) with hf₂
  have hinit₁ : f₁ 0 = x₀ := by rw [hf₁]; simp only; rw [hstart]
  have hinit₂ : f₂ 0 = x₀ := by rw [hf₂]; simp only; rw [hstart2]
  have h0ico : (0:ℝ) ∈ Set.Ico (0:ℝ) δ := ⟨le_refl _, hδ⟩
  have hcw₁ : ContinuousWithinAt γ₁ (Set.Ici (0:ℝ)) 0 := (hflow₁ 0 h0ico).1
  have hcw₂ : ContinuousWithinAt γ₂ (Set.Ici (0:ℝ)) 0 := (hflow₂ 0 h0ico).1
  obtain ⟨δ'₁, hδ'₁_pos, hconf₁⟩ := orbit_confine_source_ball (I := I) α ha_pos γ₁ hstart hcw₁
  obtain ⟨δ'₂, hδ'₂_pos, hconf₂⟩ := orbit_confine_source_ball (I := I) α ha_pos γ₂ hstart2 hcw₂
  set δ' : ℝ := min (min δ'₁ δ'₂) (min (δ/2) δ₀) with hδ'def
  have hδ'_pos : 0 < δ' := lt_min (lt_min hδ'₁_pos hδ'₂_pos) (lt_min (by linarith) hδ₀_pos)
  have hδ'_le1 : δ' ≤ δ'₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ'_le2 : δ' ≤ δ'₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ'_lt_δ : δ' < δ :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hδ'_le_δ₀ : δ' ≤ δ₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hc₁ : ∀ t ∈ Set.Icc (0:ℝ) δ', γ₁ t ∈ (extChartAt I α).source ∧
      f₁ t ∈ Metric.ball x₀ (a:ℝ) :=
    fun t ht => hconf₁ t ⟨ht.1, le_trans ht.2 hδ'_le1⟩
  have hc₂ : ∀ t ∈ Set.Icc (0:ℝ) δ', γ₂ t ∈ (extChartAt I α).source ∧
      f₂ t ∈ Metric.ball x₀ (a:ℝ) :=
    fun t ht => hconf₂ t ⟨ht.1, le_trans ht.2 hδ'_le2⟩
  refine ⟨δ', hδ'_pos, ?_⟩
  have hf₁cont : ContinuousOn f₁ (Set.Icc (0:ℝ) δ') := by
    intro t ht
    have hsrc : γ₁ t ∈ (extChartAt I α).source := (hc₁ t ht).1
    have hcw : ContinuousWithinAt γ₁ (Set.Icc (0:ℝ) δ') t :=
      ((hflow₁ t ⟨ht.1, lt_of_le_of_lt ht.2 hδ'_lt_δ⟩).1).mono (fun u hu => hu.1)
    exact (continuousAt_extChartAt' hsrc).comp_continuousWithinAt hcw
  have hf₂cont : ContinuousOn f₂ (Set.Icc (0:ℝ) δ') := by
    intro t ht
    have hsrc : γ₂ t ∈ (extChartAt I α).source := (hc₂ t ht).1
    have hcw : ContinuousWithinAt γ₂ (Set.Icc (0:ℝ) δ') t :=
      ((hflow₂ t ⟨ht.1, lt_of_le_of_lt ht.2 hδ'_lt_δ⟩).1).mono (fun u hu => hu.1)
    exact (continuousAt_extChartAt' hsrc).comp_continuousWithinAt hcw
  have hvelid : ∀ (γ : ℝ → M) (t : ℝ), γ t ∈ (extChartAt I α).source →
      tangentCoordChange I (γ t) α (γ t) (X t (γ t))
        = fromZeroChartField (I := I) X α t (extChartAt I α (γ t)) := by
    intro γ t hsrc
    rw [fromZeroChartField_eq_tangentCoordChange, (extChartAt I α).left_inv hsrc]
  have hf₁deriv : ∀ t ∈ Set.Ico (0:ℝ) δ',
      HasDerivWithinAt f₁ (fromZeroChartField (I := I) X α t (f₁ t)) (Set.Ici t) t := by
    intro t ht
    have hsrc' : γ₁ t ∈ (extChartAt I α).source := (hc₁ t ⟨ht.1, le_of_lt ht.2⟩).1
    have hsrcch : γ₁ t ∈ (chartAt H α).source := by rwa [extChartAt_source] at hsrc'
    have hbridge := bareVel_to_chartDeriv (I := I) X α γ₁ (Set.Ici 0) t hsrcch
      (hflow₁ t ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt hδ'_lt_δ)⟩)
    have hbridge' : HasDerivWithinAt f₁ (tangentCoordChange I (γ₁ t) α (γ₁ t) (X t (γ₁ t)))
        (Set.Ici t) t := hbridge.mono (fun u hu => le_trans ht.1 hu)
    rwa [hvelid γ₁ t hsrc'] at hbridge'
  have hf₂deriv : ∀ t ∈ Set.Ico (0:ℝ) δ',
      HasDerivWithinAt f₂ (fromZeroChartField (I := I) X α t (f₂ t)) (Set.Ici t) t := by
    intro t ht
    have hsrc' : γ₂ t ∈ (extChartAt I α).source := (hc₂ t ⟨ht.1, le_of_lt ht.2⟩).1
    have hsrcch : γ₂ t ∈ (chartAt H α).source := by rwa [extChartAt_source] at hsrc'
    have hbridge := bareVel_to_chartDeriv (I := I) X α γ₂ (Set.Ici 0) t hsrcch
      (hflow₂ t ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt hδ'_lt_δ)⟩)
    have hbridge' : HasDerivWithinAt f₂ (tangentCoordChange I (γ₂ t) α (γ₂ t) (X t (γ₂ t)))
        (Set.Ici t) t := hbridge.mono (fun u hu => le_trans ht.1 hu)
    rwa [hvelid γ₂ t hsrc'] at hbridge'
  have hlip' : ∀ t ∈ Set.Ico (0:ℝ) δ',
      LipschitzOnWith K (fromZeroChartField (I := I) X α t) (Metric.closedBall x₀ (a:ℝ)) :=
    fun t ht => hlipdat t ⟨ht.1, le_trans (le_of_lt ht.2) hδ'_le_δ₀⟩
  have hmem₁ : ∀ t ∈ Set.Ico (0:ℝ) δ', f₁ t ∈ Metric.closedBall x₀ (a:ℝ) :=
    fun t ht => Metric.ball_subset_closedBall (hc₁ t ⟨ht.1, le_of_lt ht.2⟩).2
  have hmem₂ : ∀ t ∈ Set.Ico (0:ℝ) δ', f₂ t ∈ Metric.closedBall x₀ (a:ℝ) :=
    fun t ht => Metric.ball_subset_closedBall (hc₂ t ⟨ht.1, le_of_lt ht.2⟩).2
  have hdist := DifferentialGeometry.Analysis.ODE.forward_orbit_dist_le (E := E)
    (f := fromZeroChartField (I := I) X α) (γ₁ := f₁) (γ₂ := f₂)
    (S := Metric.closedBall x₀ (a:ℝ)) (K := K) (δ := δ')
    hlip' hf₁cont hf₁deriv hmem₁ hf₂cont hf₂deriv hmem₂
  intro t ht
  have hd := hdist t ht
  have hinit_dist : dist (f₁ 0) (f₂ 0) = 0 := by rw [hinit₁, hinit₂, dist_self]
  rw [hinit_dist, zero_mul] at hd
  have hfeq : f₁ t = f₂ t := dist_le_zero.mp hd
  have hsrc₁ : γ₁ t ∈ (extChartAt I α).source := (hc₁ t ht).1
  have hsrc₂ : γ₂ t ∈ (extChartAt I α).source := (hc₂ t ht).1
  have hpb : (extChartAt I α).symm (f₁ t) = (extChartAt I α).symm (f₂ t) := by rw [hfeq]
  rwa [hf₁, hf₂, (extChartAt I α).left_inv hsrc₁, (extChartAt I α).left_inv hsrc₂] at hpb

end DifferentialGeometry.PDE.RicciFlow.ODE
