import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentContinuousRiemannianMetric
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] in
private lemma exists_W_and_constant_tangent
    (g : SmoothRiemannianMetric I M)
    (α y₀ : M)
    (h_y₀_α : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ W : Set M, IsOpen W ∧ y₀ ∈ W ∧ ∃ N : ℝ, 0 < N ∧ ∀ b ∈ W,
      ‖(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b‖ ≤ N := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  obtain ⟨C₁, hC₁_pos, hC₁_ev⟩ :=
    eventually_norm_trivializationAt_lt E (fun b : M => TangentSpace I b) y₀
  set ccF : M → (E →L[ℝ] E) := fun b =>
    (trivializationAt E (TangentSpace I) y₀).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) α) b with hccF_def
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ ccF
        ((trivializationAt E (TangentSpace I) y₀).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
      (F := E)
      (E := fun y : M => TangentSpace I y)
      (trivializationAt E (TangentSpace I) y₀)
      (trivializationAt E (TangentSpace I) α)
  have hy₀_y₀ : y₀ ∈ (trivializationAt E (TangentSpace I) y₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' y₀
  have hy₀_inter :
      y₀ ∈ (trivializationAt E (TangentSpace I) y₀).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ⟨hy₀_y₀, h_y₀_α⟩
  have h_cont : ContinuousOn ccF
      ((trivializationAt E (TangentSpace I) y₀).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet) :=
    h_smooth.continuousOn
  have h_open_inter :
      IsOpen ((trivializationAt E (TangentSpace I) y₀).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet) :=
    (trivializationAt E (TangentSpace I) y₀).open_baseSet.inter
      (trivializationAt E (TangentSpace I) α).open_baseSet
  have h_cc_continuousAt : ContinuousAt ccF y₀ :=
    h_cont.continuousAt (h_open_inter.mem_nhds hy₀_inter)
  have h_norm_continuousAt : ContinuousAt (fun b => ‖ccF b‖) y₀ :=
    continuous_norm.continuousAt.comp h_cc_continuousAt
  set C₂ : ℝ := ‖ccF y₀‖ + 1 with hC₂_def
  have hC₂_pos : 0 < C₂ := by rw [hC₂_def]; positivity
  have h_cc_ev : ∀ᶠ b in 𝓝 y₀, ‖ccF b‖ < C₂ := by
    exact h_norm_continuousAt (Iio_mem_nhds (by rw [hC₂_def]; linarith))
  rcases (Filter.eventually_iff_exists_mem.mp hC₁_ev) with ⟨U₁, hU₁_nhd, hU₁_bound⟩
  rcases mem_nhds_iff.mp hU₁_nhd with ⟨V₁, hV₁_sub, hV₁_open, hV₁_mem⟩
  rcases (Filter.eventually_iff_exists_mem.mp h_cc_ev) with ⟨U₂, hU₂_nhd, hU₂_bound⟩
  rcases mem_nhds_iff.mp hU₂_nhd with ⟨V₂, hV₂_sub, hV₂_open, hV₂_mem⟩
  refine ⟨V₁ ∩ V₂ ∩ (trivializationAt E (TangentSpace I) y₀).baseSet ∩
    (trivializationAt E (TangentSpace I) α).baseSet,
    ((hV₁_open.inter hV₂_open).inter
      (trivializationAt E (TangentSpace I) y₀).open_baseSet).inter
      (trivializationAt E (TangentSpace I) α).open_baseSet,
    ⟨⟨⟨hV₁_mem, hV₂_mem⟩, hy₀_y₀⟩, h_y₀_α⟩, ?_⟩
  refine ⟨C₂ * C₁, by positivity, ?_⟩
  intro b hb
  obtain ⟨⟨⟨hb_V₁, hb_V₂⟩, hb_y₀⟩, hb_α⟩ := hb
  have h_clm_norm_le :
      ‖(trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ b‖ ≤ C₁ :=
    le_of_lt (hU₁_bound b (hV₁_sub hb_V₁))
  have h_cc_norm_le : ‖ccF b‖ ≤ C₂ :=
    le_of_lt (hU₂_bound b (hV₂_sub hb_V₂))
  set ey₀ := trivializationAt E (TangentSpace I) y₀ with hey₀_def
  set eα := trivializationAt E (TangentSpace I) α with heα_def
  have hboth : b ∈ ey₀.baseSet ∩ eα.baseSet := ⟨hb_y₀, hb_α⟩
  have h_cc_apply_eq (T : TangentSpace I b) :
      (ey₀.coordChangeL ℝ eα b : E →L[ℝ] E) (ey₀.continuousLinearMapAt ℝ b T) =
      eα.continuousLinearMapAt ℝ b
        (ey₀.symmL ℝ b (ey₀.continuousLinearMapAt ℝ b T)) := by
    change (ey₀.coordChangeL ℝ eα b) (ey₀.continuousLinearMapAt ℝ b T) = _
    rw [Trivialization.coordChangeL_apply _ _ hboth]
    simp only [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_y₀,
        Bundle.Trivialization.symmL_apply]
  have h_inv (T : TangentSpace I b) :
      ey₀.symmL ℝ b (ey₀.continuousLinearMapAt ℝ b T) = T :=
    Trivialization.symmL_continuousLinearMapAt (R := ℝ) ey₀ hb_y₀ T
  have h_pointwise (T : TangentSpace I b) :
      eα.continuousLinearMapAt ℝ b T =
      (ey₀.coordChangeL ℝ eα b : E →L[ℝ] E) (ey₀.continuousLinearMapAt ℝ b T) := by
    rw [h_cc_apply_eq, h_inv]
  have h_norm_T (T : TangentSpace I b) :
      ‖eα.continuousLinearMapAt ℝ b T‖ ≤ C₂ * C₁ * ‖T‖ := by
    rw [h_pointwise T]
    calc ‖(ey₀.coordChangeL ℝ eα b : E →L[ℝ] E) (ey₀.continuousLinearMapAt ℝ b T)‖
        ≤ ‖(ey₀.coordChangeL ℝ eα b : E →L[ℝ] E)‖ *
            ‖ey₀.continuousLinearMapAt ℝ b T‖ :=
          (ey₀.coordChangeL ℝ eα b : E →L[ℝ] E).le_opNorm _
      _ ≤ C₂ * (C₁ * ‖T‖) := by
          have h1 : ‖ey₀.continuousLinearMapAt ℝ b T‖ ≤ C₁ * ‖T‖ :=
            ((ey₀.continuousLinearMapAt ℝ b).le_opNorm T).trans
              (mul_le_mul_of_nonneg_right h_clm_norm_le (norm_nonneg _))
          exact mul_le_mul h_cc_norm_le h1 (norm_nonneg _) (le_of_lt hC₂_pos)
      _ = C₂ * C₁ * ‖T‖ := by ring
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h_norm_T

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] in
theorem chartTriv_opNorm_isBounded_on_compact_unconditional
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) {K : Set M} (hK : IsCompact K)
    (hK_base : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K,
      ‖(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b‖ ≤ C := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  let W : M → Set M := fun y₀ =>
    if hy : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (exists_W_and_constant_tangent (I := I) (M := M) g α y₀ hy).choose
    else ∅
  have hW_open : ∀ y₀, IsOpen (W y₀) := by
    intro y₀; simp only [W]
    split_ifs with hy
    · exact (exists_W_and_constant_tangent (I := I) (M := M) g α y₀ hy).choose_spec.1
    · exact isOpen_empty
  have hW_mem : ∀ y₀, y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet → y₀ ∈ W y₀ := by
    intro y₀ hy; simp only [W, dif_pos hy]
    exact (exists_W_and_constant_tangent (I := I) (M := M) g α y₀ hy).choose_spec.2.1
  let N : M → ℝ := fun y₀ =>
    if hy : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (exists_W_and_constant_tangent (I := I) (M := M) g α y₀ hy).choose_spec.2.2.choose
    else 1
  have hN_pos : ∀ y₀, 0 < N y₀ := by
    intro y₀; simp only [N]
    split_ifs with hy
    · exact (exists_W_and_constant_tangent (I := I) (M := M) g α y₀ hy).choose_spec.2.2.choose_spec.1
    · exact one_pos
  have hN_bound : ∀ y₀, y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ b ∈ W y₀,
      ‖(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b‖ ≤ N y₀ := by
    intro y₀ hy b hb
    simp only [W, dif_pos hy] at hb
    simp only [N, dif_pos hy]
    exact (exists_W_and_constant_tangent (I := I) (M := M) g α y₀ hy).choose_spec.2.2.choose_spec.2
      b hb
  have h_cover : K ⊆ ⋃ y₀ ∈ K, W y₀ := fun b hb =>
    Set.mem_iUnion₂.mpr ⟨b, hb, hW_mem b (hK_base hb)⟩
  rcases hK.elim_finite_subcover_image (b := K) (c := W)
    (fun y₀ _ => hW_open y₀) h_cover with ⟨S, hS_sub, hS_finite, hS_cover⟩
  set S' : Finset M := hS_finite.toFinset with hS'_def
  have hS_cover' : K ⊆ ⋃ y₀ ∈ S', W y₀ := by
    intro b hb
    rcases Set.mem_iUnion.mp (hS_cover hb) with ⟨y₀, hy₀⟩
    rcases Set.mem_iUnion.mp hy₀ with ⟨hy₀_S, hb_in⟩
    refine Set.mem_iUnion.mpr ⟨y₀, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hb_in⟩
    rw [hS'_def]; exact hS_finite.mem_toFinset.mpr hy₀_S
  have hS_sub_K : ∀ y₀ ∈ S', y₀ ∈ K := by
    intro y₀ hy₀; rw [hS'_def] at hy₀
    exact hS_sub (hS_finite.mem_toFinset.mp hy₀)
  by_cases hS_empty : S' = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro b hb
    have : b ∈ ⋃ y₀ ∈ S', W y₀ := hS_cover' hb
    rw [hS_empty] at this; simp at this
  have hS_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set C_max : ℝ := S'.sup' hS_nonempty N with hCmax_def
  have h_C_max_pos : 0 < C_max := by
    rcases hS_nonempty with ⟨y₀, hy₀⟩
    exact (hN_pos y₀).trans_le (Finset.le_sup' (f := N) hy₀)
  refine ⟨C_max, le_of_lt h_C_max_pos, ?_⟩
  intro b hb
  rcases Set.mem_iUnion.mp (hS_cover' hb) with ⟨y₀, hy₀⟩
  rcases Set.mem_iUnion.mp hy₀ with ⟨hy₀_S, hb_in⟩
  have hy₀_base : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hK_base (hS_sub_K y₀ hy₀_S)
  have hN_b := hN_bound y₀ hy₀_base b hb_in
  have h_le_Cmax : N y₀ ≤ C_max := Finset.le_sup' (f := N) hy₀_S
  exact hN_b.trans h_le_Cmax

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock

end
