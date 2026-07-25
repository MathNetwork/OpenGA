import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Tensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_W_and_constant_symmL
    (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α y₀ : M) (h_y₀_α : y₀ ∈ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ W : Set M, IsOpen W ∧ y₀ ∈ W ∧ ∃ N : ℝ, 0 < N ∧ ∀ b ∈ W,
      ∀ v : TensorRSModel r s ℝ E,
        ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
            TensorRSSpace r s I b)‖ ≤ N * ‖v‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  haveI hICRB : IsContinuousRiemannianBundle (TensorRSModel r s ℝ E)
      (fun b : M => TensorRSSpace r s I b) :=
    tensorRS_isContinuousRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨C₁, hC₁_pos, hC₁_ev⟩ :=
    eventually_norm_symmL_trivializationAt_lt (TensorRSModel r s ℝ E)
      (fun b : M => TensorRSSpace r s I b) y₀
  set ccF : M → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) := fun b =>
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) y₀) b with hccF_def
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∞ ccF
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet ∩
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) y₀).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
      (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) y₀)
  have h_base_y₀ :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) y₀).baseSet =
      (chartAt H y₀).source := by
    change (trivializationAt E (TangentSpace I) y₀).baseSet ∩
        (trivializationAt E (TangentSpace I) y₀).baseSet = (chartAt H y₀).source
    rw [Set.inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) y₀]
  have h_base_α :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
  have hy₀_y₀ : y₀ ∈ (chartAt H y₀).source := mem_chart_source H y₀
  have hy₀_inter :
      y₀ ∈ (chartAt H α).source ∩ (chartAt H y₀).source := ⟨h_y₀_α, hy₀_y₀⟩
  have h_smooth_chart :
      ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∞ ccF
        ((chartAt H α).source ∩ (chartAt H y₀).source) := by
    rw [show (chartAt H α).source ∩ (chartAt H y₀).source =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet ∩
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) y₀).baseSet from by
        rw [h_base_y₀, h_base_α]]
    exact h_smooth
  have h_cont_chart : ContinuousOn ccF
      ((chartAt H α).source ∩ (chartAt H y₀).source) := h_smooth_chart.continuousOn
  have h_open_inter :
      IsOpen ((chartAt H α).source ∩ (chartAt H y₀).source) :=
    (chartAt H α).open_source.inter (chartAt H y₀).open_source
  have h_cc_continuousAt : ContinuousAt ccF y₀ :=
    h_cont_chart.continuousAt (h_open_inter.mem_nhds hy₀_inter)
  have h_norm_continuousAt : ContinuousAt (fun b => ‖ccF b‖) y₀ :=
    continuous_norm.continuousAt.comp h_cc_continuousAt
  set C₂ : ℝ := ‖ccF y₀‖ + 1 with hC₂_def
  have hC₂_pos : 0 < C₂ := by
    rw [hC₂_def]; positivity
  have h_cc_ev : ∀ᶠ b in 𝓝 y₀, ‖ccF b‖ < C₂ := by
    have h_lt : ‖ccF y₀‖ < C₂ := by rw [hC₂_def]; linarith
    have h_mem_nhds : Set.Iio C₂ ∈ 𝓝 ‖ccF y₀‖ := Iio_mem_nhds h_lt
    exact h_norm_continuousAt h_mem_nhds
  rcases (Filter.eventually_iff_exists_mem.mp hC₁_ev) with ⟨U₁, hU₁_nhd, hU₁_bound⟩
  rcases mem_nhds_iff.mp hU₁_nhd with ⟨V₁, hV₁_sub, hV₁_open, hV₁_mem⟩
  rcases (Filter.eventually_iff_exists_mem.mp h_cc_ev) with ⟨U₂, hU₂_nhd, hU₂_bound⟩
  rcases mem_nhds_iff.mp hU₂_nhd with ⟨V₂, hV₂_sub, hV₂_open, hV₂_mem⟩
  refine ⟨V₁ ∩ V₂ ∩ (chartAt H y₀).source ∩ (chartAt H α).source,
    ((hV₁_open.inter hV₂_open).inter (chartAt H y₀).open_source).inter
      (chartAt H α).open_source,
    ⟨⟨⟨hV₁_mem, hV₂_mem⟩, hy₀_y₀⟩, h_y₀_α⟩, ?_⟩
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro b hb v
  obtain ⟨⟨⟨hb_V₁, hb_V₂⟩, hb_y₀_src⟩, hb_α_src⟩ := hb
  have h_symmL_norm_lt : ‖(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) y₀).symmL ℝ b‖ < C₁ :=
    hU₁_bound b (hV₁_sub hb_V₁)
  have h_symmL_norm_le : ‖(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) y₀).symmL ℝ b‖ ≤ C₁ :=
    le_of_lt h_symmL_norm_lt
  have h_cc_norm_lt : ‖ccF b‖ < C₂ := hU₂_bound b (hV₂_sub hb_V₂)
  have h_cc_norm_le : ‖ccF b‖ ≤ C₂ := le_of_lt h_cc_norm_lt
  have hb_tan_y₀ : b ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) y₀]; exact hb_y₀_src
  have hb_tan_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hb_α_src
  have hb_y₀_RS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) y₀).baseSet := ⟨hb_tan_y₀, hb_tan_y₀⟩
  have hb_α_RS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hb_tan_α, hb_tan_α⟩
  set ey₀ := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) y₀ with hey₀_def
  set eα := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heα_def
  have h_cc_eq_clmAt_symmL :
      (eα.coordChangeL ℝ ey₀ b
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) v =
      ey₀.continuousLinearMapAt ℝ b (eα.symmL ℝ b v) := by
    change (eα.coordChangeL ℝ ey₀ b) v =
        ey₀.continuousLinearMapAt ℝ b (eα.symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_α_RS, hb_y₀_RS⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_y₀_RS,
        Bundle.Trivialization.symmL_apply]
  have h_symmL_clmAt :
      ey₀.symmL ℝ b (ey₀.continuousLinearMapAt ℝ b (eα.symmL ℝ b v)) =
      eα.symmL ℝ b v :=
    Trivialization.symmL_continuousLinearMapAt (R := ℝ) ey₀ hb_y₀_RS (eα.symmL ℝ b v)
  have h_factor :
      (eα.symmL ℝ b v : TensorRSSpace r s I b) =
      ey₀.symmL ℝ b ((eα.coordChangeL ℝ ey₀ b
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) v) := by
    rw [h_cc_eq_clmAt_symmL, h_symmL_clmAt]
  have h_norm_cc_v :
      ‖(eα.coordChangeL ℝ ey₀ b
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) v‖ ≤ C₂ * ‖v‖ := by
    have := (eα.coordChangeL ℝ ey₀ b
        : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E).le_opNorm v
    have h_ccF_eq : ‖ccF b‖ =
        ‖(eα.coordChangeL ℝ ey₀ b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)‖ := rfl
    rw [h_ccF_eq] at h_cc_norm_le
    exact this.trans (mul_le_mul_of_nonneg_right h_cc_norm_le (norm_nonneg _))
  have h_norm_total :
      ‖(eα.symmL ℝ b v : TensorRSSpace r s I b)‖ ≤
        ‖ey₀.symmL ℝ b‖ *
        ‖(eα.coordChangeL ℝ ey₀ b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) v‖ := by
    rw [h_factor]
    exact ContinuousLinearMap.le_opNorm (ey₀.symmL ℝ b) _
  calc ‖(eα.symmL ℝ b v : TensorRSSpace r s I b)‖
      ≤ ‖ey₀.symmL ℝ b‖ *
          ‖(eα.coordChangeL ℝ ey₀ b
              : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) v‖ := h_norm_total
    _ ≤ C₁ *
          ‖(eα.coordChangeL ℝ ey₀ b
              : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) v‖ :=
        mul_le_mul_of_nonneg_right h_symmL_norm_le (norm_nonneg _)
    _ ≤ C₁ * (C₂ * ‖v‖) :=
        mul_le_mul_of_nonneg_left h_norm_cc_v (le_of_lt hC₁_pos)
    _ = C₁ * C₂ * ‖v‖ := by ring

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
    (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ v : TensorRSModel r s ℝ E,
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
          TensorRSSpace r s I b)‖ ≤ C * ‖v‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  let W : M → Set M := fun y₀ =>
    if hy : y₀ ∈ (chartAt H α).source then
      (exists_W_and_constant_symmL (I := I) (M := M) g r s α y₀ hy).choose
    else ∅
  have hW_open : ∀ y₀, IsOpen (W y₀) := by
    intro y₀; simp only [W]
    split_ifs with hy
    · exact (exists_W_and_constant_symmL (I := I) (M := M) g r s α y₀ hy).choose_spec.1
    · exact isOpen_empty
  have hW_mem : ∀ y₀, y₀ ∈ (chartAt H α).source → y₀ ∈ W y₀ := by
    intro y₀ hy; simp only [W, dif_pos hy]
    exact (exists_W_and_constant_symmL (I := I) (M := M) g r s α y₀ hy).choose_spec.2.1
  let N : M → ℝ := fun y₀ =>
    if hy : y₀ ∈ (chartAt H α).source then
      (exists_W_and_constant_symmL (I := I) (M := M) g r s α y₀ hy).choose_spec.2.2.choose
    else 1
  have hN_pos : ∀ y₀, 0 < N y₀ := by
    intro y₀; simp only [N]
    split_ifs with hy
    · exact (exists_W_and_constant_symmL (I := I) (M := M) g r s α y₀ hy).choose_spec.2.2.choose_spec.1
    · exact one_pos
  have hN_bound : ∀ y₀ (hy : y₀ ∈ (chartAt H α).source), ∀ b ∈ W y₀,
      ∀ v : TensorRSModel r s ℝ E,
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
          TensorRSSpace r s I b)‖ ≤ N y₀ * ‖v‖ := by
    intro y₀ hy b hb v
    simp only [W, dif_pos hy] at hb
    simp only [N, dif_pos hy]
    exact (exists_W_and_constant_symmL (I := I) (M := M) g r s α y₀ hy).choose_spec.2.2.choose_spec.2
      b hb v
  have h_cover : K ⊆ ⋃ y₀ ∈ K, W y₀ := fun b hb =>
    Set.mem_iUnion₂.mpr ⟨b, hb, hW_mem b (hKsub hb)⟩
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
  · refine ⟨1, one_pos, ?_⟩
    intro b hb _
    have : b ∈ ⋃ y₀ ∈ S', W y₀ := hS_cover' hb
    rw [hS_empty] at this
    simp at this
  have hS_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set C_max : ℝ := S'.sup' hS_nonempty N with hCmax_def
  have h_C_max_pos : 0 < C_max := by
    rcases hS_nonempty with ⟨y₀, hy₀⟩
    exact (hN_pos y₀).trans_le (Finset.le_sup' (f := N) hy₀)
  refine ⟨C_max + 1, by linarith, ?_⟩
  intro b hb v
  rcases Set.mem_iUnion.mp (hS_cover' hb) with ⟨y₀, hy₀⟩
  rcases Set.mem_iUnion.mp hy₀ with ⟨hy₀_S, hb_in⟩
  have hy₀_α : y₀ ∈ (chartAt H α).source := hKsub (hS_sub_K y₀ hy₀_S)
  have hN_b := hN_bound y₀ hy₀_α b hb_in v
  have h_le_Cmax : N y₀ ≤ C_max := Finset.le_sup' (f := N) hy₀_S
  have h_v_nn : 0 ≤ ‖v‖ := norm_nonneg _
  calc ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
            TensorRSSpace r s I b)‖
      ≤ N y₀ * ‖v‖ := hN_b
    _ ≤ C_max * ‖v‖ := mul_le_mul_of_nonneg_right h_le_Cmax h_v_nn
    _ ≤ (C_max + 1) * ‖v‖ := mul_le_mul_of_nonneg_right (by linarith) h_v_nn

end DifferentialGeometry.Integral.Connection

end
