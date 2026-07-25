import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.IntrinsicPieceFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma c_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  exact hF_cd.fderiv_of_isOpen hU_open h_le

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma u_contDiffOn_goodSet'
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  exact chartE_pullback_contDiffOn_goodSet (I := I) α hB_on

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma pouTsupport_subset_goodSet' (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have h_eq :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
    (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
  exact (chartAtlasPOU_isSubordinate I M) α hb

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDeriv_u_continuousOn
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : ℕ) :
    ContinuousOn
      (fun y : E => ‖iteratedFDeriv ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U :=
    u_contDiffOn_goodSet' (I := I) α B
  have hk_le : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((k : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have hcd_k : ContDiffOn ℝ k
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U :=
    hu_cd.of_le hk_le
  have h_within_cont : ContinuousOn
      (iteratedFDerivWithin ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U) U :=
    hcd_k.continuousOn_iteratedFDerivWithin (m := k) (le_refl _)
      (hU_open.uniqueDiffOn)
  have h_eq : EqOn
      (iteratedFDerivWithin ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U)
      (iteratedFDeriv ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)) U :=
    iteratedFDerivWithin_of_isOpen k hU_open
  have h_iter_cont : ContinuousOn
      (iteratedFDeriv ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)) U := by
    refine h_within_cont.congr ?_
    intro y hy
    exact (h_eq hy).symm
  exact continuous_norm.comp_continuousOn h_iter_cont

omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDeriv_u_bound_012
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖iteratedFDeriv ℝ 0
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 1
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet' (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set U :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have h_cont_0 : ContinuousOn (fun b : M => ‖iteratedFDeriv ℝ 0
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖) K_set :=
    (iteratedFDeriv_u_continuousOn (I := I) α B 0).comp
      hφ_cont hmaps
  have h_cont_1 : ContinuousOn (fun b : M => ‖iteratedFDeriv ℝ 1
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖) K_set :=
    (iteratedFDeriv_u_continuousOn (I := I) α B 1).comp
      hφ_cont hmaps
  have h_cont_2 : ContinuousOn (fun b : M => ‖iteratedFDeriv ℝ 2
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖) K_set :=
    (iteratedFDeriv_u_continuousOn (I := I) α B 2).comp
      hφ_cont hmaps
  obtain ⟨C0, hC0_mem⟩ := hK_compact.bddAbove_image h_cont_0
  obtain ⟨C1, hC1_mem⟩ := hK_compact.bddAbove_image h_cont_1
  obtain ⟨C2, hC2_mem⟩ := hK_compact.bddAbove_image h_cont_2
  refine ⟨max (max (max C0 C1) C2) 0, le_max_right _ _, ?_⟩
  intro b hb
  refine ⟨?_, ?_, ?_⟩
  · have h := hC0_mem ⟨b, hb, rfl⟩
    calc _ ≤ C0 := h
      _ ≤ max C0 C1 := le_max_left _ _
      _ ≤ max (max C0 C1) C2 := le_max_left _ _
      _ ≤ max (max (max C0 C1) C2) 0 := le_max_left _ _
  · have h := hC1_mem ⟨b, hb, rfl⟩
    calc _ ≤ C1 := h
      _ ≤ max C0 C1 := le_max_right _ _
      _ ≤ max (max C0 C1) C2 := le_max_left _ _
      _ ≤ max (max (max C0 C1) C2) 0 := le_max_left _ _
  · have h := hC2_mem ⟨b, hb, rfl⟩
    calc _ ≤ C2 := h
      _ ≤ max (max C0 C1) C2 := le_max_right _ _
      _ ≤ max (max (max C0 C1) C2) 0 := le_max_left _ _

omit [NeZero (Module.finrank ℝ E)] in
theorem intrinsic_piece_iteratedFDeriv_two_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
          (fun y : E =>
            fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y')
                ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)‖ ≤
        K * (‖iteratedFDeriv ℝ 3 (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨C, hC_nn, hC_bound⟩ := iteratedFDeriv_u_bound_012 (I := I) (M := M) α B
  refine ⟨2 * C, by positivity, ?_⟩
  intro T b hb
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) ∘ (extChartAt I α).symm with hF_def
  set u : E → E :=
    chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm with hu_def
  set x : E := extChartAt I α b with hx_def
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hF_cd : ContDiffOn ℝ ∞ F U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hu_cd : ContDiffOn ℝ ∞ u U := u_contDiffOn_goodSet' (I := I) α B
  set c : E → (E →L[ℝ] TensorRSModel r s ℝ E) := fderiv ℝ F with hc_def
  have hc_cd : ContDiffOn ℝ ∞ c U :=
    c_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  have hx_mem : x ∈ U := ⟨b, hb_good, rfl⟩
  have hUniqueDiff : UniqueDiffOn ℝ U := hU_open.uniqueDiffOn
  have h_two_le_top : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have h_leibniz_within :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => c y (u y)) U x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDerivWithin ℝ i c U x‖ *
            ‖iteratedFDerivWithin ℝ (2 - i) u U x‖ :=
    norm_iteratedFDerivWithin_clm_apply hc_cd hu_cd hUniqueDiff hx_mem h_two_le_top
  have h_iter_c : ∀ k : ℕ,
      iteratedFDerivWithin ℝ k c U x = iteratedFDeriv ℝ k c x := by
    intro k; exact iteratedFDerivWithin_of_isOpen k hU_open hx_mem
  have h_iter_u : ∀ k : ℕ,
      iteratedFDerivWithin ℝ k u U x = iteratedFDeriv ℝ k u x := by
    intro k; exact iteratedFDerivWithin_of_isOpen k hU_open hx_mem
  have h_iter_clm :
      iteratedFDerivWithin ℝ 2 (fun y : E => c y (u y)) U x =
        iteratedFDeriv ℝ 2 (fun y : E => c y (u y)) x :=
    iteratedFDerivWithin_of_isOpen 2 hU_open hx_mem
  have h_norm_clm :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => c y (u y)) U x‖ =
        ‖iteratedFDeriv ℝ 2 (fun y : E => c y (u y)) x‖ := by
    rw [h_iter_clm]
  have h_norm_iter_c : ∀ k : ℕ,
      ‖iteratedFDerivWithin ℝ k c U x‖ = ‖iteratedFDeriv ℝ k c x‖ := by
    intro k; rw [h_iter_c k]
  have h_norm_iter_u : ∀ k : ℕ,
      ‖iteratedFDerivWithin ℝ k u U x‖ = ‖iteratedFDeriv ℝ k u x‖ := by
    intro k; rw [h_iter_u k]
  have h_leibniz_global :
      ‖iteratedFDeriv ℝ 2 (fun y : E => c y (u y)) x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (2 - i) u x‖ := by
    rw [← h_norm_clm]
    refine le_trans h_leibniz_within ?_
    apply Finset.sum_le_sum
    intro i _
    rw [h_norm_iter_c i, h_norm_iter_u (2 - i)]
  have h_goalLHS_fn : (fun y : E =>
        fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y)))) =
      (fun y : E => c y (u y)) := by
    funext y
    rfl
  rw [h_goalLHS_fn]
  have h_choose_0 : ((2 : ℕ).choose 0 : ℝ) = 1 := by norm_num
  have h_choose_1 : ((2 : ℕ).choose 1 : ℝ) = 2 := by norm_num
  have h_choose_2 : ((2 : ℕ).choose 2 : ℝ) = 1 := by norm_num
  have h_sum_eq :
      ∑ i ∈ Finset.range (2 + 1),
        ↑((2 : ℕ).choose i) *
          ‖iteratedFDeriv ℝ i c x‖ *
          ‖iteratedFDeriv ℝ (2 - i) u x‖ =
        ‖iteratedFDeriv ℝ 0 c x‖ * ‖iteratedFDeriv ℝ 2 u x‖ +
        (2 : ℝ) * ‖iteratedFDeriv ℝ 1 c x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
        ‖iteratedFDeriv ℝ 2 c x‖ * ‖iteratedFDeriv ℝ 0 u x‖ := by
    rw [show (2 + 1 : ℕ) = 3 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [zero_add, h_choose_0, h_choose_1, h_choose_2]
    have h_sub_0 : (2 - 0 : ℕ) = 2 := by norm_num
    have h_sub_1 : (2 - 1 : ℕ) = 1 := by norm_num
    have h_sub_2 : (2 - 2 : ℕ) = 0 := by norm_num
    rw [h_sub_0, h_sub_1, h_sub_2]
    ring
  rw [h_sum_eq] at h_leibniz_global
  have h_c0 : ‖iteratedFDeriv ℝ 0 c x‖ = ‖iteratedFDeriv ℝ 1 F x‖ := by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 0)
    convert this
  have h_c1 : ‖iteratedFDeriv ℝ 1 c x‖ = ‖iteratedFDeriv ℝ 2 F x‖ := by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 1)
    convert this
  have h_c2 : ‖iteratedFDeriv ℝ 2 c x‖ = ‖iteratedFDeriv ℝ 3 F x‖ := by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 2)
    convert this
  rw [h_c0, h_c1, h_c2] at h_leibniz_global
  have h_fderiv_iter :
      ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ :=
    norm_iteratedFDeriv_one (𝕜 := ℝ) F (x := x)
  rw [h_fderiv_iter] at h_leibniz_global
  obtain ⟨hu0_le, hu1_le, hu2_le⟩ := hC_bound b hb.1
  set A1 : ℝ := ‖fderiv ℝ F x‖ with hA1_def
  set A2 : ℝ := ‖iteratedFDeriv ℝ 2 F x‖ with hA2_def
  set A3 : ℝ := ‖iteratedFDeriv ℝ 3 F x‖ with hA3_def
  set Bu0 : ℝ := ‖iteratedFDeriv ℝ 0 u x‖ with hBu0_def
  set Bu1 : ℝ := ‖iteratedFDeriv ℝ 1 u x‖ with hBu1_def
  set Bu2 : ℝ := ‖iteratedFDeriv ℝ 2 u x‖ with hBu2_def
  have hA1_nn : 0 ≤ A1 := norm_nonneg _
  have hA2_nn : 0 ≤ A2 := norm_nonneg _
  have hA3_nn : 0 ≤ A3 := norm_nonneg _
  have hBu0_nn : 0 ≤ Bu0 := norm_nonneg _
  have hBu1_nn : 0 ≤ Bu1 := norm_nonneg _
  have hBu2_nn : 0 ≤ Bu2 := norm_nonneg _
  have h_leibniz' :
      ‖iteratedFDeriv ℝ 2 (fun y : E => c y (u y)) x‖ ≤
        A1 * Bu2 + (2 : ℝ) * A2 * Bu1 + A3 * Bu0 := h_leibniz_global
  have h_A1Bu2 : A1 * Bu2 ≤ A1 * C :=
    mul_le_mul_of_nonneg_left hu2_le hA1_nn
  have h_A2Bu1 : A2 * Bu1 ≤ A2 * C :=
    mul_le_mul_of_nonneg_left hu1_le hA2_nn
  have h_A3Bu0 : A3 * Bu0 ≤ A3 * C :=
    mul_le_mul_of_nonneg_left hu0_le hA3_nn
  have h_AC_combined :
      A1 * Bu2 + (2 : ℝ) * A2 * Bu1 + A3 * Bu0 ≤
        A1 * C + 2 * (A2 * C) + A3 * C := by
    have h2 : (2 : ℝ) * A2 * Bu1 ≤ 2 * (A2 * C) := by
      have : (2 : ℝ) * A2 * Bu1 = 2 * (A2 * Bu1) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h_A2Bu1 (by norm_num)
    linarith
  have h_final_le :
      A1 * C + 2 * (A2 * C) + A3 * C ≤ 2 * C * (A3 + A2 + A1) := by
    have h_A1C_nn : 0 ≤ A1 * C := mul_nonneg hA1_nn hC_nn
    have h_A3C_nn : 0 ≤ A3 * C := mul_nonneg hA3_nn hC_nn
    have h_A1C_double : A1 * C ≤ 2 * (A1 * C) := by linarith
    have h_A3C_double : A3 * C ≤ 2 * (A3 * C) := by linarith
    have hStep : A1 * C + 2 * (A2 * C) + A3 * C ≤
        2 * (A1 * C) + 2 * (A2 * C) + 2 * (A3 * C) := by linarith
    have h_target_eq :
        2 * (A1 * C) + 2 * (A2 * C) + 2 * (A3 * C) =
          2 * C * (A3 + A2 + A1) := by ring
    linarith [hStep, h_target_eq.le, h_target_eq.symm.le]
  exact le_trans h_leibniz' (le_trans h_AC_combined h_final_le)

end Connection
end Integral
end DifferentialGeometry

end
