import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.IntrinsicPieceIteratedFDerivTwoBound


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

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma input_slot_pulled_eq_kernel_repr_eventually
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hmem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  refine Filter.eventually_of_mem (hU_open.mem_nhds hmem) ?_
  intro y hy
  rcases hy with ⟨x, hx_good, hxy⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hx_extsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_src
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  have h_factor :=
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx_inv]; exact hx_src) k
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
      ((extChartAt I α).symm y)
      (chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun y' : M => T.toSection y') B.toFun
        ((extChartAt I α).symm y) k) =
    inputSlotChartKernel (I := I) g r s α B.toFun k
      ((extChartAt I α).symm y)
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
  exact h_factor

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma output_slot_pulled_eq_kernel_repr_eventually
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hmem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  refine Filter.eventually_of_mem (hU_open.mem_nhds hmem) ?_
  intro y hy
  rcases hy with ⟨x, hx_good, hxy⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hx_extsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_src
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  have h_factor :=
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx_inv]; exact hx_src) l
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
      ((extChartAt I α).symm y)
      (chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun y' : M => T.toSection y') B.toFun
        ((extChartAt I α).symm y) l) =
    outputSlotChartKernel (I := I) g r s α B.toFun l
      ((extChartAt I α).symm y)
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
  exact h_factor

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContinuousOn
      (fun y : E => ‖iteratedFDeriv ℝ 2
        (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hcd : ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y)) U :=
    inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B k
  have hk_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have hcd_2 : ContDiffOn ℝ 2
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y)) U :=
    hcd.of_le hk_le
  have h_within_cont : ContinuousOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) U) U :=
    hcd_2.continuousOn_iteratedFDerivWithin (m := 2) (le_refl _)
      (hU_open.uniqueDiffOn)
  have h_eq : EqOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) U)
      (iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y))) U :=
    iteratedFDerivWithin_of_isOpen 2 hU_open
  have h_iter_cont : ContinuousOn
      (iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y))) U := by
    refine h_within_cont.congr ?_
    intro y hy
    exact (h_eq hy).symm
  exact continuous_norm.comp_continuousOn h_iter_cont

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma outputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContinuousOn
      (fun y : E => ‖iteratedFDeriv ℝ 2
        (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hcd : ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y)) U :=
    outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B l
  have hk_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have hcd_2 : ContDiffOn ℝ 2
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y)) U :=
    hcd.of_le hk_le
  have h_within_cont : ContinuousOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) U) U :=
    hcd_2.continuousOn_iteratedFDerivWithin (m := 2) (le_refl _)
      (hU_open.uniqueDiffOn)
  have h_eq : EqOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) U)
      (iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y))) U :=
    iteratedFDerivWithin_of_isOpen 2 hU_open
  have h_iter_cont : ContinuousOn
      (iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y))) U := by
    refine h_within_cont.congr ?_
    intro y hy
    exact (h_eq hy).symm
  exact continuous_norm.comp_continuousOn h_iter_cont

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma pouTsupport_subset_goodSet (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have h_eq :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
    (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
  exact (chartAtlasPOU_isSubordinate I M) α hb

omit [NeZero (Module.finrank ℝ E)] in
private lemma inputSlotChartKernel_iteratedFDeriv_two_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
            (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := inputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (I := I) (M := M) g r s α B k
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma outputSlotChartKernel_iteratedFDeriv_two_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
            (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := outputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (I := I) (M := M) g r s α B l
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps

  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
