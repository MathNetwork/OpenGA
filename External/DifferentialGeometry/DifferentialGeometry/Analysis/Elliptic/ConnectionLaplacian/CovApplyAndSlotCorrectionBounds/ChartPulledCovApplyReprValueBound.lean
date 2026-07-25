import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.IntrinsicPieceFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartPulledCovApplyExplicitFormula

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

omit [NeZero (Module.finrank ℝ E)] in
private lemma trivToE_B_value_bound_on_pouTsupport
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖trivToE (I := I) α b (B.toFun b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  have hcont_u : ContinuousOn (fun y : E =>
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    continuous_norm.comp_continuousOn hu_cd.continuousOn
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_u_M : ContinuousOn (fun b : M =>
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖) K_set :=
    hcont_u.comp hφ_cont hmaps
  obtain ⟨Cu, hCu_mem⟩ := hK_compact.bddAbove_image hcont_u_M
  refine ⟨max Cu 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart
  have hsymm_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_extsrc
  have h_eq : ‖trivToE (I := I) α b (B.toFun b)‖ =
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ := by
    change ‖trivToE (I := I) α b (B.toFun b)‖ =
      ‖chartE_section_repr (I := I) α B.toFun
        ((extChartAt I α).symm (extChartAt I α b))‖
    rw [hsymm_inv]
    rfl
  rw [h_eq]
  have h1 := hCu_mem ⟨b, hb, rfl⟩
  exact le_trans h1 (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
