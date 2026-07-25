import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawTensorConnLapPointwiseBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.RawTensorConnLap2ndApplicationOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartPulledCovApplyReprValueBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartReprNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.IntrinsicPieceFderivBound
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.IntrinsicComponent
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs


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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma sq_add_three_le_three_mul_sum_sq (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma reprT_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (T.toSection x)) :=
    T.toSection.contMDiff
  have hbase :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  have hcm_on_source :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)
        ((chartAt H α).source) := by
    refine ContMDiffOn.congr hrewrite ?_
    intro x hx
    have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
      rw [hbase]; exact hx
    change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x
        (T.toSection x) = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hcm_on_good :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)
        (chartLeviCivitaGoodSet (I := I) α) := by
    rw [h_good_eq_source]; exact hcm_on_source
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hx_good, rfl⟩
  set F : M → TensorRSModel r s ℝ E :=
    fun b : M => tensorRSChartE_section_repr (I := I) r s α
      (fun y' : M => T.toSection y') b with hF_def
  have hF_at : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞ F x :=
    hcm_on_good.contMDiffAt (hgood_open.mem_nhds hx_good)
  set φ := extChartAt I α
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hxφ_src : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_on :
      ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      φ.symm φ.target (φ x) := hsymm_on (φ x) hxφ_tgt
  have hF_at' : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      F (φ.symm (φ x)) := by
    rw [hxφ_inv]; exact hF_at
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (F ∘ φ.symm) φ.target (φ x) :=
    hF_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_reprT_differentiableAt_chart_point
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b) := by
  classical
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hcd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    hcd.fderiv_of_isOpen hU_open h_le
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by intro h; exact absurd h (by simp)
  have hwithin : DifferentiableWithinAt ℝ
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α)
      (extChartAt I α b) :=
    (hfd_cd.differentiableOn hne) (extChartAt I α b) hx_mem
  exact hwithin.differentiableAt (hU_open.mem_nhds hx_mem)

omit [BoundarylessManifold I M] in
private lemma chartFrameNormGlobalSmooth_fderiv_repr_bound
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖fderiv ℝ
            (chartE_section_repr (I := I) α
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) ∘
              (extChartAt I α).symm)
            (extChartAt I α b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  set Bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hBg_def
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hBg_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (Bg.toFun x)) := Bg.contMDiff
  have hBg_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (Bg.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hBg_total.contMDiffOn
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hBg_on
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    hu_cd.fderiv_of_isOpen hU_open h_le
  have hcont_fd : ContinuousOn (fun y : E =>
      ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    continuous_norm.comp_continuousOn hfd_cd.continuousOn
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    have h_eq := DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    intro y hy
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hy
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_fd_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖) K_set :=
    hcont_fd.comp hφ_cont hmaps
  obtain ⟨Cfd, hCfd_mem⟩ := hK_compact.bddAbove_image hcont_fd_M
  refine ⟨max Cfd 0, le_max_right _ _, ?_⟩
  intro b hb
  have h := hCfd_mem ⟨b, hb, rfl⟩
  exact le_trans h (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
