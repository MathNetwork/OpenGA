import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.IteratedFDerivTensorReprChartCompBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawTensorConnLapChartTargetSqBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapChartL2PouBridge
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.FderivToWkpNormBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.IteratedFderivToWkpNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBoundChartPouEuclFderiv


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  classical
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma tensorChartComp_tsupport_subset_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  set f : M → ℝ := tensorChartComponentPou (I := I) (M := M)
    g r s T α Idx Jdx with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  set K : Set EuclN :=
    (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_src : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_src
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_subset_target : K ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro z hz_carrier
    rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
    have hx_src : x ∈ (extChartAt I α).source := hsub_src hx_supp
    have hw_target : w ∈ (extChartAt I α).target := by
      rw [← hxw]; exact (extChartAt I α).map_source hx_src
    exact ⟨w, hw_target, hwz⟩
  have h_supp_K : Function.support
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ⊆ K := by
    intro y hy_supp
    by_contra hyK
    apply hy_supp
    by_cases hy_target :
        y ∈ chartTargetEuclid (I := I) (M := M) α
    · rcases hy_target with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [tensorChartComp_def, tensorChartComponent_def,
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) α f ⟨w, hw_target, hwy⟩]
      by_contra hne_f
      apply hyK
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
          tsupport f := by
        apply subset_tsupport
        exact hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      exact ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
    · rw [tensorChartComp_def, tensorChartComponent_def]
      exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) α f hy_target
  refine (closure_minimal h_supp_K hK_closed).trans hK_subset_target

private lemma sq_eLpNorm_two_eq_lintegral_ofReal_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq f μ]
  refine lintegral_congr ?_
  intro x
  rw [show ((f x) ^ 2 : ℝ) = ‖f x‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs],
    ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm_eq_enorm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma repr_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e := by
  classical
  set b : M := (extChartAt I α).symm e
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  have hψ_eq :
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) =
        fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
    funext y
    set bb := (extChartAt I α).symm y
    set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
      r s α (fun z : M => T.toSection z) bb
    have hR_recover : R =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx R •
              tensorChartBasisElement (E := E) r s Idx Jdx :=
      tensorRSModel_eq_sum_basis (E := E) r s R
    have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx R =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx bb := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def]
      rfl
    change R = _
    rw [hR_recover]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [hcomp_eq Idx Jdx]
    rfl
  rw [hψ_eq]
  refine DifferentiableAt.fun_sum (fun Idx _ => ?_)
  refine DifferentiableAt.fun_sum (fun Jdx _ => ?_)
  refine DifferentiableAt.smul_const ?_ _
  have hdiff := chart_pulled_component_differentiableAt
    (I := I) (M := M) g r s T α Idx Jdx hb_chart
  rwa [he_eq] at hdiff

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma raw_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e :=
  tensorChartComponentRaw_symm_differentiableAt
    (I := I) (M := M) g r s T α Idx Jdx he

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_pou_raw_symm_eq_chain
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  rw [fderiv_pou_mul_raw_symm_eq_fderiv_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he]
  exact fderiv_tensorChartComp_toEuclidean (I := I) (M := M) g r s T α Idx Jdx e

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma fderiv_pou_raw_symm_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e) •
          fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e +
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e) •
          fderiv ℝ
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e := by
  classical
  have hP_diff : DifferentiableAt ℝ
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) e :=
    chartAtlasPOU_symm_differentiableAt (I := I) (M := M) α he
  have hR_diff : DifferentiableAt ℝ
      (fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e')) e :=
    raw_symm_differentiableAt (I := I) (M := M) g r s T α Idx Jdx he
  exact fderiv_fun_mul hP_diff hR_diff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma fderiv_repr_opNormSq_le_sum_fderiv_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {e : E}
    (he : e ∈ (extChartAt I α).target) :
    ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        e‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) e‖ ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set b : M := (extChartAt I α).symm e with hb_def
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  have hbasis_le : ∀ Idx Jdx, ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤ Bnorm := by
    intro Idx Jdx
    exact tensorChartBasisElement_norm_le (E := E) r s Idx Jdx
  have h_lin :=
    fderiv_repr_opNorm_le_sum_fderiv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart
  rw [he_eq] at h_lin
  have h_rhs_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ *
              ‖tensorChartBasisElement (E := E) r s Idx Jdx‖) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact mul_le_mul_of_nonneg_left (hbasis_le Idx Jdx) (norm_nonneg _)
  have h_norm_le : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ Idx, ∑ Jdx,
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := h_lin.trans h_rhs_le
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_sum_pair_eq :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)]
  have h_sum_nn :
      0 ≤ (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
          p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_le' : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [← h_sum_pair_eq] at h_norm_le; exact h_norm_le
  have h_norm_sq : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ((∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 := by
    have := mul_le_mul h_norm_le' h_norm_le' (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  have hCS :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    exact hbase
  have h_combined : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 *
        ∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have h_sq_eq : ((∑ p ∈ V,
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 = (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    calc ‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ (∑ p ∈ V,
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * (∑ p ∈ V,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) * Bnorm ^ 2 := h_mul
      _ = (V.card : ℝ) * Bnorm ^ 2 *
            ∑ p ∈ V,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by ring
  have h_pair_to_nest :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2)]
  rw [h_pair_to_nest] at h_combined
  exact h_combined

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma pou_sq_fderiv_repr_sq_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (K_pou : ℝ) (hK_pou_nn : 0 ≤ K_pou)
    (hK_pou_bound : ∀ e ∈ (extChartAt I α).target,
      ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm e)) ^ 2) *
      (‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (2 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ ^ 2 +
        (2 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2 * K_pou ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e)
  have hρ_nn : 0 ≤ ρ := by
    have := (chartAtlasPOU I M).nonneg α ((extChartAt I α).symm e); exact this
  have h_sq := fderiv_repr_opNormSq_le_sum_fderiv_components_sq
    (I := I) (M := M) g r s T α (e := e) he
  have h_scaled : ρ ^ 2 *
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
  have h_per_IJ : ∀ Idx Jdx,
      ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
        2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
        2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2 := by
    intro Idx Jdx
    set raw_val : ℝ := tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e)
    set FR : E →L[ℝ] ℝ := fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) e
    set FP : E →L[ℝ] ℝ := fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e
    set L : E →L[ℝ] ℝ := fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e
    have hleibniz : L = ρ • FR + raw_val • FP := by
      simpa [L, FR, FP, raw_val, ρ] using
        fderiv_pou_raw_symm_leibniz (I := I) (M := M) g r s T α Idx Jdx he
    have h_eq : ρ • FR = L - raw_val • FP := by
      rw [hleibniz]; abel
    have hnorm : ‖ρ • FR‖ ≤ ‖L‖ + |raw_val| * ‖FP‖ := by
      rw [h_eq]
      refine le_trans (norm_sub_le _ _) ?_
      refine add_le_add le_rfl ?_
      rw [norm_smul, Real.norm_eq_abs]
    have hρFR : ‖ρ • FR‖ = ρ * ‖FR‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ_nn]
    rw [hρFR] at hnorm
    have hρFR_nn : 0 ≤ ρ * ‖FR‖ := mul_nonneg hρ_nn (norm_nonneg _)
    have hLraw_nn : 0 ≤ ‖L‖ + |raw_val| * ‖FP‖ :=
      add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    have hsq : (ρ * ‖FR‖) ^ 2 ≤ (‖L‖ + |raw_val| * ‖FP‖) ^ 2 := by
      exact pow_le_pow_left₀ hρFR_nn hnorm 2
    have hexp : (‖L‖ + |raw_val| * ‖FP‖) ^ 2 ≤ 2 * ‖L‖ ^ 2 + 2 * (|raw_val| * ‖FP‖) ^ 2 := by
      have h := sq_nonneg (‖L‖ - |raw_val| * ‖FP‖)
      nlinarith [h]
    have hρ_sq_FR_sq : ρ ^ 2 * ‖FR‖ ^ 2 = (ρ * ‖FR‖) ^ 2 := by ring
    rw [hρ_sq_FR_sq]
    refine le_trans hsq (le_trans hexp ?_)
    have hL_eq := fderiv_pou_raw_symm_eq_chain (I := I) (M := M)
      g r s T α Idx Jdx he
    have hL_bound : ‖L‖ ≤
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ * NtoE := by
      change ‖fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e‖ ≤ _
      rw [hL_eq]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hL_nn : 0 ≤ ‖L‖ := norm_nonneg _
    have hLsq : ‖L‖ ^ 2 ≤
        (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 :=
      pow_le_pow_left₀ hL_nn hL_bound 2
    have hFP_bound : ‖FP‖ ≤ K_pou := hK_pou_bound e he
    have hFP_nn : 0 ≤ ‖FP‖ := norm_nonneg _
    have hraw_abs_nn : 0 ≤ |raw_val| := abs_nonneg _
    have h_raw_fp_nn : 0 ≤ |raw_val| * ‖FP‖ := mul_nonneg hraw_abs_nn hFP_nn
    have h_raw_K_nn : 0 ≤ |raw_val| * K_pou := mul_nonneg hraw_abs_nn hK_pou_nn
    have h_raw_fp_le : |raw_val| * ‖FP‖ ≤ |raw_val| * K_pou :=
      mul_le_mul_of_nonneg_left hFP_bound hraw_abs_nn
    have h_raw_fp_sq_le : (|raw_val| * ‖FP‖) ^ 2 ≤ (|raw_val| * K_pou) ^ 2 :=
      pow_le_pow_left₀ h_raw_fp_nn h_raw_fp_le 2
    have h_raw_K_sq : (|raw_val| * K_pou) ^ 2 = raw_val ^ 2 * K_pou ^ 2 := by
      rw [mul_pow]; rw [sq_abs]
    have hL_NtoE_sq : (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 =
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by ring
    have h_total : 2 * ‖L‖ ^ 2 + 2 * (|raw_val| * ‖FP‖) ^ 2 ≤
        2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
        2 * raw_val ^ 2 * K_pou ^ 2 := by
      have h1 : 2 * ‖L‖ ^ 2 ≤ 2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by
        calc 2 * ‖L‖ ^ 2 ≤ 2 * (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left hLsq (by norm_num)
            _ = 2 *
                ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by
              rw [hL_NtoE_sq]; ring
      have h2 : 2 * (|raw_val| * ‖FP‖) ^ 2 ≤ 2 * raw_val ^ 2 * K_pou ^ 2 := by
        calc 2 * (|raw_val| * ‖FP‖) ^ 2 ≤ 2 * (|raw_val| * K_pou) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left h_raw_fp_sq_le (by norm_num)
            _ = 2 * raw_val ^ 2 * K_pou ^ 2 := by
              rw [h_raw_K_sq]; ring
      linarith
    exact h_total
  have h_sum_per :
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (2 * N * Bnorm ^ 2 * NtoE ^ 2) *
          ∑ Idx, ∑ Jdx,
            ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              ((toEuclidean (E := E)) e)‖ ^ 2 +
        (2 * N * Bnorm ^ 2 * K_pou ^ 2) *
          ∑ Idx, ∑ Jdx,
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 := by
    rw [show ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) = (N * Bnorm ^ 2) *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
      rw [show (∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
            ρ ^ 2 * ∑ Idx, ∑ Jdx,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [Finset.mul_sum]]
      ring]
    have hNBsq_nn : 0 ≤ N * Bnorm ^ 2 :=
      mul_nonneg hN_nn (sq_nonneg _)
    calc N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ N * Bnorm ^ 2 *
            (∑ Idx, ∑ Jdx,
              (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
              2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNBsq_nn
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = (2 * N * Bnorm ^ 2 * NtoE ^ 2) *
            ∑ Idx, ∑ Jdx,
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ ^ 2 +
          (2 * N * Bnorm ^ 2 * K_pou ^ 2) *
            ∑ Idx, ∑ Jdx,
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 := by
          have h_inner_sum : ∀ Idx,
              (∑ Jdx,
                (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) =
              (∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) +
              (∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) := fun Idx => by
            rw [Finset.sum_add_distrib]
          have h_outer_sum :
              (∑ Idx, ∑ Jdx,
                (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) =
              (∑ Idx, ∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) +
              (∑ Idx, ∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) := by
            rw [Finset.sum_congr rfl (fun Idx _ => h_inner_sum Idx)]
            rw [Finset.sum_add_distrib]
          rw [h_outer_sum]
          rw [show (∑ Idx, ∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) =
            2 * NtoE ^ 2 *
              ∑ Idx, ∑ Jdx,
                ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Idx _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Jdx _ => ?_)
            ring]
          rw [show (∑ Idx, ∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) =
            2 * K_pou ^ 2 *
              ∑ Idx, ∑ Jdx,
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e)) ^ 2 from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Idx _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Jdx _ => ?_)
            ring]
          ring
  exact le_trans h_scaled h_sum_per

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma raw_sym_sq_ofReal_aeMeasurable_restrict
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN =>
        ENNReal.ofReal
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_raw_symm_contDiffOn : ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) :=
    tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_symm_cont : ContinuousOn
      (fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e')) (extChartAt I α).target :=
    h_raw_symm_contDiffOn.continuousOn
  have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
    (toEuclidean (E := E)).symm.continuous
  have h_raw_sym_cont : ContinuousOn
      (fun y : EuclN => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine h_raw_symm_cont.comp h_toEucl_symm_cont.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_raw_sym_ae :
      AEMeasurable
        (fun y : EuclN => tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    h_raw_sym_cont.aemeasurable h_chartTarget_meas
  have h_sq_ae : AEMeasurable
      (fun y : EuclN => (tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_raw_sym_ae.pow_const 2
  exact ENNReal.measurable_ofReal.comp_aemeasurable h_sq_ae

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma fderiv_tensorChartComp_sq_ofReal_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (fun y : EuclN =>
        ENNReal.ofReal
          (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  refine (continuous_pow 2).measurable.comp ?_
  have h_fderiv_cont : Continuous
      (fun y : EuclN =>
        fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) := by
    have := (tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx)
    exact this.continuous_fderiv (by simp)
  exact h_fderiv_cont.norm.measurable

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTargetPouWeightedL2NormSq_fderiv_repr_le_sum_chartComp_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖fderiv ℝ
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    (chartTargetEuclid (I := I) (M := M) α) ^ 2 +
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  eLpNorm
                      (fun y : EuclN =>
                        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
                      ((volume : Measure EuclN).restrict
                        (chartTargetEuclid (I := I) (M := M) α)) ^ 2) := by
  classical
  obtain ⟨K_pou, hK_pou_nn, hK_pou_bound⟩ :=
    exists_pou_symm_fderiv_uniform_bound (I := I) (M := M) α
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set C1 : ℝ := 2 * N * Bnorm ^ 2 * NtoE ^ 2 with hC1_def
  set C2 : ℝ := 2 * N * Bnorm ^ 2 * K_pou ^ 2 with hC2_def
  have hC1_nn : 0 ≤ C1 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    exact by norm_num
  have hC2_nn : 0 ≤ C2 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    exact by norm_num
  refine ⟨C1 + C2, add_nonneg hC1_nn hC2_nn, ?_⟩
  intro T
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2) with hlhs_def
  set fIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)
    with hfInt_def
  set rIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
    with hrInt_def
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal C1 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fIntegrand Idx Jdx y) +
        ENNReal.ofReal C2 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rIntegrand Idx Jdx y) := by
    intro y hy
    set e : E := (toEuclidean (E := E)).symm y with he_def
    have he_target : e ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_real := pou_sq_fderiv_repr_sq_pointwise
      (I := I) (M := M) g r s T α K_pou hK_pou_nn hK_pou_bound (e := e) he_target
    have h_toEucl_e : (toEuclidean (E := E)) e = y := by
      simp [he_def, (toEuclidean (E := E)).apply_symm_apply]
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e) with hρ_def
    have hρ_sym : ρ = (chartAtlasPOU I M α : M → ℝ) (sym y) := by
      simp [hρ_def, hsym_def, he_def]
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    set FRsq : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 with hFRsq_def
    have hFRsq_nn : 0 ≤ FRsq := sq_nonneg _
    set fSum : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ ^ 2 with hfSum_def
    have hfSum_nn : 0 ≤ fSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    set rSum : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 with hrSum_def
    have hrSum_nn : 0 ≤ rSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h_real' : ρ ^ 2 * FRsq ≤ C1 * fSum + C2 * rSum := by
      simpa [ρ, FRsq, fSum, rSum, C1, C2, Bnorm, NtoE, N, hC1_def, hC2_def,
        hBnorm_def, hNtoE_def, hN_def] using h_real
    have h_LHS_eq : lhsIntegrand y =
        ENNReal.ofReal (ρ ^ 2 * FRsq) := by
      simp only [hlhs_def, ← hρ_sym, FRsq]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_LHS_eq]
    refine le_trans (ENNReal.ofReal_le_ofReal h_real') ?_
    have h_C1fSum_nn : 0 ≤ C1 * fSum := mul_nonneg hC1_nn hfSum_nn
    have h_C2rSum_nn : 0 ≤ C2 * rSum := mul_nonneg hC2_nn hrSum_nn
    rw [ENNReal.ofReal_add h_C1fSum_nn h_C2rSum_nn]
    rw [ENNReal.ofReal_mul hC1_nn, ENNReal.ofReal_mul hC2_nn]
    have h_fSum_eq :
        ENNReal.ofReal fSum =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y := by
      simp only [hfSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg (fun Jdx _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun Jdx _ => sq_nonneg _)]
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      change ENNReal.ofReal
          (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2) =
        fIntegrand Idx Jdx y
      rw [h_toEucl_e]
    have h_rSum_eq :
        ENNReal.ofReal rSum =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y := by
      simp only [hrSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg (fun Jdx _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun Jdx _ => sq_nonneg _)]
    rw [h_fSum_eq, h_rSum_eq]
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (ENNReal.ofReal C1 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fIntegrand Idx Jdx y) +
              ENNReal.ofReal C2 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  rIntegrand Idx Jdx y))
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  have h_fInt_meas : ∀ Idx Jdx, Measurable (fIntegrand Idx Jdx) := fun Idx Jdx =>
    fderiv_tensorChartComp_sq_ofReal_measurable
      (I := I) (M := M) g r s T α Idx Jdx
  have h_rInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (rIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    have := raw_sym_sq_ofReal_aeMeasurable_restrict
      (I := I) (M := M) g r s T α Idx Jdx
    simpa [hrInt_def, hsym_def] using this
  have h_fInt_sum_aeMeas :
      AEMeasurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    have : Measurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y) := by
      refine Finset.measurable_sum _ (fun Idx _ => ?_)
      refine Finset.measurable_sum _ (fun Jdx _ => ?_)
      exact h_fInt_meas Idx Jdx
    exact this.aemeasurable
  have h_rInt_sum_aeMeas :
      AEMeasurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_inner_ae : ∀ Idx,
        AEMeasurable
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
      have h_eq : (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
        funext y
        simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    have h_funsum_ae : AEMeasurable
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      Finset.aemeasurable_sum _ (fun Idx _ => h_inner_ae Idx)
    have h_eq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) =
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
      funext y
      simp [Finset.sum_apply]
    rwa [h_eq] at h_funsum_ae
  have h_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y) +
            ENNReal.ofReal C2 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y))
          ∂(volume : Measure EuclN) =
        (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal C1 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN)) +
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal C2 *
                (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                  ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                    rIntegrand Idx Jdx y)
              ∂(volume : Measure EuclN)) := by
    have h_lhs_aeMeas : AEMeasurable
        (fun y : EuclN =>
          ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      exact AEMeasurable.const_mul h_fInt_sum_aeMeas _
    exact lintegral_add_left' h_lhs_aeMeas _
  rw [h_split] at h_int_mono
  have h_const_C1 :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C1 *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h_const_C2 :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal C2 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C2 *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [h_const_C1, h_const_C2] at h_int_mono
  have h_dist_f :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                fIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    rw [lintegral_finset_sum _ (fun Idx _ => by
      refine Finset.measurable_sum _ (fun Jdx _ => ?_)
      exact h_fInt_meas Idx Jdx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum _ (fun Jdx _ => h_fInt_meas Idx Jdx)
  have h_dist_r :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    have h_inner_ae : ∀ Idx,
        AEMeasurable
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
      have h_eq : (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
        funext y
        simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    rw [lintegral_finset_sum' _ (fun Idx _ => h_inner_ae Idx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum' _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
  rw [h_dist_f, h_dist_r] at h_int_mono
  have h_per_f : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          fIntegrand Idx Jdx y ∂(volume : Measure EuclN) ≤
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
    intro Idx Jdx
    have h_chartTarget_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α
    have h_tcc_smooth : ContDiff ℝ ∞
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
      tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
    have h_tcc_compactSupport : HasCompactSupport
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
      tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
    have h_tcc_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        ⊆ chartTargetEuclid (I := I) (M := M) α :=
      tensorChartComp_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) g r s T α Idx Jdx
    have h_brg :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_fderiv_eLpNorm_le_wkpNorm_one_two
        (d := Module.finrank ℝ E) h_chartTarget_open
        (h_tcc_smooth.of_le (by simp)) h_tcc_compactSupport h_tcc_supp
    have h_lp_sq :
        (eLpNorm
            (fun y : EuclN =>
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 =
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              fIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
      have h_eLp_sq := sq_eLpNorm_two_eq_lintegral_ofReal_sq
        (fun y : EuclN =>
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      rw [h_eLp_sq]
    have h_sq_le :
        (eLpNorm
            (fun y : EuclN =>
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
      exact pow_le_pow_left' h_brg 2
    rw [← h_lp_sq]; exact h_sq_le
  have h_per_r : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          rIntegrand Idx Jdx y ∂(volume : Measure EuclN) =
        eLpNorm
            (fun y : EuclN =>
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    intro Idx Jdx
    have h_eLp_sq := sq_eLpNorm_two_eq_lintegral_ofReal_sq
      (fun y : EuclN =>
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
    have h_eq_lhs :
        ∫⁻ y,
            ENNReal.ofReal
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
            ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) =
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            rIntegrand Idx Jdx y ∂(volume : Measure EuclN) := rfl
    rw [h_eq_lhs] at h_eLp_sq
    exact h_eLp_sq.symm
  refine h_int_mono.trans ?_
  have h_f_total_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) ≤
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact h_per_f Idx Jdx
  have h_r_total_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rIntegrand Idx Jdx y ∂(volume : Measure EuclN)) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            eLpNorm
                (fun y : EuclN =>
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact h_per_r Idx Jdx
  set Xf : ℝ≥0∞ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ^ 2 with hXf_def
  set Xr : ℝ≥0∞ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      eLpNorm
          (fun y : EuclN =>
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 with hXr_def
  have h_C1_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C1 + C2) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hC2_nn)
  have h_C2_le : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C1 + C2) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hC1_nn)
  calc
    ENNReal.ofReal C1 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
      ENNReal.ofReal C2 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  rIntegrand Idx Jdx y ∂(volume : Measure EuclN))
        ≤ ENNReal.ofReal C1 * Xf + ENNReal.ofReal C2 * Xr := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_right h_f_total_le (ENNReal.ofReal C1)
          · exact le_of_eq (by rw [h_r_total_eq])
      _ ≤ ENNReal.ofReal (C1 + C2) * Xf + ENNReal.ofReal (C1 + C2) * Xr := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_left h_C1_le Xf
          · exact mul_le_mul_left h_C2_le Xr
      _ = ENNReal.ofReal (C1 + C2) * (Xf + Xr) := by
          rw [mul_add]

end Connection
end Integral
end DifferentialGeometry

end
