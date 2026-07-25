import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreen
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIdentity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def frameVF
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  chartFrameNormGlobalSmooth (I := I) (M := M) g α i

def frameDirGradPairing
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  tensorInnerScalar (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
    (covDerivAlongVFSection (I := I) (M := M) g v.toSection (frameVF (I := I) (M := M) g α i))

def frameDirSecondCovDerivPairing
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  tensorInnerScalar (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
      (frameVF (I := I) (M := M) g α i))
    v.toSection

def frameDirDivergencePairing
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun b =>
    tensorInnerScalar (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
        v.toSection b
      * divergence_g (I := I) g (frameVF (I := I) (M := M) g α i) b

def frameDirWeightDerivPairing
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun b =>
    tensorInnerScalar (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
        v.toSection b
      * tangentSectionAction (I := I) (frameVF (I := I) (M := M) g α i)
          ((chartAtlasPOU I M α : M → ℝ)) b

omit [I.Boundaryless] in
private lemma perDirCross_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (frameDirGradPairing (I := I) (M := M) g T v α i) :=
  (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 _ _).continuous

omit [I.Boundaryless] in
private lemma perDirSecond_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i) :=
  (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 _ _).continuous

omit [I.Boundaryless] in
private lemma perDirInner_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (tensorInnerScalar (I := I) (M := M) g 0 2
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection (frameVF (I := I) (M := M) g α i))
      v.toSection) :=
  (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 _ _).continuous

private lemma perDirDiv_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (frameDirDivergencePairing (I := I) (M := M) g T v α i) :=
  (perDirInner_continuous (I := I) (M := M) g T v α i).mul
    (divergence_g_contMDiff (I := I) g (frameVF (I := I) (M := M) g α i)).continuous

private lemma perDirWeight_continuous
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Continuous (frameDirWeightDerivPairing (I := I) (M := M) g T v α i) :=
  (perDirInner_continuous (I := I) (M := M) g T v α i).mul
    (tangentSectionAction_contMDiff (I := I) (frameVF (I := I) (M := M) g α i)
      (chartAtlasPOU I M α).contMDiff).continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma perDir_integrable_of_continuous
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    (I := I) g hf (HasCompactSupport.of_compactSpace _)

private theorem tensorCovDerivPointwiseInner_eq_perDirCross_sum_on_support
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        frameDirGradPairing (I := I) (M := M) g T v α i b := by
  classical
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j =>
      chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
        (I := I) (M := M) g α hb i j
  rw [tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two
    (I := I) (M := M) g T v b
    (fun i : Fin (Module.finrank ℝ E) =>
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
    hB_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold frameDirGradPairing frameVF
  rw [tensorInnerScalar_apply,
    tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
      (covDerivAlongVFSection (I := I) (M := M) g v.toSection
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i)) b]
  rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g T.toSection
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b,
    toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g v.toSection
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b]
  rfl

private theorem integral_pou_perDirCross_eq
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∫ b, (chartAtlasPOU I M α : M → ℝ) b * frameDirGradPairing (I := I) (M := M) g T v α i b
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -(∫ b, (chartAtlasPOU I M α : M → ℝ) b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ b, (chartAtlasPOU I M α : M → ℝ) b * frameDirDivergencePairing (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ b, frameDirWeightDerivPairing (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hB_def
  set ρ : M → ℝ := (chartAtlasPOU I M α : M → ℝ) with hρ_def
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := (chartAtlasPOU I M α).contMDiff
  have hIBP := integral_weighted_secondOrder_combined_eq_neg_weightDeriv
    (I := I) (M := M) g T.toSection v.toSection B ρ hρ
  have hLHS_pt : ∀ b : M,
      ρ b * (covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 v.toSection b))
            + covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) b))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v.toSection B b))
            + tensorInnerScalar (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection b
              * divergence_g (I := I) g B b) =
        ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
          + ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b
          + ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b := by
    intro b
    have hA : covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 v.toSection b)) =
        frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b := by
      unfold frameDirSecondCovDerivPairing frameVF
      rw [tensorInnerScalar_apply,
        tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
          v.toSection b]
      rw [hB_def]
      rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b]
      rfl
    have hC : covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g b
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2
                  (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) b))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v.toSection B b)) =
        frameDirGradPairing (I := I) (M := M) g T v α i b := by
      unfold frameDirGradPairing frameVF
      rw [tensorInnerScalar_apply,
        tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T.toSection
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i))
          (covDerivAlongVFSection (I := I) (M := M) g v.toSection
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i)) b]
      rw [hB_def]
      rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g T.toSection
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b,
        toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g v.toSection
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i) b]
      rfl
    have hD : tensorInnerScalar (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection b
              * divergence_g (I := I) g B b =
        frameDirDivergencePairing (I := I) (M := M) g T v α i b := by
      unfold frameDirDivergencePairing frameVF; rw [hB_def]
    rw [hA, hC, hD]; ring
  have hRHS_pt : ∀ b : M,
      tensorInnerScalar (I := I) (M := M) g 0 2
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection b
          * tangentSectionAction (I := I) B ρ b =
        frameDirWeightDerivPairing (I := I) (M := M) g T v α i b := by
    intro b; unfold frameDirWeightDerivPairing frameVF; rw [hB_def, hρ_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hLHS_pt)] at hIBP
  rw [integral_congr_ae (Filter.Eventually.of_forall hRHS_pt)] at hIBP
  have hρ_cont : Continuous ρ := hρ.continuous
  have h_int_second : Integrable
      (fun b : M => ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b) μ :=
    perDir_integrable_of_continuous (I := I) g
      (hρ_cont.mul (perDirSecond_continuous (I := I) (M := M) g T v α i))
  have h_int_cross : Integrable
      (fun b : M => ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b) μ :=
    perDir_integrable_of_continuous (I := I) g
      (hρ_cont.mul (perDirCross_continuous (I := I) (M := M) g T v α i))
  have h_int_div : Integrable
      (fun b : M => ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b) μ :=
    perDir_integrable_of_continuous (I := I) g
      (hρ_cont.mul (perDirDiv_continuous (I := I) (M := M) g T v α i))
  have hadd1 :
      ∫ b, ((ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
              + ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b)
            + ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b) ∂μ =
        (∫ b, (ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
              + ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b) ∂μ)
          + (∫ b, ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b ∂μ) :=
    integral_add (μ := μ)
      (f := fun b : M => ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
              + ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b)
      (g := fun b : M => ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b)
      (h_int_second.add h_int_cross) h_int_div
  have hadd2 :
      ∫ b, (ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
              + ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b) ∂μ =
        (∫ b, ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b ∂μ)
          + (∫ b, ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b ∂μ) :=
    integral_add (μ := μ)
      (f := fun b : M => ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b)
      (g := fun b : M => ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b)
      h_int_second h_int_cross
  have h3 :
      ∫ b, ((ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
            + ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b)
            + ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b) ∂μ =
        (∫ b, ρ b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b ∂μ)
        + (∫ b, ρ b * frameDirGradPairing (I := I) (M := M) g T v α i b ∂μ)
        + (∫ b, ρ b * frameDirDivergencePairing (I := I) (M := M) g T v α i b ∂μ) := by
    rw [hadd1, hadd2]
  rw [h3] at hIBP
  linarith [hIBP]

private theorem pou_tensorCovDerivPointwiseInner_eq_perDirCross_sum
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) (b : M) :
    (chartAtlasPOU I M α : M → ℝ) b
        * tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      (chartAtlasPOU I M α : M → ℝ) b
        * ∑ i : Fin (Module.finrank ℝ E), frameDirGradPairing (I := I) (M := M) g T v α i b := by
  classical
  by_cases hb_supp : b ∈ tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have hb_chartSrc : b ∈ (chartAt H α).source :=
      (chartAtlasPOU_isSubordinate (I := I) (M := M) α) hb_supp
    have hb_extSrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source]; exact hb_chartSrc
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]; exact hb_extSrc
    have hb_inter : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α := ⟨hb_supp, hb_good⟩
    rw [tensorCovDerivPointwiseInner_eq_perDirCross_sum_on_support
      (I := I) (M := M) g T v α hb_inter]
  · have hp0 : (chartAtlasPOU I M α : M → ℝ) b = 0 :=
      image_eq_zero_of_notMem_tsupport hb_supp
    rw [hp0, zero_mul, zero_mul]

private theorem integral_pou_tensorCovDerivPointwiseInner_eq_frame_sum
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) :
    ∫ b, (chartAtlasPOU I M α : M → ℝ) b
          * tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ b, (chartAtlasPOU I M α : M → ℝ) b * frameDirGradPairing (I := I) (M := M) g T v α i b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (pou_tensorCovDerivPointwiseInner_eq_perDirCross_sum (I := I) (M := M) g T v α))]
  have hdist : ∀ b : M,
      (chartAtlasPOU I M α : M → ℝ) b
          * ∑ i : Fin (Module.finrank ℝ E), frameDirGradPairing (I := I) (M := M) g T v α i b =
        ∑ i : Fin (Module.finrank ℝ E),
          (chartAtlasPOU I M α : M → ℝ) b * frameDirGradPairing (I := I) (M := M) g T v α i b := by
    intro b; rw [Finset.mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdist)]
  have hρ_cont : Continuous ((chartAtlasPOU I M α : M → ℝ)) :=
    (chartAtlasPOU I M α).contMDiff.continuous
  refine MeasureTheory.integral_finset_sum (Finset.univ) (fun i _ => ?_)
  exact perDir_integrable_of_continuous (I := I) g
    (hρ_cont.mul (perDirCross_continuous (I := I) (M := M) g T v α i))

theorem integral_pou_tensorCovDerivPointwiseInner_eq_neg_second_div_weight
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (α : M) :
    ∫ b, (chartAtlasPOU I M α : M → ℝ) b
          * tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -(∑ i : Fin (Module.finrank ℝ E),
          ∫ b, (chartAtlasPOU I M α : M → ℝ) b * frameDirSecondCovDerivPairing (I := I) (M := M) g T v α i b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∑ i : Fin (Module.finrank ℝ E),
          ∫ b, (chartAtlasPOU I M α : M → ℝ) b * frameDirDivergencePairing (I := I) (M := M) g T v α i b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∑ i : Fin (Module.finrank ℝ E),
          ∫ b, frameDirWeightDerivPairing (I := I) (M := M) g T v α i b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  rw [integral_pou_tensorCovDerivPointwiseInner_eq_frame_sum (I := I) (M := M) g T v α]
  rw [Finset.sum_congr rfl (fun i _ =>
    integral_pou_perDirCross_eq (I := I) (M := M) g T v α i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end Connection
end Integral
end DifferentialGeometry

end
