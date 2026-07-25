import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RoughLaplacianCometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SlotExtendCovariantParallelism
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem covGrad_appCc_cometricDoubleTrace_eq (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (W : SmoothCcTensor g₀ 0 (p + 2)) :
    covGrad (I := I) (M := M) g₀ 0 p
        (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) W) =
      operatorFieldApply (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
        (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p))
        (covGrad (I := I) (M := M) g₀ 0 (p + 2) W) := by
  rw [covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) W]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ p]
  exact add_eq_right.mpr (appCc_zero_left (I := I) (M := M) g₀ (p + 2) (p + 1) W)

theorem covGrad_covGrad_appCc_cometricDoubleTrace_eq (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (W : SmoothCcTensor g₀ 0 (p + 2)) :
    covGrad (I := I) (M := M) g₀ 0 (p + 1)
        (covGrad (I := I) (M := M) g₀ 0 p
          (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) W)) =
      operatorFieldApply (I := I) (M := M) g₀ (p + 2 + 1 + 1) (p + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
          (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)))
        (covGrad (I := I) (M := M) g₀ 0 (p + 2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 (p + 2) W)) := by
  rw [covGrad_appCc_cometricDoubleTrace_eq (I := I) (M := M) g₀ p W]
  rw [covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
    (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p))
    (covGrad (I := I) (M := M) g₀ 0 (p + 2) W)]
  rw [covGrad_slotExtend_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ (p + 2) p
    (cometricDoubleTraceField (I := I) g₀ p)
    (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ p)]
  exact add_eq_right.mpr (appCc_zero_left (I := I) (M := M) g₀ (p + 2 + 1) (p + 1 + 1)
    (covGrad (I := I) (M := M) g₀ 0 (p + 2) W))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_toModel_unitEval_gen
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g₀ 0 s) (x : M)
    (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s W x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma unitModel_appCc_cometricDoubleTrace_eq_dualTrace
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (W : SmoothCcTensor g₀ 0 (p + 2))
    (x : M) (v : Fin p → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ p
        (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (p + 2) W x
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (p + 2) I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g₀ p).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (p + 2) I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g₀ x)]
  rfl

private lemma secondCovDeriv_frame_unitEval_eq_iteratedCovGrad_gen
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 t) (x : M)
    (v : Fin t → TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g₀ 0 t
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => W.toSection z) x)
          (unitZeroSec (I := I) (M := M) x)) v =
      unitModel (I := I) (M := M) g₀ (t + 2) (iteratedCovGrad (I := I) g₀ 0 t 2 W) x
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v)) := by
  have hbridge := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (I := I) (M := M) g₀ t W
    (X := smoothOrthoFrame (I := I) g₀ x i)
    (Y := smoothOrthoFrame (I := I) g₀ x i)
    (smoothOrthoFrame_smooth (I := I) g₀ x i) (smoothOrthoFrame_smooth (I := I) g₀ x i) x v
  exact hbridge.symm

lemma unitModel_rawConnLap_eq_frame_sum_gen
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 t) (x : M)
    (v : Fin t → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ t (rawTensorConnLapSmooth (I := I) g₀ 0 t W) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (t + 2) (iteratedCovGrad (I := I) g₀ 0 t 2 W) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v)) := by
  classical
  rw [unitModel_eq_toModel_unitEval_gen]
  have hsec : (rawTensorConnLapSmooth (I := I) g₀ 0 t W).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g₀ 0 t
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => W.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g₀ 0 t W x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g₀ 0 t
        (fun z : M => W.toSection z) x]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        (rawTensorConnLapSmooth (I := I) g₀ 0 t W).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g₀ 0 t
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => W.toSection z) x)
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, ContinuousLinearMap.sum_apply]]
  rw [← Tensor0SSpace.toModelL_apply (s := t) (x := x),
    map_sum (Tensor0SSpace.toModelL t x)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  exact secondCovDeriv_frame_unitEval_eq_iteratedCovGrad_gen (I := I) g₀ t W x v i

theorem rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace_of_rank
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 t) :
    rawTensorConnLapSmooth (I := I) g₀ 0 t W =
      operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
        (iteratedCovGrad (I := I) g₀ 0 t 2 W) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_rawConnLap_eq_frame_sum_gen (I := I) g₀ t W x v,
    unitModel_appCc_cometricDoubleTrace_eq_dualTrace (I := I) g₀ t
      (iteratedCovGrad (I := I) g₀ 0 t 2 W) x v]
  exact (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometric_dualTrace_eq_orthoFrame_diag
    (I := I) g₀ (s := t) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (unitModel (I := I) (M := M) g₀ (t + 2) (iteratedCovGrad (I := I) g₀ 0 t 2 W) x) v).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_contract_covariant_eval (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          Tensor0SBundle.contract_covariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons ((v : TangentSpace I b) : E) m) := rfl

private lemma vecTail_cons_eq {α : Type*} {n : ℕ} (a : α) (w : Fin n → α) :
    Matrix.vecTail (Fin.cons a w) = w := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

theorem covDivergence_eq_cometricDoubleTrace_apply_covGrad
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) :
    covDivergence (I := I) (M := M) g₀ s V =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_appCc_cometricDoubleTrace_eq_dualTrace (I := I) g₀ s
    (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x v]
  rw [show ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x
        (Fin.cons (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) v)) from
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometric_dualTrace_eq_orthoFrame_diag
      (I := I) g₀ (s := s) x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (unitModel (I := I) (M := M) g₀ (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x) v]
  rw [unitModel_eq_toModel_unitEval_gen]
  have hsec : (covDivergence (I := I) (M := M) g₀ s V).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covDivergenceBilinear (I := I) (M := M) g₀ s V x
          (smoothOrthoFrame (I := I) g₀ x i x) (smoothOrthoFrame (I := I) g₀ x i x) := by
    rw [covDivergence_toSection_apply]
    rfl
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s) I x from
        (covDivergence (I := I) (M := M) g₀ s V).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          covDivergenceBilinear (I := I) (M := M) g₀ s V x
            (smoothOrthoFrame (I := I) g₀ x i x) (smoothOrthoFrame (I := I) g₀ x i x))
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, ContinuousLinearMap.sum_apply]]
  rw [← Tensor0SSpace.toModelL_apply (s := s) (x := x),
    map_sum (Tensor0SSpace.toModelL s x)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g₀ x i z)) x :=
    (smoothOrthoFrame_smooth (I := I) g₀ x i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g₀ s V x hSmooth_at hSmooth_at]
  rw [toModel_contract_covariant_eval (I := I) (M := M) s x
    (smoothOrthoFrame (I := I) g₀ x i x)
    ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
        (LeviCivita (I := I) g₀)).toFun (fun z : M => V.toSection z) x
      (smoothOrthoFrame (I := I) g₀ x i x))
    (unitZeroSec (I := I) (M := M) x) v]
  rw [show unitModel (I := I) (M := M) g₀ (s + 2)
      (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) v)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (covGrad (I := I) (M := M) g₀ 0 (s + 1) V).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) v)) from rfl]
  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g₀ (s + 1) V x
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) v))]
  simp only [vecTail_cons_eq, Fin.cons_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem l2Inner_sub_left_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  have hsub : (S₁.toFun - S₂.toFun) = S₁.toFun + (-1 : ℝ) • S₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S₂.toFun x) (T.toFun x)) := by
      funext x
      change tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • S₂.toFun x) (T.toFun x) = _
      rw [tensorInnerPointwise_smul_left]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun ((-1 : ℝ) • S₂.toFun) T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T) hint2,
    tensorL2Inner_smul_left]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem l2Inner_sub_right_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  have hsub : (T₁.toFun - T₂.toFun) = T₁.toFun + (-1 : ℝ) • T₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S T₂
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (T₂.toFun x)) := by
      funext x
      change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) ((-1 : ℝ) • T₂.toFun x) = _
      rw [tensorInnerPointwise_smul_right]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_right (I := I) (M := M) g r s S.toFun T₁.toFun ((-1 : ℝ) • T₂.toFun)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S T₁) hint2,
    tensorL2Inner_smul_right]
  ring

theorem rawTensorConnLapSmooth_l2Inner_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
  have hTv := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s T v
  have hvT := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s v T
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T).toFun (covGrad (I := I) (M := M) g r s v).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s v).toFun T.toFun
  rw [hsymm1, hvT] at hTv
  rw [← hsymm2]
  linarith [hTv]

theorem pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : SmoothCcTensor g 0 s) (Z : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s X).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g 0 s X.toFun
        (rawTensorConnLapSmooth (I := I) g 0 s (covDivergence (I := I) (M := M) g s Z) -
          covDivergence (I := I) (M := M) g s
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun := by
  classical
  have hptc : (pointwiseTensorCurv (I := I) (M := M) g s X).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s X)).toFun -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s X)).toFun := by
    unfold pointwiseTensorCurv
    rw [SmoothCcTensor.toFun_sub]
  have hK : (rawTensorConnLapSmooth (I := I) g 0 s (covDivergence (I := I) (M := M) g s Z) -
      covDivergence (I := I) (M := M) g s
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 s
          (covDivergence (I := I) (M := M) g s Z)).toFun -
        (covDivergence (I := I) (M := M) g s
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun :=
    SmoothCcTensor.toFun_sub _ _
  rw [hptc, hK]
  rw [l2Inner_sub_left_cc (I := I) (M := M) g 0 (s + 1)
    (rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s X))
    (covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s X)) Z]
  rw [l2Inner_sub_right_cc (I := I) (M := M) g 0 s X
    (rawTensorConnLapSmooth (I := I) g 0 s (covDivergence (I := I) (M := M) g s Z))
    (covDivergence (I := I) (M := M) g s (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z))]
  have h1 : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s X)).toFun Z.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s X.toFun
        (covDivergence (I := I) (M := M) g s
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun := by
    rw [rawTensorConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s X) Z]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g s X (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)
  have h2 : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s X)).toFun Z.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s X.toFun
        (rawTensorConnLapSmooth (I := I) g 0 s
          (covDivergence (I := I) (M := M) g s Z)).toFun := by
    rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g s (rawTensorConnLapSmooth (I := I) g 0 s X) Z]
    rw [rawTensorConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g 0 s
      X (covDivergence (I := I) (M := M) g s Z)]
  linarith [h1, h2]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma unitModel_appCc_slotExtend_slotExtend_cometric
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (U : SmoothCcTensor g₀ 0 (t + 4))
    (x : M) (a b : E) (v : Fin t → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ (t + 2)
        (operatorFieldApply (I := I) (M := M) g₀ (t + 4) (t + 2)
          (slotExtend (I := I) (M := M) g₀ (t + 2 + 1) (t + 1)
            (slotExtend (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)))
          U) x
        (Fin.cons a (Fin.cons b (fun j => (v j : E)))) =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (t + 4) U x
          (Fin.cons a (Fin.cons b
            (Fin.cons ((cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)) : TangentSpace I x) : E)
              (Fin.cons (((Module.finBasis ℝ E) k : E)) (fun j => (v j : E)))))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace (t + 4) I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (slotExtend (I := I) (M := M) g₀ (t + 2 + 1) (t + 1)
          (slotExtend (I := I) (M := M) g₀ (t + 2) t
            (cometricDoubleTraceField (I := I) g₀ t))).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 4) I x from
          U.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace (t + 4) I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (slotExtend (I := I) (M := M) g₀ (t + 2 + 1) (t + 1)
          (slotExtend (I := I) (M := M) g₀ (t + 2) t
            (cometricDoubleTraceField (I := I) g₀ t))).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 4) I x from
          U.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [slotExtend_toSection, slotExtendFib_apply_eval]
  rw [slotExtend_toSection, slotExtendFib_apply_eval]
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) t (cometricLmodel (I := I) g₀ x)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)]
  rfl

theorem iteratedCovGrad_two_appCc_cometricDoubleTrace_eq
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (W : SmoothCcTensor g₀ 0 (p + 2)) :
    iteratedCovGrad (I := I) g₀ 0 p 2
        (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) W) =
      operatorFieldApply (I := I) (M := M) g₀ (p + 2 + 1 + 1) (p + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
          (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)))
        (iteratedCovGrad (I := I) g₀ 0 (p + 2) 2 W) :=
  covGrad_covGrad_appCc_cometricDoubleTrace_eq (I := I) (M := M) g₀ p W

theorem rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 (t + 2)) :
    rawTensorConnLapSmooth (I := I) g₀ 0 t
        (operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t) W) =
      operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
        (rawTensorConnLapSmooth (I := I) g₀ 0 (t + 2) W) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_rawConnLap_eq_frame_sum_gen (I := I) g₀ t
    (operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t) W) x v]
  rw [unitModel_appCc_cometricDoubleTrace_eq_dualTrace (I := I) g₀ t
    (rawTensorConnLapSmooth (I := I) g₀ 0 (t + 2) W) x v]
  have hlhs : ∀ i : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ (t + 2)
          (iteratedCovGrad (I := I) g₀ 0 t 2
            (operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t) W)) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v)) =
        ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ (t + 4)
            (iteratedCovGrad (I := I) g₀ 0 (t + 2) 2 W) x
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
                (Fin.cons ((cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)) : TangentSpace I x) : E)
                  (Fin.cons (((Module.finBasis ℝ E) k : E)) (fun j => (v j : E)))))) := by
    intro i
    rw [iteratedCovGrad_two_appCc_cometricDoubleTrace_eq (I := I) (M := M) g₀ t W]
    exact unitModel_appCc_slotExtend_slotExtend_cometric (I := I) (M := M) g₀ t
      (iteratedCovGrad (I := I) g₀ 0 (t + 2) 2 W) x
      ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
      ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) v
  have hrhs : ∀ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ (t + 2)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (t + 2) W) x
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) =
        ∑ i : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ (t + 4)
            (iteratedCovGrad (I := I) g₀ 0 (t + 2) 2 W) x
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
                (Fin.cons (cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v)))) := by
    intro k
    exact unitModel_rawConnLap_eq_frame_sum_gen (I := I) g₀ (t + 2) W x
      (Fin.cons (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) v))
  rw [Finset.sum_congr rfl (fun i _ => hlhs i), Finset.sum_congr rfl (fun k _ => hrhs k)]
  rw [Finset.sum_comm]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem appCc_sub_right_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (A B : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (A - B) =
      operatorFieldApply (I := I) (M := M) g r s Φ A - operatorFieldApply (I := I) (M := M) g r s Φ B := by
  have hAB : A - B = A + (-1 : ℝ) • B := by
    rw [neg_one_smul]
    exact sub_eq_add_neg A B
  rw [hAB, appCc_add_right (I := I) (M := M) g r s Φ A ((-1 : ℝ) • B),
    appCc_smul_right (I := I) (M := M) g r s (-1 : ℝ) Φ B,
    neg_one_smul, ← sub_eq_add_neg]

theorem rawConnLap_covDivergence_commutator_eq_appCc_pointwiseTensorCurv
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (Z : SmoothCcTensor g₀ 0 (s + 1)) :
    rawTensorConnLapSmooth (I := I) g₀ 0 s (covDivergence (I := I) (M := M) g₀ s Z) -
        covDivergence (I := I) (M := M) g₀ s
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) Z) := by
  have h1 : rawTensorConnLapSmooth (I := I) g₀ 0 s (covDivergence (I := I) (M := M) g₀ s Z) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) Z)) := by
    rw [covDivergence_eq_cometricDoubleTrace_apply_covGrad (I := I) (M := M) g₀ s Z]
    exact rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm (I := I) (M := M) g₀ s
      (covGrad (I := I) (M := M) g₀ 0 (s + 1) Z)
  have h2 : covDivergence (I := I) (M := M) g₀ s
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (covGrad (I := I) (M := M) g₀ 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z)) :=
    covDivergence_eq_cometricDoubleTrace_apply_covGrad (I := I) (M := M) g₀ s
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z)
  rw [h1, h2]
  rw [← appCc_sub_right_cc (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_iteratedCovGrad_comp_cc (g : SmoothRiemannianMetric I M) (s j i : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ := by
  have hsq : ‖iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M), SmoothCcTensor.norm_def (I := I) (M := M),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0
        ((s + j) + i)
        (iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0
        (s + (j + i)) (iteratedCovGrad (I := I) g 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g 0 s j i S x
  have ha : (0 : ℝ) ≤
      ‖iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)‖ :=
    norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ := norm_nonneg _
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, hsq]

theorem exists_iteratedCovGrad_covDivergence_l2_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)),
        ‖iteratedCovGrad (I := I) g₀ 0 s p (covDivergence (I := I) (M := M) g₀ s V)‖ ≤
          K p * ∑ k ∈ Finset.range (p + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) k V‖ := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_appCc_iteratedCovGrad_l2_window_bound (I := I) (M := M) g₀ (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s)
  refine ⟨cc, hcc_nn, fun p V => ?_⟩
  rw [covDivergence_eq_cometricDoubleTrace_apply_covGrad (I := I) (M := M) g₀ s V]
  refine le_trans (hcc (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) p) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hcc_nn p)
  have hterm : ∀ i ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 2) i (covGrad (I := I) (M := M) g₀ 0 (s + 1) V)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (1 + i) V‖ := by
    intro i _
    have h0 : covGrad (I := I) (M := M) g₀ 0 (s + 1) V =
        iteratedCovGrad (I := I) g₀ 0 (s + 1) 1 V := rfl
    rw [h0]
    exact norm_iteratedCovGrad_comp_cc (I := I) (M := M) g₀ (s + 1) 1 i V
  rw [Finset.sum_congr rfl hterm]
  have hreindex : ∑ i ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (1 + i) V‖ =
      ∑ i ∈ Finset.range (p + 1), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (i + 1) V‖ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.add_comm 1 i]
  rw [hreindex]
  have hshift := Finset.sum_range_succ'
    (fun k => ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) k V‖) (p + 1)
  have h0nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) 0 V‖ := norm_nonneg _
  linarith [hshift]

section CurvatureCommutatorL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (Z : SmoothCcTensor g₀ 0 (s + 1)),
        ‖iteratedCovGrad (I := I) g₀ 0 s p
            (rawTensorConnLapSmooth (I := I) g₀ 0 s (covDivergence (I := I) (M := M) g₀ s Z) -
              covDivergence (I := I) (M := M) g₀ s
                (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z))‖ ≤
          K p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) a Z‖ := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_appCc_iteratedCovGrad_l2_window_bound (I := I) (M := M) g₀ (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s)
  obtain ⟨Kp, hKp_nn, hKp⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (s + 1)
  refine ⟨fun p => cc p * ∑ i ∈ Finset.range (p + 1), Kp i,
    fun p => mul_nonneg (hcc_nn p) (Finset.sum_nonneg (fun i _ => hKp_nn i)),
    fun p Z => ?_⟩
  rw [rawConnLap_covDivergence_commutator_eq_appCc_pointwiseTensorCurv (I := I) (M := M) g₀ s Z]
  refine le_trans (hcc (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) Z) p) ?_
  have hJ_nn : (0 : ℝ) ≤ ∑ a ∈ Finset.range (p + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) a Z‖ :=
    Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hterm : ∀ i ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 2) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) Z)‖ ≤
        Kp i * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) a Z‖ := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine le_trans (hKp i Z) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKp_nn i)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => norm_nonneg _)
    exact Finset.range_subset_range.mpr (by omega)
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (hcc_nn p)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

end CurvatureCommutatorL2

set_option backward.isDefEq.respectTransparency false in

theorem covDiv_appCc (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 1 1) (W : SmoothCcTensor g₀ 0 1) :
    covDivergence (I := I) (M := M) g₀ 0
        (operatorFieldApply (I := I) (M := M) g₀ 1 1 Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ 1 0
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 0
            (cometricDoubleTraceField (I := I) g₀ 0)
            (covGrad (I := I) (M := M) g₀ 1 1 Φ)) W +
        operatorFieldApply (I := I) (M := M) g₀ 2 0
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 0
            (cometricDoubleTraceField (I := I) g₀ 0)
            (slotExtend (I := I) (M := M) g₀ 1 1 Φ))
          (covGrad (I := I) (M := M) g₀ 0 1 W) := by
  rw [covDivergence_eq_cometricDoubleTrace_apply_covGrad, covGrad_operatorFieldApply_eq, appCc_add_right]
  rw [appCc_assoc, appCc_assoc]


end Connection
end Integral
end DifferentialGeometry

end
