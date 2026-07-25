import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnLapCommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.ChartH2GardingConstant
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Tensor0SBundle in
private lemma bal_rawLap_frame_sum_eval (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) (D : Tensor0SSpace r I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (iteratedCovGrad (I := I) g r s 2 Φ).toSection x) D)
          (Fin.cons ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E) m)) := by
  classical
  have hsec : (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => Φ.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s Φ x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s
        (fun z : M => Φ.toSection z) x]
  have happ : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x) D =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => Φ.toSection z) x) D := by
    rw [hsec, ContinuousLinearMap.sum_apply]
  rw [happ, toModel_sum_eval]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (iteratedCovGrad (I := I) g r s 2 Φ).toSection x =
      (covGrad (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s Φ)).toSection x from rfl]
  exact (secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r s Φ
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i)
    x D m).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Tensor0SBundle in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bal_appCcRS_cometric_eval (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (K : SmoothCcTensor g r (s + 2)) (x : M) (D : Tensor0SSpace r I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
            (DeTurck.cometricDoubleTraceField (I := I) g s) K).toSection x) D) m =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            K.toSection x) D)
          (Fin.cons (DeTurck.cometricLmodel (I := I) g x
              (model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m)) := by
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
          (DeTurck.cometricDoubleTraceField (I := I) g s) K).toSection x) D =
      DeTurck.cometricDoubleTraceFib (I := I) g s x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          K.toSection x) D) from rfl]
  rw [DeTurck.cometricDoubleTraceFib_toModel]
  exact DeTurck.modelDoubleTrace_apply (E := E) s (DeTurck.cometricLmodel (I := I) g x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        K.toSection x) D)) m

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Tensor0SBundle in
private lemma bal_rawLap_toSection_eq_cometric (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x =
      (ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
        (DeTurck.cometricDoubleTraceField (I := I) g s)
        (iteratedCovGrad (I := I) g r s 2 Φ)).toSection x := by
  classical
  apply tensorRS_eq_of_toModel_eval_eq
  intro D m
  refine (bal_rawLap_frame_sum_eval (I := I) g r s Φ x D m).trans ?_
  refine Eq.trans ?_ (bal_appCcRS_cometric_eval (I := I) g r s
    (iteratedCovGrad (I := I) g r s 2 Φ) x D m).symm
  exact (DeTurck.cometric_dualTrace_eq_orthoFrame_diag (I := I) g (s := s) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (iteratedCovGrad (I := I) g r s 2 Φ).toSection x) D)) m).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem rawTensorConnLapSmooth_eq_appCcRS_cometricDoubleTrace_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s Φ =
      ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s (DeTurck.cometricDoubleTraceField (I := I) g s)
        (iteratedCovGrad (I := I) g r s 2 Φ) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact bal_rawLap_toSection_eq_cometric (I := I) g r s Φ x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma bal_appCc_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (A B : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (A - B) =
      operatorFieldApply (I := I) (M := M) g r s Φ A - operatorFieldApply (I := I) (M := M) g r s Φ B := by
  have hAB : A - B = A + (-1 : ℝ) • B := by
    rw [neg_one_smul]
    exact sub_eq_add_neg A B
  rw [hAB, appCc_add_right (I := I) (M := M) g r s Φ A ((-1 : ℝ) • B),
    appCc_smul_right (I := I) (M := M) g r s (-1 : ℝ) Φ B,
    neg_one_smul, ← sub_eq_add_neg]

omit [CompactSpace M] [I.Boundaryless] in
lemma oneMinusConnLapSmoothIter_sub (g : SmoothRiemannianMetric I M) (r s : ℕ) (q : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s q (A - B) =
      oneMinusConnLapSmoothIter (I := I) g r s q A -
        oneMinusConnLapSmoothIter (I := I) g r s q B := by
  induction q with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih]
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel

omit [CompactSpace M] [I.Boundaryless] in
private lemma bal_lap_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (A + B) =
      rawTensorConnLapSmooth (I := I) g r s A + rawTensorConnLapSmooth (I := I) g r s B := by
  have h0 : rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
    have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A A
    rw [sub_self, sub_self] at this
    exact this
  have hneg : rawTensorConnLapSmooth (I := I) g r s (-B) =
      -rawTensorConnLapSmooth (I := I) g r s B := by
    have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s 0 B
    rw [zero_sub, h0, zero_sub] at this
    exact this
  have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A (-B)
  rw [sub_neg_eq_add, hneg, sub_neg_eq_add] at this
  exact this

omit [CompactSpace M] [I.Boundaryless] in
private lemma bal_P_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A + B) =
      oneMinusConnLapSmooth (I := I) g r s A + oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [bal_lap_add]
  abel

private lemma bal_peel (Φ : SmoothCcTensor g₀ 2 2) (W : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmooth (I := I) g₀ 0 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmooth (I := I) g₀ 2 2 Φ) W +
        (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
          - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (slotExtend (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ))
                (covGrad (I := I) (M := M) g₀ 0 2 W))
          - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                  (slotExtend (I := I) (M := M) g₀ 2 2 Φ))
                (covGrad (I := I) (M := M) g₀ 0 2 W))) := by
  have hlap : operatorFieldApply (I := I) (M := M) g₀ 2 2 (rawTensorConnLapSmooth (I := I) g₀ 2 2 Φ) W =
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 2)
          (covGrad (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ)) W) := by
    rw [rawTensorConnLapSmooth_eq_appCcRS_cometricDoubleTrace_rs (I := I) (M := M) g₀ 2 2 Φ]
    rw [show iteratedCovGrad (I := I) g₀ 2 2 2 Φ =
        covGrad (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ) from rfl]
    exact (SmoothCcTensor.ext_iff.mpr rfl).symm
  have hpeel := rawTensorConnLap_appCc_comm_of_rank (I := I) g₀ 2 2 Φ W
  unfold oneMinusConnLapSmooth
  rw [hpeel, appCc_sub_left (I := I) (M := M) g₀ 2 2 Φ
    (rawTensorConnLapSmooth (I := I) g₀ 2 2 Φ) W, hlap]
  abel

lemma bal_transport (Φ : SmoothCcTensor g₀ 2 2) (W : SmoothCcTensor g₀ 0 2) (p : ℕ) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W +
        ∑ q ∈ Finset.range p, oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
                  (covGrad (I := I) (M := M) g₀ 0 2 W))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
                  (covGrad (I := I) (M := M) g₀ 0 2 W))) := by
  classical
  set Efun : ℕ → SmoothCcTensor g₀ 0 2 := fun q =>
    -(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
            (covGrad (I := I) (M := M) g₀ 0 2 W))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
            (covGrad (I := I) (M := M) g₀ 0 2 W)) with hEfun
  induction p with
  | zero =>
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ p ih =>
    have hPhom : ∀ (A B : SmoothCcTensor g₀ 0 2),
        oneMinusConnLapSmooth (I := I) g₀ 0 2 (A + B) =
          oneMinusConnLapSmooth (I := I) g₀ 0 2 A +
            oneMinusConnLapSmooth (I := I) g₀ 0 2 B :=
      fun A B => bal_P_add (I := I) (M := M) g₀ 0 2 A B
    have hpeelp := bal_peel (I := I) (M := M) g₀
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W
    calc oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1)
          (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W) = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W)) := by
          rw [oneMinusConnLapSmoothIter_succ]
      _ = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W +
              ∑ q ∈ Finset.range p,
                oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [ih]
      _ = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [hPhom]
          congr 1
          exact map_sum (AddMonoidHom.mk' (oneMinusConnLapSmooth (I := I) g₀ 0 2)
            (fun A B => hPhom A B)) (fun q => oneMinusConnLapSmoothIter (I := I) g₀ 0 2
              (p - 1 - q) (Efun q)) (Finset.range p)
      _ = (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W + Efun p) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [hpeelp, ← oneMinusConnLapSmoothIter_succ (I := I) g₀ 2 2 p Φ]
      _ = (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W + Efun p) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1 - 1 - q) (Efun q) := by
          congr 1
          refine Finset.sum_congr rfl (fun q hq => ?_)
          have hqlt : q < p := Finset.mem_range.mp hq
          rw [← oneMinusConnLapSmoothIter_succ (I := I) g₀ 0 2 (p - 1 - q) (Efun q),
            show p - 1 - q + 1 = p + 1 - 1 - q from by omega]
      _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W +
            ∑ q ∈ Finset.range (p + 1),
              oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1 - 1 - q) (Efun q) := by
          rw [Finset.sum_range_succ,
            show p + 1 - 1 - p = 0 from by omega, oneMinusConnLapSmoothIter_zero]
          abel

end BalLadder

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
