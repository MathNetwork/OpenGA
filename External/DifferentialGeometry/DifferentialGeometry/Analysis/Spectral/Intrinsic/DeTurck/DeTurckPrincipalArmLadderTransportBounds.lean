import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.EndoCovariantDerivativeSelfAdjoint
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotSwapPairingCalculus
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmConnLaplacianSelfAdjoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmIteratedCovGradJetBounds


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
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
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem arm_g0Term_abs_le_jetProduct (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0)
            (ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun| ≤
      C * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  set a : ℕ := n / 2 with ha_def
  set b : ℕ := n - n / 2 with hb_def
  set Gf : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hGf_def
  obtain ⟨CfL, hCfL_nn, hCfL⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ 2 b
  obtain ⟨CfR, hCfR_nn, hCfR⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ 2 a
  obtain ⟨CfG, hCfG_nn, hCfG⟩ :=
    armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ (2 + 1) (2 + 0) Gf
  refine ⟨CfL 0 * (CfR 0 * ∑ q ∈ Finset.range (2 * a + 1), CfG q), ?_, fun u₀ => ?_⟩
  · exact mul_nonneg (hCfL_nn 0)
      (mul_nonneg (hCfR_nn 0) (Finset.sum_nonneg (fun q _ => hCfG_nn q)))
  · set GT : SmoothCcTensor g₀ 0 (2 + 0) :=
      operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) Gf (covGrad (I := I) (M := M) g₀ 0 2 u₀)
      with hGT_def
    have hsym := oneMinusConnLapSmoothIter_l2Inner_sym_split (I := I) (M := M) g₀ 0 2 a b u₀ GT
    have hab : a + b = n := by omega
    rw [hab] at hsym
    rw [hsym]
    have hL : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 b u₀‖ ≤
        CfL 0 * ∑ q ∈ Finset.range (2 * b + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖ := by
      have h := hCfL 0 u₀
      simpa only [Nat.zero_add] using h
    have hR : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 a GT‖ ≤
        CfR 0 * ((∑ q ∈ Finset.range (2 * a + 1), CfG q) *
          ∑ k ∈ Finset.range (2 * a + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖) := by
      have h0 := hCfR 0 GT
      simp only [Nat.zero_add] at h0
      refine le_trans h0 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCfR_nn 0)
      have hq : ∀ q ∈ Finset.range (2 * a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q GT‖ ≤
            CfG q * ∑ k ∈ Finset.range (2 * a + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖ := by
        intro q hqmem
        rw [Finset.mem_range] at hqmem
        have hstep := hCfG q (covGrad (I := I) (M := M) g₀ 0 2 u₀)
        rw [← hGT_def] at hstep
        refine le_trans hstep ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCfG_nn q)
        refine le_trans (armJet_jetSum_mono (I := I) (M := M) g₀ (2 + 1)
          (show q + 1 ≤ 2 * a + 1 by omega) (covGrad (I := I) (M := M) g₀ 0 2 u₀)) ?_
        exact armJet_jetSum_covGrad_le (I := I) (M := M) g₀ 2 (2 * a + 1) u₀
      refine le_trans (Finset.sum_le_sum hq) ?_
      rw [← Finset.sum_mul]
    have habs := armJet_abs_pairing_le (I := I) (M := M) g₀ 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 b u₀)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 a GT)
    refine le_trans habs ?_
    have hLnn : 0 ≤ CfL 0 * ∑ q ∈ Finset.range (2 * b + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖ :=
      mul_nonneg (hCfL_nn 0) (Finset.sum_nonneg (fun q _ => norm_nonneg _))
    calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 b u₀‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 a GT‖
        ≤ (CfL 0 * ∑ q ∈ Finset.range (2 * b + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖) *
            (CfR 0 * ((∑ q ∈ Finset.range (2 * a + 1), CfG q) *
              ∑ k ∈ Finset.range (2 * a + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖)) :=
          mul_le_mul hL hR (norm_nonneg _) hLnn
      _ = (CfL 0 * (CfR 0 * ∑ q ∈ Finset.range (2 * a + 1), CfG q)) *
            ((∑ q ∈ Finset.range (2 * b + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖) *
              (∑ k ∈ Finset.range (2 * a + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖)) := by
          ring
      _ ≤ (CfL 0 * (CfR 0 * ∑ q ∈ Finset.range (2 * a + 1), CfG q)) *
            ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact armJet_jetProduct_le (I := I) (M := M) g₀ n (2 * b + 1) (2 * a + 2)
              (by omega) (by omega) (by omega) u₀
          · exact mul_nonneg (hCfL_nn 0)
              (mul_nonneg (hCfR_nn 0) (Finset.sum_nonneg (fun q _ => hCfG_nn q)))

omit [CompactSpace M] [I.Boundaryless] in
private theorem armLadder_rawConnLap_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (A + B) =
      rawTensorConnLapSmooth (I := I) g r s A + rawTensorConnLapSmooth (I := I) g r s B := by
  have h0 : rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A A
    rw [sub_self, sub_self] at h
    exact h
  have hAB : A + B = A - (0 - B) := by abel
  rw [hAB, rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A (0 - B),
    rawTensorConnLapSmooth_sub (I := I) (M := M) g r s 0 B, h0]
  abel

omit [CompactSpace M] [I.Boundaryless] in
private theorem armLadder_oneMinusConnLapSmooth_add (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A + B) =
      oneMinusConnLapSmooth (I := I) g r s A + oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [armLadder_rawConnLap_add (I := I) (M := M) g r s A B]
  abel

omit [CompactSpace M] [I.Boundaryless] in
private theorem armLadder_iterL_add (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s j (A + B) =
      oneMinusConnLapSmoothIter (I := I) g r s j A +
        oneMinusConnLapSmoothIter (I := I) g r s j B := by
  induction j with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih,
      armLadder_oneMinusConnLapSmooth_add (I := I) (M := M) g r s]

private theorem armLadder_covGrad_oneMinusConnLapSmooth (g : SmoothRiemannianMetric I M)
    (s : ℕ) (S : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 s (oneMinusConnLapSmooth (I := I) g 0 s S) =
      oneMinusConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) +
        pointwiseTensorCurv (I := I) (M := M) g s S := by
  have hcomm := pointwiseTensorCurv_commutator_eq (I := I) (M := M) g s S
  unfold oneMinusConnLapSmooth
  rw [covGrad_sub (I := I) (M := M) g 0 s S (rawTensorConnLapSmooth (I := I) g 0 s S)]
  rw [hcomm]
  abel

omit [CompactSpace M] [I.Boundaryless] in
private theorem armLadder_iterL_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 1 S = oneMinusConnLapSmooth (I := I) g r s S := by
  rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_zero]

theorem armLadder_covGrad_iterL_expansion (g : SmoothRiemannianMetric I M)
    (s : ℕ) (j : ℕ) :
    ∀ S : SmoothCcTensor g 0 s,
      covGrad (I := I) (M := M) g 0 s (oneMinusConnLapSmoothIter (I := I) g 0 s j S) =
        oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) j
            (covGrad (I := I) (M := M) g 0 s S) +
          ∑ i ∈ Finset.range j,
            oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g s
                (oneMinusConnLapSmoothIter (I := I) g 0 s (j - 1 - i) S)) := by
  induction j with
  | zero =>
    intro S
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ k ih =>
    intro S
    have hsplit : oneMinusConnLapSmoothIter (I := I) g 0 s (k + 1) S =
        oneMinusConnLapSmoothIter (I := I) g 0 s k (oneMinusConnLapSmooth (I := I) g 0 s S) := by
      rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 s k 1 S,
        armLadder_iterL_one (I := I) (M := M) g 0 s S]
    rw [hsplit, ih (oneMinusConnLapSmooth (I := I) g 0 s S)]
    rw [armLadder_covGrad_oneMinusConnLapSmooth (I := I) (M := M) g s S]
    rw [armLadder_iterL_add (I := I) (M := M) g 0 (s + 1) k
      (oneMinusConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S))
      (pointwiseTensorCurv (I := I) (M := M) g s S)]
    have hL : oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) k
        (oneMinusConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)) =
        oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) (k + 1)
          (covGrad (I := I) (M := M) g 0 s S) := by
      rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 (s + 1) k 1,
        armLadder_iterL_one (I := I) (M := M) g 0 (s + 1)]
    rw [hL]
    have hsum : ∑ i ∈ Finset.range k,
        oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g s
            (oneMinusConnLapSmoothIter (I := I) g 0 s (k - 1 - i)
              (oneMinusConnLapSmooth (I := I) g 0 s S))) =
        ∑ i ∈ Finset.range k,
          oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g s
              (oneMinusConnLapSmoothIter (I := I) g 0 s (k + 1 - 1 - i) S)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      have hidx : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [hidx, oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 s (k - 1 - i) 1 S,
        armLadder_iterL_one (I := I) (M := M) g 0 s S]
    rw [hsum]
    rw [Finset.sum_range_succ
      (fun i => oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
        (pointwiseTensorCurv (I := I) (M := M) g s
          (oneMinusConnLapSmoothIter (I := I) g 0 s (k + 1 - 1 - i) S))) k]
    rw [show k + 1 - 1 - k = 0 from by omega, oneMinusConnLapSmoothIter_zero]
    abel

theorem armLadder_pairing_transport (g : SmoothRiemannianMetric I M) (σ a r : ℕ)
    (hr : r ≤ a) (X Y : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ a X).toFun Y.toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 σ r Y).toFun := by
  have hsplit : oneMinusConnLapSmoothIter (I := I) g 0 σ a X =
      oneMinusConnLapSmoothIter (I := I) g 0 σ r
        (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X) := by
    rw [← oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 σ r (a - r) X]
    congr 1
    omega
  rw [hsplit]
  exact oneMinusConnLapSmoothIter_l2Inner_selfAdjoint (I := I) (M := M) g 0 σ r
    (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X) Y

theorem armLadder_pairing_abs_le_transport (g : SmoothRiemannianMetric I M)
    (σ a r : ℕ) (hr : r ≤ a) (X Y : SmoothCcTensor g 0 σ) :
    |tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ a X).toFun Y.toFun| ≤
      ‖oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X‖ *
        ‖oneMinusConnLapSmoothIter (I := I) g 0 σ r Y‖ := by
  rw [armLadder_pairing_transport (I := I) (M := M) g σ a r hr X Y]
  exact armJet_abs_pairing_le (I := I) (M := M) g σ
    (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X)
    (oneMinusConnLapSmoothIter (I := I) g 0 σ r Y)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem armAsm_l2Inner_zero_left (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (0 : SmoothCcTensor g 0 σ).toFun Z.toFun = 0 := by
  rw [SmoothCcTensor.toFun_zero]
  exact tensorL2Inner_zero_left (I := I) (M := M) g 0 σ Z.toFun

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem armAsm_l2Inner_zero_right (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun (0 : SmoothCcTensor g 0 σ).toFun = 0 := by
  rw [SmoothCcTensor.toFun_zero]
  exact tensorL2Inner_zero_right (I := I) (M := M) g 0 σ Z.toFun

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem armAsm_l2Inner_add_left (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (A B Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (A + B).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ A.toFun Z.toFun +
        tensorL2Inner (I := I) (M := M) g 0 σ B.toFun Z.toFun := by
  have hAB : A + B = A - (0 - B) := by abel
  rw [hAB, SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g 0 σ A (0 - B) Z,
    SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g 0 σ 0 B Z,
    armAsm_l2Inner_zero_left (I := I) (M := M) g σ Z]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem armAsm_l2Inner_add_right (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z A B : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun (A + B).toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun A.toFun +
        tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun B.toFun := by
  have hAB : A + B = A - (0 - B) := by abel
  rw [hAB, SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_right_smoothCc (I := I) (M := M) g 0 σ Z A (0 - B),
    SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_right_smoothCc (I := I) (M := M) g 0 σ Z 0 B,
    armAsm_l2Inner_zero_right (I := I) (M := M) g σ Z]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem armAsm_l2Inner_sum_left (g : SmoothRiemannianMetric I M) (σ c : ℕ)
    (f : ℕ → SmoothCcTensor g 0 σ) (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (∑ i ∈ Finset.range c, f i).toFun Z.toFun =
      ∑ i ∈ Finset.range c, tensorL2Inner (I := I) (M := M) g 0 σ (f i).toFun Z.toFun := by
  induction c with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
    exact armAsm_l2Inner_zero_left (I := I) (M := M) g σ Z
  | succ d ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      armAsm_l2Inner_add_left (I := I) (M := M) g σ (∑ i ∈ Finset.range d, f i) (f d) Z, ih]

theorem armAsm_sum_window_le (P w : ℕ) (φ A B : ℕ → ℝ)
    (hφ_nn : ∀ c, 0 ≤ φ c) (hB_nn : ∀ e, 0 ≤ B e)
    (h : ∀ c, c < P → A c ≤ φ c * ∑ e ∈ Finset.range (c + w + 1), B e) :
    ∑ c ∈ Finset.range P, A c ≤
      (∑ c ∈ Finset.range P, φ c) * ∑ e ∈ Finset.range (P + w), B e := by
  have hterm : ∀ c ∈ Finset.range P,
      A c ≤ φ c * ∑ e ∈ Finset.range (P + w), B e := by
    intro c hc
    rw [Finset.mem_range] at hc
    refine le_trans (h c hc) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hφ_nn c)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hB_nn e)
    exact Finset.range_subset_range.mpr (by omega)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

theorem armAsm_iterL_norm_le (g₀ : SmoothRiemannianMetric I M) (σ a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SmoothCcTensor g₀ 0 σ,
      ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ a v‖ ≤
        C * ∑ q ∈ Finset.range (2 * a + 1), ‖iteratedCovGrad (I := I) g₀ 0 σ q v‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ σ a
  refine ⟨Cf 0, hCf_nn 0, fun v => ?_⟩
  have h := hCf 0 v
  simpa only [Nat.zero_add, iteratedCovGrad_zero] using h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armAsm_shifted_jetSum_le (g₀ : SmoothRiemannianMetric I M) (base c : ℕ)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    ∑ a ∈ Finset.range c,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + base) a
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀)‖ ≤
      ∑ j ∈ Finset.range (c + base), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  have hterm : ∀ a ∈ Finset.range c,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + base) a
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (base + a) u₀‖ :=
    fun a _ => armJet_norm_comp (I := I) (M := M) g₀ 2 base a u₀
  rw [Finset.sum_congr rfl hterm]
  have hIco : ∑ a ∈ Finset.range c, ‖iteratedCovGrad (I := I) g₀ 0 2 (base + a) u₀‖ =
      ∑ b ∈ Finset.Ico base (base + c), ‖iteratedCovGrad (I := I) g₀ 0 2 b u₀‖ := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr ?_ (fun a _ => rfl)
    congr 1
    omega
  rw [hIco]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
  intro b hb
  rw [Finset.mem_Ico] at hb
  rw [Finset.mem_range]
  omega

omit [NeZero (Module.finrank ℝ E)] in
theorem armAsm_appCc_jet_window (g₀ : SmoothRiemannianMetric I M) (base c : ℕ)
    (Φ : SmoothCcTensor g₀ (2 + base) c) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 c p
          (operatorFieldApply (I := I) (M := M) g₀ (2 + base) c Φ
            (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ := armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ (2 + base) c Φ
  refine ⟨Cf, hCf_nn, fun u₀ p => ?_⟩
  refine le_trans (hCf p (iteratedCovGrad (I := I) g₀ 0 2 base u₀)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCf_nn p)
  have hsh := armAsm_shifted_jetSum_le (I := I) (M := M) g₀ base (p + 1) u₀
  rw [show p + 1 + base = p + base + 1 from by omega] at hsh
  exact hsh

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appFullSec_iteratedCovGrad_shiftedJetWindow_bound (g₀ : SmoothRiemannianMetric I M) (base c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) 0 (2 + base) c I) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 c p
          (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + base) c Q
            (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨cq, hcq_nn, hcq⟩ :=
    exists_appFullSec_iteratedCovGrad_l2_window_bound (I := I) (M := M) g₀ 0 (2 + base) c Q
  refine ⟨cq, hcq_nn, fun u₀ p => ?_⟩
  refine le_trans (hcq (iteratedCovGrad (I := I) g₀ 0 2 base u₀) p) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hcq_nn p)
  have hsh := armAsm_shifted_jetSum_le (I := I) (M := M) g₀ base (p + 1) u₀
  rw [show p + 1 + base = p + base + 1 from by omega] at hsh
  exact hsh

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appCc_appFullSec_iteratedCovGrad_jetWindow_bound (g₀ : SmoothRiemannianMetric I M)
    (base b2 c2 : ℕ) (Q : HomTensorRSField (E := E) (M := M) 0 (2 + base) b2 I)
    (Φ : SmoothCcTensor g₀ b2 c2) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 c2 p
          (operatorFieldApply (I := I) (M := M) g₀ b2 c2 Φ
            (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + base) b2 Q
              (iteratedCovGrad (I := I) g₀ 0 2 base u₀)))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ := armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ b2 c2 Φ
  obtain ⟨cq, hcq_nn, hcq⟩ :=
    exists_appFullSec_iteratedCovGrad_shiftedJetWindow_bound (I := I) (M := M) g₀ base b2 Q
  refine ⟨fun p => Cf p * ∑ e ∈ Finset.range (p + 1), cq e,
    fun p => mul_nonneg (hCf_nn p) (Finset.sum_nonneg fun e _ => hcq_nn e),
    fun u₀ p => ?_⟩
  refine le_trans (hCf p (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + base) b2 Q
    (iteratedCovGrad (I := I) g₀ 0 2 base u₀))) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hCf_nn p)
  have hwin := armAsm_sum_window_le (p + 1) base cq
    (fun e => ‖iteratedCovGrad (I := I) g₀ 0 b2 e
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + base) b2 Q
        (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
    hcq_nn (fun _ => norm_nonneg _) (fun e _ => hcq u₀ e)
  rw [show p + 1 + base = p + base + 1 from by omega] at hwin
  exact hwin

omit [NeZero (Module.finrank ℝ E)] in
theorem armAsm_covGrad_appCc_jet_window (g₀ : SmoothRiemannianMetric I M) (base : ℕ)
    (Φ : SmoothCcTensor g₀ (2 + base) (2 + base)) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 ((2 + base) + 1) p
          (covGrad (I := I) (M := M) g₀ 0 (2 + base)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
              (iteratedCovGrad (I := I) g₀ 0 2 base u₀)))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ :=
    armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
  refine ⟨fun p => Cf (1 + p), fun p => hCf_nn (1 + p), fun u₀ p => ?_⟩
  have hnc : ‖iteratedCovGrad (I := I) g₀ 0 ((2 + base) + 1) p
      (covGrad (I := I) (M := M) g₀ 0 (2 + base)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀)))‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + base) (1 + p)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖ :=
    armJet_norm_comp (I := I) (M := M) g₀ (2 + base) 1 p
      (operatorFieldApply (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
        (iteratedCovGrad (I := I) g₀ 0 2 base u₀))
  rw [hnc]
  refine le_trans (hCf (1 + p) (iteratedCovGrad (I := I) g₀ 0 2 base u₀)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCf_nn (1 + p))
  have hsh := armAsm_shifted_jetSum_le (I := I) (M := M) g₀ base (1 + p + 1) u₀
  rw [show 1 + p + 1 + base = p + base + 2 from by omega] at hsh
  exact hsh

theorem armAsm_abs_add4_sub_le (a b c d e : ℝ) :
    |a + b + c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc |a + b + c + d - e| = |a + b + c + d + -e| := by rw [sub_eq_add_neg]
    _ ≤ |a + b + c + d| + |-e| := abs_add_le _ _
    _ ≤ |a + b + c| + |d| + |-e| := add_le_add_left (abs_add_le _ _) _
    _ ≤ |a + b| + |c| + |d| + |-e| :=
        add_le_add_left (add_le_add_left (abs_add_le _ _) _) _
    _ ≤ |a| + |b| + |c| + |d| + |-e| :=
        add_le_add_left (add_le_add_left (add_le_add_left (abs_add_le _ _) _) _) _
    _ = |a| + |b| + |c| + |d| + |e| := by rw [abs_neg]

theorem armAsm_transport_pairing_jet_le (g₀ : SmoothRiemannianMetric I M)
    (σ a r dX dY NA NB : ℕ) (hr : r ≤ a)
    (hNA : 2 * (a - r) + dX ≤ NA) (hNB : 2 * r + dY ≤ NB)
    (cX cY : ℕ → ℝ) (hcX_nn : ∀ p, 0 ≤ cX p) (hcY_nn : ∀ p, 0 ≤ cY p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (X Y : SmoothCcTensor g₀ 0 σ),
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 σ p X‖ ≤
        cX p * ∑ j ∈ Finset.range (p + dX + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 σ p Y‖ ≤
        cY p * ∑ j ∈ Finset.range (p + dY + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      |tensorL2Inner (I := I) (M := M) g₀ 0 σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ a X).toFun Y.toFun| ≤
        C * ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := armAsm_iterL_norm_le (I := I) (M := M) g₀ σ (a - r)
  obtain ⟨CR, hCR_nn, hCR⟩ := armAsm_iterL_norm_le (I := I) (M := M) g₀ σ r
  refine ⟨(CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
      (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p),
    mul_nonneg (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcX_nn p))
      (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcY_nn p)),
    fun u₀ X Y hX hY => ?_⟩
  have hXb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (a - r) X‖ ≤
      (CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
        ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    refine le_trans (hCL X) ?_
    have h1 : ∑ p ∈ Finset.range (2 * (a - r) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 σ p X‖ ≤
        (∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          ∑ j ∈ Finset.range (2 * (a - r) + 1 + dX),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
      armAsm_sum_window_le (2 * (a - r) + 1) dX cX
        (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p X‖)
        (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
        hcX_nn (fun _ => norm_nonneg _) (fun p _ => hX p)
    refine le_trans (mul_le_mul_of_nonneg_left h1 hCL_nn) ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcX_nn p))
    exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
  have hYb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ r Y‖ ≤
      (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
        ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    refine le_trans (hCR Y) ?_
    have h1 : ∑ p ∈ Finset.range (2 * r + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 σ p Y‖ ≤
        (∑ p ∈ Finset.range (2 * r + 1), cY p) *
          ∑ j ∈ Finset.range (2 * r + 1 + dY),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
      armAsm_sum_window_le (2 * r + 1) dY cY
        (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p Y‖)
        (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
        hcY_nn (fun _ => norm_nonneg _) (fun p _ => hY p)
    refine le_trans (mul_le_mul_of_nonneg_left h1 hCR_nn) ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcY_nn p))
    exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
  refine le_trans
    (armLadder_pairing_abs_le_transport (I := I) (M := M) g₀ σ a r hr X Y) ?_
  calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (a - r) X‖ *
        ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ r Y‖
      ≤ ((CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        ((CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
        mul_le_mul hXb hYb (norm_nonneg _) (le_trans (norm_nonneg _) hXb)
    _ = (CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
        ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
        ring

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem armSwap_appFullSec_sub_right (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (A B : SmoothCcTensor g 0 (t + 2)) :
    homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F (A - B) =
      homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F A -
        homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F A -
      homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B).toSection x) =
    (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F A).toSection x -
      (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((A - B).toSection x : TensorRSSpace 0 (t + 2) I x) =
      A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  exact map_sub _ _ _

private theorem armSwap_oneMinusConnLapSmooth_comm (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (w : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b w)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a w)))
    (U : SmoothCcTensor g 0 (t + 2)) :
    oneMinusConnLapSmooth (I := I) g 0 (t + 2)
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) =
      homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (oneMinusConnLapSmooth (I := I) g 0 (t + 2) U) := by
  unfold oneMinusConnLapSmooth
  rw [appFullSec_swap_rawConnLap_comm (I := I) (M := M) g t F hF U,
    armSwap_appFullSec_sub_right (I := I) (M := M) g t F U
      (rawTensorConnLapSmooth (I := I) g 0 (t + 2) U)]

theorem armSwap_iterL_comm (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (w : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b w)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a w)))
    (k : ℕ) (U : SmoothCcTensor g 0 (t + 2)) :
    oneMinusConnLapSmoothIter (I := I) g 0 (t + 2) k
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) =
      homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (oneMinusConnLapSmoothIter (I := I) g 0 (t + 2) k U) := by
  induction k with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ d ih =>
    rw [oneMinusConnLapSmoothIter_succ, ih,
      armSwap_oneMinusConnLapSmooth_comm (I := I) (M := M) g t F hF
        (oneMinusConnLapSmoothIter (I := I) g 0 (t + 2) d U),
      oneMinusConnLapSmoothIter_succ]

omit [CompactSpace M] [I.Boundaryless] in
private theorem armLadder_oneMinusConnLapSmooth_sub (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A - B) =
      oneMinusConnLapSmooth (I := I) g r s A - oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A B]
  abel

omit [CompactSpace M] [I.Boundaryless] in
theorem armLadder_iterL_sub (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s j (A - B) =
      oneMinusConnLapSmoothIter (I := I) g r s j A -
        oneMinusConnLapSmoothIter (I := I) g r s j B := by
  induction j with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ d ih =>
    rw [oneMinusConnLapSmoothIter_succ, ih,
      armLadder_oneMinusConnLapSmooth_sub (I := I) (M := M) g r s,
      oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
