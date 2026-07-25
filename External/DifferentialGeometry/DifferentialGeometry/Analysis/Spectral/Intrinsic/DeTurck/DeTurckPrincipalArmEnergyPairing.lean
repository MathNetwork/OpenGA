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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmResidualDivergenceSplit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmLadderTransportBounds


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

omit [BoundarylessManifold I M] in
theorem tensorL2Inner_eq_tsum_l2Coeff_cross_arm
    (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner_eq]
  have h_par := b.tsum_inner_mul_inner (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← h_par]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 A) i,
    tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 B) i]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) = ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from
    real_inner_comm _ _]

private theorem spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (u₀ : SmoothCcTensor g₀ 0 2) (A : SmoothCcTensor g₀ 0 2) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) A).coeff i) =
      tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        A.toFun := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [tensorL2Inner_eq_tsum_l2Coeff_cross_arm (I := I) (M := M) g₀
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀) A]
  refine tsum_congr (fun i => ?_)
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ h_compact u₀ i n]
  have hweight : tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight]
  ring

private noncomputable def negGInvDiffSlotApplied
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) : TensorRSSpace 0 (s + 1) I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (-metricComparisonDiffEndo (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem slotInsertEndoFib_neg_left (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (-Λ) =
      - slotInsertEndoFib (I := I) (M := M) s k x Λ := by
  rw [show (-Λ) = (-1 : ℝ) • Λ from by rw [neg_one_smul],
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ, neg_one_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem negGInvDiffSlotApplied_eq_neg
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    negGInvDiffSlotApplied (I := I) g₀ g₁ s x W =
      - gInvDiffSlotApplied (I := I) g₀ g₁ s x W := by
  rw [negGInvDiffSlotApplied, gInvDiffSlotApplied,
    slotInsertEndoFib_neg_left (I := I) (M := M) (s + 1) 0 x
      (metricComparisonDiffEndo (I := I) g₀ g₁ x),
    ContinuousLinearMap.neg_comp]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem toModel_negGInvDiffSlotApplied_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
        (negGInvDiffSlotApplied (I := I) g₀ g₁ s x W) =
      - TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ s x W) := by
  rw [negGInvDiffSlotApplied_eq_neg (I := I) g₀ g₁ s x W, TensorRSSpace.toModel_neg]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem negGInvDiffRaisedEndo_g0_self_adjoint
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x ((-metricComparisonDiffEndo (I := I) g₀ g₁ x) a) b
      = g₀.inner x a ((-metricComparisonDiffEndo (I := I) g₀ g₁ x) b) := by
  simp only [ContinuousLinearMap.neg_apply, map_neg]
  rw [gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x a b]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem negGInvDiffRaisedEndo_inner_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x ((-metricComparisonDiffEndo (I := I) g₀ g₁ x) v) v
      ≤ (δ / (1 - δ)) * g₀.inner x v v := by
  rw [ContinuousLinearMap.neg_apply, map_neg]
  have hbnd := abs_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  have hle : -g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) v
      ≤ |g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) v| := neg_le_abs _
  calc -g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) v
      ≤ |g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) v| := hle
    _ ≤ (δ / (1 - δ)) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := hbnd
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem tensorInnerPointwise_negGInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel (negGInvDiffSlotApplied (I := I) g₀ g₁ s x W))
      ≤ (δ / (1 - δ)) * tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.exists_orthoFrame_basis_E
      (I := I) (M := M) g₀ x
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorInnerPointwise_slotΛ_le
    (I := I) (M := M) g₀ s x (-metricComparisonDiffEndo (I := I) g₀ g₁ x)
    (negGInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x)
    (fun v => negGInvDiffRaisedEndo_inner_self_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth

private noncomputable def armPrincipalSlotPairing
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) : ℝ :=
  tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (negGInvDiffSlotApplied
        (I := I) g₀ g₁ (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x)))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem armPrincipalSlotPairing_eq_neg_inner
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
      - (⟪iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀,
          operatorFieldApply (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + n)
              (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)⟫_ℝ : ℝ) := by
  classical
  set A : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hA_def
  set B : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    operatorFieldApply (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + n)
        (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁)) A with hB_def
  have hBfun : ∀ x : M,
      B.toFun x =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := fun x => rfl
  rw [SmoothCcTensor.inner_def (I := I) (M := M) A B]
  rw [armPrincipalSlotPairing]
  have heq :
      (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
        = (fun x => - B.toFun x) := by
    funext x
    rw [hBfun x,
      toModel_negGInvDiffSlotApplied_eq (I := I) g₀ g₁ (2 + n) x (A.toSection x)]
  rw [show (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) = A.toFun from rfl,
    heq]
  have hsmul : (fun x => - B.toFun x) = (-1 : ℝ) • B.toFun := by
    funext x; rw [Pi.smul_apply, neg_one_smul]
  rw [hsmul,
    tensorL2Inner_smul_right (I := I) (M := M) g₀ 0 ((2 + n) + 1) (-1 : ℝ) A.toFun B.toFun]
  ring

private theorem deTurckArm_residual_ibp_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ F₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0),
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 0 u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ 0 u₀ =
        (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
            operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) F₀
              (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) := by
  classical
  refine ⟨-(ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))), fun u₀ => ?_⟩
  set G₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hG₀
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      Du with hP
  rw [armPrincipalSlotPairing_eq_neg_inner (I := I) (M := M) g₀ g₁ 0 u₀, sub_neg_eq_add,
    oneMinusConnLapSmoothIter_zero]
  have hslot : (⟪iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀,
      operatorFieldApply (I := I) (M := M) g₀ ((2 + 0) + 1) ((2 + 0) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + 0)
          (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀)⟫_ℝ : ℝ) =
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1) Du.toFun P.toFun := by
    rw [hDu, hP]
    exact SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀)
      (operatorFieldApply (I := I) (M := M) g₀ ((2 + 0) + 1) ((2 + 0) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + 0)
          (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀))
  rw [hslot]
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g₀ 2 u₀ P
  have hsplit := armResidual_covDivergence_split (I := I) (M := M) g₀ g₁ u₀
  have hfun : (covDivergence (I := I) (M := M) g₀ 2 P).toFun =
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun +
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    rw [hP, hDu, hG₀, hsplit, SmoothCcTensor.toFun_add]
  rw [hfun] at hgreen
  rw [tensorL2Inner_add_right (I := I) (M := M) g₀ 0 2 u₀.toFun
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun
    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) u₀ (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) u₀ (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du))] at hgreen
  have hrhs : (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
      operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) (-G₀)
        (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) =
      - tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 0) u₀.toFun
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    have hinner := SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 0 u₀)
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) (-G₀)
        (iteratedCovGrad (I := I) g₀ 0 2 1 u₀))
    rw [hinner]
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 1 u₀ : SmoothCcTensor g₀ 0 (2 + 1)) = Du from rfl]
    rw [appCc_neg_left (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du,
      SmoothCcTensor.toFun_neg]
    rw [show (-(operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun) =
        (-1 : ℝ) • (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun from by
      funext x
      rw [Pi.neg_apply, Pi.smul_apply, neg_one_smul]]
    rw [tensorL2Inner_smul_right]
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 u₀).toFun = u₀.toFun from rfl]
    ring
  rw [hrhs]
  have hDuFun : Du.toFun = (covGrad (I := I) (M := M) g₀ 0 2 u₀).toFun := rfl
  rw [hDuFun]
  have hY : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 0) u₀.toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 2 u₀.toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := rfl
  linarith [hgreen, hY]

private theorem armComm_pointwiseTensorCurv_pairing_abs_le (g₀ : SmoothRiemannianMetric I M)
    (σ i q dS dZ NA NB : ℕ) (hNA : i + q + 2 + dS ≤ NA) (hNB : i + q + dZ ≤ NB)
    (cS cZ : ℕ → ℝ) (hcS_nn : ∀ p, 0 ≤ cS p) (hcZ_nn : ∀ p, 0 ≤ cZ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (S : SmoothCcTensor g₀ 0 σ)
      (Z : SmoothCcTensor g₀ 0 (σ + 1)),
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ ≤
        cS p * ∑ j ∈ Finset.range (p + dS + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) p Z‖ ≤
        cZ p * ∑ j ∈ Finset.range (p + dZ + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      |tensorL2Inner (I := I) (M := M) g₀ 0 (σ + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))).toFun Z.toFun| ≤
        C * ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  rcases le_or_gt q i with hqi | hiq
  · obtain ⟨Kp, hKp_nn, hKp⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ σ
    obtain ⟨CfQ, hCfQ_nn, hCfQ⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ σ q
    obtain ⟨CL, hCL_nn, hCL⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ (σ + 1) (i - (i + q) / 2)
    obtain ⟨CR, hCR_nn, hCR⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ (σ + 1) ((i + q) / 2)
    refine ⟨(CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
        ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
          ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
      (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p),
      mul_nonneg (mul_nonneg hCL_nn (mul_nonneg
          (Finset.sum_nonneg fun c _ => hKp_nn c)
          (mul_nonneg (Finset.sum_nonneg fun e _ => hCfQ_nn e)
            (Finset.sum_nonneg fun p _ => hcS_nn p))))
        (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcZ_nn p)),
      fun u₀ S Z hS hZ => ?_⟩
    have hLb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) (i - (i + q) / 2)
        (pointwiseTensorCurv (I := I) (M := M) g₀ σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖ ≤
        (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
          ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
            ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCL (pointwiseTensorCurv (I := I) (M := M) g₀ σ
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))) ?_
      have h1 : ∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) c
            (pointwiseTensorCurv (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖ ≤
          (∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 σ e
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖ :=
        armAsm_sum_window_le (2 * (i - (i + q) / 2) + 1) 1 Kp
          (fun c => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) c
            (pointwiseTensorCurv (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖)
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖)
          hKp_nn (fun _ => norm_nonneg _)
          (fun c _ => hKp c (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))
      have h2 : ∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖ ≤
          (∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
            ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q),
              ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ :=
        armAsm_sum_window_le (2 * (i - (i + q) / 2) + 1 + 1) (2 * q) CfQ
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖)
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖)
          hCfQ_nn (fun _ => norm_nonneg _) (fun e _ => hCfQ e S)
      have h3 : ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q),
          ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ ≤
          (∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p) *
            ∑ j ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q + dS),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q) dS cS
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcS_nn (fun _ => norm_nonneg _) (fun p _ => hS p)
      have h4 : ∑ j ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q + dS),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ ≤
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
      calc CL * ∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) c
              (pointwiseTensorCurv (I := I) (M := M) g₀ σ
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖
          ≤ CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
                ((∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p) *
                  ∑ j ∈ Finset.range (NA + 1),
                    ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCL_nn
            refine le_trans h1 ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun c _ => hKp_nn c)
            refine le_trans h2 ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun e _ => hCfQ_nn e)
            refine le_trans h3 ?_
            exact mul_le_mul_of_nonneg_left h4
              (Finset.sum_nonneg fun p _ => hcS_nn p)
        _ = (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
                ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
            ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
            ring
    have hRb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) ((i + q) / 2) Z‖ ≤
        (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCR Z) ?_
      have h1 : ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) p Z‖ ≤
          (∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
            ∑ j ∈ Finset.range (2 * ((i + q) / 2) + 1 + dZ),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * ((i + q) / 2) + 1) dZ cZ
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) p Z‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcZ_nn (fun _ => norm_nonneg _) (fun p _ => hZ p)
      refine le_trans (mul_le_mul_of_nonneg_left h1 hCR_nn) ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcZ_nn p))
      exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
    refine le_trans (armLadder_pairing_abs_le_transport (I := I) (M := M) g₀ (σ + 1) i
      ((i + q) / 2) (by omega)
      (pointwiseTensorCurv (I := I) (M := M) g₀ σ
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)) Z) ?_
    calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) (i - (i + q) / 2)
          (pointwiseTensorCurv (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) ((i + q) / 2) Z‖
        ≤ ((CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
              ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
            ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          ((CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
            ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
          mul_le_mul hLb hRb (norm_nonneg _) (le_trans (norm_nonneg _) hLb)
      _ = (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
              ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
          (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
          ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
            (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
          ring
  · obtain ⟨KK, hKK_nn, hKK⟩ :=
      exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le (I := I) (M := M) g₀ σ
    obtain ⟨CfI, hCfI_nn, hCfI⟩ :=
      armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ (σ + 1) i
    obtain ⟨CL, hCL_nn, hCL⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ σ (q - (q - i - 1) / 2)
    obtain ⟨CR, hCR_nn, hCR⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ σ ((q - i - 1) / 2)
    refine ⟨(CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
      (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
        ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
          ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))),
      mul_nonneg (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcS_nn p))
        (mul_nonneg hCR_nn (mul_nonneg (Finset.sum_nonneg fun c _ => hKK_nn c)
          (mul_nonneg (Finset.sum_nonneg fun e _ => hCfI_nn e)
            (Finset.sum_nonneg fun b _ => hcZ_nn b)))),
      fun u₀ S Z hS hZ => ?_⟩
    have h1 : tensorL2Inner (I := I) (M := M) g₀ 0 (σ + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g₀ 0 (σ + 1)
        (pointwiseTensorCurv (I := I) (M := M) g₀ σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)).toFun
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z).toFun := by
      have h := armLadder_pairing_transport (I := I) (M := M) g₀ (σ + 1) i i le_rfl
        (pointwiseTensorCurv (I := I) (M := M) g₀ σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)) Z
      rw [Nat.sub_self, oneMinusConnLapSmoothIter_zero] at h
      exact h
    have h2 := pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator (I := I) (M := M) g₀ σ
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)
    rw [h1, h2]
    have hLb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (q - (q - i - 1) / 2) S‖ ≤
        (CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCL S) ?_
      have hw : ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ ≤
          (∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
            ∑ j ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1 + dS),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * (q - (q - i - 1) / 2) + 1) dS cS
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcS_nn (fun _ => norm_nonneg _) (fun p _ => hS p)
      refine le_trans (mul_le_mul_of_nonneg_left hw hCL_nn) ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcS_nn p))
      exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
    have hRb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ ((q - i - 1) / 2)
        (rawTensorConnLapSmooth (I := I) g₀ 0 σ
            (covDivergence (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
          covDivergence (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖ ≤
        (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
          ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
            ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCR (rawTensorConnLapSmooth (I := I) g₀ 0 σ
          (covDivergence (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
        covDivergence (I := I) (M := M) g₀ σ
          (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))) ?_
      have h1' : ∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 σ c
            (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                (covDivergence (I := I) (M := M) g₀ σ
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖ ≤
          (∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
            ∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖ :=
        armAsm_sum_window_le (2 * ((q - i - 1) / 2) + 1) 1 KK
          (fun c => ‖iteratedCovGrad (I := I) g₀ 0 σ c
            (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                (covDivergence (I := I) (M := M) g₀ σ
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖)
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖)
          hKK_nn (fun _ => norm_nonneg _)
          (fun c _ => hKK c (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z))
      have h2' : ∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖ ≤
          (∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
            ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖ :=
        armAsm_sum_window_le (2 * ((q - i - 1) / 2) + 1 + 1) (2 * i) CfI
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖)
          (fun b => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖)
          hCfI_nn (fun _ => norm_nonneg _) (fun e _ => hCfI e Z)
      have h3' : ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖ ≤
          (∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b) *
            ∑ j ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i + dZ),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i) dZ cZ
          (fun b => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcZ_nn (fun _ => norm_nonneg _) (fun b _ => hZ b)
      have h4' : ∑ j ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i + dZ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ ≤
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
      calc CR * ∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 σ c
              (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                  (covDivergence (I := I) (M := M) g₀ σ
                    (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
                covDivergence (I := I) (M := M) g₀ σ
                  (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                    (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖
          ≤ CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
                ((∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b) *
                  ∑ j ∈ Finset.range (NB + 1),
                    ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCR_nn
            refine le_trans h1' ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun c _ => hKK_nn c)
            refine le_trans h2' ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun e _ => hCfI_nn e)
            refine le_trans h3' ?_
            exact mul_le_mul_of_nonneg_left h4'
              (Finset.sum_nonneg fun b _ => hcZ_nn b)
        _ = (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
                ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
            ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
            ring
    refine le_trans (armLadder_pairing_abs_le_transport (I := I) (M := M) g₀ σ q
      ((q - i - 1) / 2) (by omega) S
      (rawTensorConnLapSmooth (I := I) g₀ 0 σ
          (covDivergence (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
        covDivergence (I := I) (M := M) g₀ σ
          (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))) ?_
    calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (q - (q - i - 1) / 2) S‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ ((q - i - 1) / 2)
            (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                (covDivergence (I := I) (M := M) g₀ σ
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖
        ≤ ((CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
            ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          ((CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
                ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
            ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
          mul_le_mul hLb hRb (norm_nonneg _) (le_trans (norm_nonneg _) hLb)
      _ = (CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
          (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
            ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
              ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
          ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
            (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
          ring

private theorem armStep_pairing_diff_abs_le (g₀ g₁ : SmoothRiemannianMetric I M) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun -
        tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
          (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun| ≤
      C * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨F, R, hF, hE2⟩ :=
    exists_secondCovGrad_swap_ricciDefect_homField (I := I) (M := M) g₀ 0 (2 + m)
  obtain ⟨cWm, hcWm_nn, hcWm⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ (m + 1)
    (2 + m + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  obtain ⟨cDWm, hcDWm_nn, hcDWm⟩ := armAsm_covGrad_appCc_jet_window (I := I) (M := M) g₀ (m + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  obtain ⟨cGY, hcGY_nn, hcGY⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ (m + 1)
    (2 + m + 1 + 1)
    (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
  obtain ⟨cDD, hcDD_nn, hcDD⟩ :=
    exists_appFullSec_iteratedCovGrad_shiftedJetWindow_bound (I := I) (M := M) g₀ m ((2 + m) + 2) R
  obtain ⟨cD2Y, hcD2Y_nn, hcD2Y⟩ := exists_appCc_appFullSec_iteratedCovGrad_jetWindow_bound (I := I) (M := M) g₀ m
    ((2 + m) + 2) (2 + m + 1 + 1) R
    (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
  obtain ⟨cWm', hcWm'_nn, hcWm'⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ (m + 1 + 1)
    (2 + (m + 1) + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
      (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  have hV1win : ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1) p
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)‖ ≤
        (1 : ℝ) * ∑ j ∈ Finset.range (p + (m + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    intro u₀ p
    rw [one_mul]
    have h := armJet_norm_comp (I := I) (M := M) g₀ 2 (m + 1) p u₀
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1) p
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + p) u₀‖ := h
      _ ≤ ∑ j ∈ Finset.range (p + (m + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hCVwin : ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1 + 1) p
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))‖ ≤
        (1 : ℝ) * ∑ j ∈ Finset.range (p + (m + 1 + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    intro u₀ p
    rw [one_mul]
    have h := armJet_norm_comp (I := I) (M := M) g₀ 2 (m + 1 + 1) p u₀
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1 + 1) p
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1 + p) u₀‖ := h
      _ ≤ ∑ j ∈ Finset.range (p + (m + 1 + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  obtain ⟨CA, hCA_nn, hCA⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
    (2 + m + 1) k (k / 2) (m + 1) (m + 1) (m + k + 2) (m + k + 1)
    (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cWm (fun _ => zero_le_one) hcWm_nn
  obtain ⟨CD1, hCD1_nn, hCD1⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
    (2 + m + 1 + 1) k (k / 2) m (m + 1 + 1) (m + k + 1) (m + k + 2)
    (by omega) (by omega) (by omega) cDD cWm' hcDD_nn hcWm'_nn
  obtain ⟨CD2, hCD2_nn, hCD2⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
    (2 + m + 1 + 1) k (k - k / 2) (m + 1 + 1) m (m + k + 2) (m + k + 1)
    (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cD2Y (fun _ => zero_le_one) hcD2Y_nn
  have hGEx : ∃ CG : ℝ, 0 ≤ CG ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
            (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
            (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun| ≤
        CG * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    by_cases hk2 : k % 2 = 0
    · obtain ⟨CG, hCG_nn, hCG⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
        (2 + m + 1 + 1) k (k / 2) (m + 1 + 1) (m + 1) (m + k + 2) (m + k + 1)
        (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cGY (fun _ => zero_le_one) hcGY_nn
      refine ⟨CG, hCG_nn, fun u₀ => ?_⟩
      have h := hCG u₀
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
          (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (hCVwin u₀) (fun p => hcGY u₀ p)
      rw [show m + k + 2 + 1 = m + k + 3 from by omega,
        show m + k + 1 + 1 = m + k + 2 from by omega] at h
      rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)]
      calc |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
              (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
                (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
              (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun|
          ≤ CG * ((∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := h
        _ = CG * ((∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by ring
    · obtain ⟨CG, hCG_nn, hCG⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
        (2 + m + 1 + 1) k (k - k / 2) (m + 1 + 1) (m + 1) (m + k + 1) (m + k + 2)
        (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cGY (fun _ => zero_le_one) hcGY_nn
      refine ⟨CG, hCG_nn, fun u₀ => ?_⟩
      have h := hCG u₀
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
          (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (hCVwin u₀) (fun p => hcGY u₀ p)
      rw [show m + k + 1 + 1 = m + k + 2 from by omega,
        show m + k + 2 + 1 = m + k + 3 from by omega] at h
      rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)]
      exact h
  obtain ⟨CG, hCG_nn, hCGb⟩ := hGEx
  have hCiEx : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2, i < k →
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
                (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun| ≤
        Ci * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    intro i
    by_cases hik : i < k
    · obtain ⟨Ci, hCi_nn, hCi⟩ := armComm_pointwiseTensorCurv_pairing_abs_le (I := I) (M := M) g₀
        (2 + m + 1) i (k - 1 - i) (m + 1) (m + 2) (m + k + 2) (m + k + 1)
        (by omega) (by omega) (fun _ => (1 : ℝ)) cDWm (fun _ => zero_le_one) hcDWm_nn
      refine ⟨Ci, hCi_nn, fun u₀ _ => ?_⟩
      have h := hCi u₀ (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
        (hV1win u₀) (fun p => hcDWm u₀ p)
      rw [show m + k + 2 + 1 = m + k + 3 from by omega,
        show m + k + 1 + 1 = m + k + 2 from by omega] at h
      calc |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
                  (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
            (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun|
          ≤ Ci * ((∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := h
        _ = Ci * ((∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by ring
    · exact ⟨0, le_rfl, fun u₀ hik' => absurd hik' hik⟩
  choose Ci hCi_nn hCi using hCiEx
  refine ⟨CA + CG + CD1 + CD2 + ∑ i ∈ Finset.range k, Ci i,
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hCA_nn hCG_nn) hCD1_nn) hCD2_nn)
      (Finset.sum_nonneg fun i _ => hCi_nn i),
    fun u₀ => ?_⟩
  have hDir : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun := by
    rw [oneMinusConnLapSmoothIter_succ]
    exact oneMinusConnLapSmooth_l2Inner_eq_add_covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
  have hsplit1 : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun +
    ∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun := by
    rw [armLadder_covGrad_iterL_expansion (I := I) (M := M) g₀ (2 + m + 1) k
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀),
      armAsm_l2Inner_add_left (I := I) (M := M) g₀ (2 + m + 1 + 1),
      armAsm_l2Inner_sum_left (I := I) (M := M) g₀ (2 + m + 1 + 1) k]
  have hgradW : covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) =
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
      (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀) +
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) := by
    rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)]
    exact covGrad_appCcRS_eq (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)
  have hMainSplit : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun := by
    rw [hgradW, armAsm_l2Inner_add_right (I := I) (M := M) g₀ (2 + m + 1 + 1)]
  have hE2v : covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀) =
    homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) +
    homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
      (iteratedCovGrad (I := I) g₀ 0 2 m u₀) :=
    hE2 (iteratedCovGrad (I := I) g₀ 0 2 m u₀)
  have hPsplit : ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) =
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) +
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀)) := by
    conv_lhs => rw [hE2v]
    exact appCcRS_add_right (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))
  have hsplitP : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun := by
    rw [hPsplit, armAsm_l2Inner_add_right (I := I) (M := M) g₀ (2 + m + 1 + 1)]
  have hconj : ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) =
    homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)) := by
    rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))]
    exact appCc_slotExtend_slotInsert_appFullSec_swap_conj (I := I) (M := M) g₀ (2 + m)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) F hF
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
  have hhop : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    rw [hconj]
    exact (appFullSec_swap_l2Inner_hop (I := I) (M := M) g₀ (2 + m) F hF
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀))).symm
  have hσiter : homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) =
    oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) :=
    (armSwap_iterL_comm (I := I) (M := M) g₀ (2 + m) F hF k
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).symm
  have hσsub : homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) =
    covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀) -
    homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
      (iteratedCovGrad (I := I) g₀ 0 2 m u₀) :=
    eq_sub_of_add_eq hE2v.symm
  have hitersub : oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) =
    oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) -
    oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀)) := by
    rw [hσsub]
    exact armLadder_iterL_sub (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) k
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))
  have hlast : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) -
        oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
          (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
            (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    rw [SmoothCcTensor.toFun_sub]
    exact tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀)))
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀))
  have hbr : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := rfl
  have hPσ : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    rw [hhop, hσiter, hitersub, hlast, hbr]
  have hEq : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    (∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun) +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    linarith [hDir, hsplit1, hMainSplit, hsplitP, hPσ]
  rw [hEq]
  have hA2 : |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun| ≤
      CA * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    have h := hCA u₀ (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (hV1win u₀) (fun p => hcWm u₀ p)
    rw [show m + k + 2 + 1 = m + k + 3 from by omega,
      show m + k + 1 + 1 = m + k + 2 from by omega] at h
    refine le_trans h (le_of_eq ?_)
    ring
  have hD1b : |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun| ≤
      CD1 * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    have h := hCD1 u₀
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))
      (operatorFieldApply (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀))
      (fun p => hcDD u₀ p) (fun p => hcWm' u₀ p)
    rw [show m + k + 1 + 1 = m + k + 2 from by omega,
      show m + k + 2 + 1 = m + k + 3 from by omega] at h
    exact h
  have hD2b : |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun| ≤
      CD2 * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    have h := hCD2 u₀
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀)))
      (hCVwin u₀) (fun p => hcD2Y u₀ p)
    rw [show m + k + 2 + 1 = m + k + 3 from by omega,
      show m + k + 1 + 1 = m + k + 2 from by omega] at h
    rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (homTensorRSFieldApply (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))]
    refine le_trans h (le_of_eq ?_)
    ring
  have hCsum : ∑ i ∈ Finset.range k,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun| ≤
      (∑ i ∈ Finset.range k, Ci i) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    refine le_trans (Finset.sum_le_sum
      (fun i hi => hCi i u₀ (Finset.mem_range.mp hi))) ?_
    rw [← Finset.sum_mul]
  refine le_trans ?_ (le_of_eq (show
      (CA + (∑ i ∈ Finset.range k, Ci i) + CG + CD2 + CD1) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) =
      (CA + CG + CD1 + CD2 + ∑ i ∈ Finset.range k, Ci i) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) from
    by ring))
  refine le_trans (armAsm_abs_add4_sub_le _ _ _ _ _) ?_
  have hSabs : |∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun| ≤
      (∑ i ∈ Finset.range k, Ci i) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hCsum
  exact le_trans
    (add_le_add (add_le_add (add_le_add (add_le_add hA2 hSabs) (hCGb u₀)) hD2b) hD1b)
    (le_of_eq (by ring))

private theorem oneMinusConnLapIter_dirichletSlotForm_add_armPrincipalSlotPairing_abs_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun +
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀| ≤
      C * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  obtain ⟨cW0, hcW0_nn, hcW0⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ 1 (2 + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  have hCbEx : ∀ i : ℕ, ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2, i < n →
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g₀ 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun| ≤
        Cb * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨Cb, hCb_nn, hCb⟩ := armComm_pointwiseTensorCurv_pairing_abs_le (I := I) (M := M) g₀ 2 i
        (n - 1 - i) 0 1 (n + 1) n (by omega) (by omega)
        (fun _ => (1 : ℝ)) cW0 (fun _ => zero_le_one) hcW0_nn
      refine ⟨Cb, hCb_nn, fun u₀ _ => ?_⟩
      have hSwin : ∀ p, ‖iteratedCovGrad (I := I) g₀ 0 2 p u₀‖ ≤
          (1 : ℝ) * ∑ j ∈ Finset.range (p + 0 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
        intro p
        rw [one_mul]
        exact Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      have h := hCb u₀ u₀
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀))
        hSwin (fun p => hcW0 u₀ p)
      rw [show n + 1 + 1 = n + 2 from by omega] at h
      refine le_trans h (le_of_eq ?_)
      ring
    · exact ⟨0, le_rfl, fun u₀ hi' => absurd hi' hi⟩
  choose Cb hCb_nn hCb using hCbEx
  choose Cs hCs_nn hCs using fun μ : ℕ =>
    armStep_pairing_diff_abs_le (I := I) (M := M) g₀ g₁ μ (n - 1 - μ)
  refine ⟨(∑ i ∈ Finset.range n, Cb i) + ∑ μ ∈ Finset.range n, Cs μ,
    add_nonneg (Finset.sum_nonneg fun i _ => hCb_nn i)
      (Finset.sum_nonneg fun μ _ => hCs_nn μ),
    fun u₀ => ?_⟩
  set H : ℕ → ℝ := fun μ => tensorL2Inner (I := I) (M := M) g₀ 0 (2 + μ + 1)
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + μ + 1) (n - μ)
      (iteratedCovGrad (I := I) g₀ 0 2 (μ + 1) u₀)).toFun
    (operatorFieldApply (I := I) (M := M) g₀ (2 + μ + 1) (2 + μ + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + μ)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 0 2 (μ + 1) u₀)).toFun with hH
  have htele : ∑ μ ∈ Finset.range n, (H μ - H (μ + 1)) = H 0 - H n :=
    Finset.sum_range_sub' H n
  have hH0 : H 0 = tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) n
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun := by
    simp only [hH]
    rw [Nat.sub_zero]
    rfl
  have hPSP : armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ = - H n := by
    simp only [hH]
    rw [show n - n = 0 from Nat.sub_self n, oneMinusConnLapSmoothIter_zero,
      armPrincipalSlotPairing_eq_neg_inner (I := I) (M := M) g₀ g₁ n u₀,
      SmoothCcTensor.inner_def]
    rfl
  have hbase : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) n
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun +
    ∑ i ∈ Finset.range n,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun := by
    rw [armLadder_covGrad_iterL_expansion (I := I) (M := M) g₀ 2 n u₀,
      armAsm_l2Inner_add_left (I := I) (M := M) g₀ (2 + 1),
      armAsm_l2Inner_sum_left (I := I) (M := M) g₀ (2 + 1) n]
  have hgoal_eq : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun +
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
    (∑ i ∈ Finset.range n,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun) +
    ∑ μ ∈ Finset.range n, (H μ - H (μ + 1)) := by
    linarith [hbase, hH0, hPSP, htele]
  rw [hgoal_eq]
  have hstepb : ∀ μ ∈ Finset.range n, |H μ - H (μ + 1)| ≤
      Cs μ * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    intro μ hμ
    rw [Finset.mem_range] at hμ
    have h := hCs μ u₀
    rw [show μ + (n - 1 - μ) + 2 = n + 1 from by omega,
      show μ + (n - 1 - μ) + 3 = n + 2 from by omega] at h
    simp only [hH]
    rw [show n - μ = n - 1 - μ + 1 from by omega,
      show n - (μ + 1) = n - 1 - μ from by omega]
    exact h
  have hbaseb : ∀ i ∈ Finset.range n,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun| ≤
      Cb i * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) :=
    fun i hi => hCb i u₀ (Finset.mem_range.mp hi)
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
    (Finset.abs_sum_le_sum_abs _ _)) ?_
  refine le_trans (add_le_add (Finset.sum_le_sum hbaseb) (Finset.sum_le_sum hstepb)) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]

private theorem oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le_jetProduct
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      C * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  obtain ⟨C₁, hC₁_nn, h₁⟩ :=
    oneMinusConnLapIter_dirichletSlotForm_add_armPrincipalSlotPairing_abs_le
      (I := I) (M := M) g₀ g₁ n
  obtain ⟨C₂, hC₂_nn, h₂⟩ := arm_g0Term_abs_le_jetProduct (I := I) (M := M) g₀ g₁ n
  refine ⟨C₁ + C₂, add_nonneg hC₁_nn hC₂_nn, fun u₀ => ?_⟩
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set G₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hG₀
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      Du with hP
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g₀ 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀) P
  have hsplit := armResidual_covDivergence_split (I := I) (M := M) g₀ g₁ u₀
  have hfun : (covDivergence (I := I) (M := M) g₀ 2 P).toFun =
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun +
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    rw [hP, hDu, hG₀, hsplit, SmoothCcTensor.toFun_add]
  rw [hfun] at hgreen
  rw [tensorL2Inner_add_right (I := I) (M := M) g₀ 0 2
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun
    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du))] at hgreen
  have h₁u := h₁ u₀
  have h₂u := h₂ u₀
  rw [← hDu] at h₂u
  rw [← hDu, ← hP] at h₁u
  have habs1 : -(tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun P.toFun +
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀) ≤
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun P.toFun +
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀| := neg_le_abs _
  have habs2 : -(tensorL2Inner (I := I) (M := M) g₀ 0 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun) ≤
      |tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun| := neg_le_abs _
  linarith [h₁u, h₂u, habs1, habs2, hgreen]

private theorem exists_oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_jetBound_core
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (_htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (_hδ_lt : δ < 1) (_hδ_nn : 0 ≤ δ) (_hδ : metricCauchySchwarzBound (I := I) g₀ h δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (1 / 4 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  obtain ⟨C, hC_nn, hres⟩ :=
    oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le_jetProduct
      (I := I) (M := M) g₀ g₁ n
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ n
  obtain ⟨Cjet, hCjet_nn, hjet⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
      (I := I) (M := M) g₀ n
  refine ⟨(C + C ^ 2) * Cjet ^ 2 + (1 / 4) * Cgap, by positivity, fun u₀ => ?_⟩
  set Mtop := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ with hMtop_def
  set Mlow := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ with hMlow_def
  set Jn := ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ with hJn_def
  set X := ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖ with hX_def
  have hMtop_nn : 0 ≤ Mtop := norm_nonneg _
  have hMlow_nn : 0 ≤ Mlow := norm_nonneg _
  have hJn_nn : 0 ≤ Jn := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hX_nn : 0 ≤ X := norm_nonneg _
  have hgap_u := hgap u₀
  have hjet_u := hjet u₀
  have hsum : ∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ =
      Jn + X := by
    rw [hJn_def, hX_def]
    exact Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) (n + 1)
  have hres_u : tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      C * Jn ^ 2 + C * (Jn * X) := by
    refine le_trans (hres u₀) ?_
    rw [hsum]
    have : C * (Jn * (Jn + X)) = C * Jn ^ 2 + C * (Jn * X) := by ring
    linarith [this.le, this.ge]
  have hX_toL2 : X = ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ := by
    rw [hX_def, SmoothCcTensor.norm_toL2]
  have hX_sq_le : X ^ 2 ≤ Mtop ^ 2 + Cgap * Mlow ^ 2 := by
    rw [hX_toL2]; exact hgap_u
  have hJn_le : Jn ≤ Cjet * Mlow := hjet_u
  have hJn_sq_le : Jn ^ 2 ≤ Cjet ^ 2 * Mlow ^ 2 := by
    nlinarith [hJn_nn, mul_nonneg hCjet_nn hMlow_nn]
  have hyoung : C * (Jn * X) ≤ (1 / 4) * X ^ 2 + C ^ 2 * Jn ^ 2 := by
    nlinarith [sq_nonneg (X / 2 - C * Jn)]
  have hA : (C + C ^ 2) * Jn ^ 2 ≤ (C + C ^ 2) * (Cjet ^ 2 * Mlow ^ 2) :=
    mul_le_mul_of_nonneg_left hJn_sq_le (by positivity)
  have hB : (1 / 4 : ℝ) * X ^ 2 ≤ (1 / 4) * (Mtop ^ 2 + Cgap * Mlow ^ 2) := by
    linarith [hX_sq_le]
  nlinarith [hres_u, hyoung, hA, hB]

private theorem oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (1 / 4 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  exists_oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_jetBound_core
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ

private theorem oneMinusConnLapIter_pairing_fold
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ) :
    ∃ rem : SmoothCcTensor g₀ 0 2 → ℝ,
      (∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun =
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ + rem u₀) ∧
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          rem u₀ ≤
            (1 / 4 : ℝ) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  refine ⟨fun u₀ =>
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀,
    fun u₀ => by ring, ?_⟩
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le
      (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  exact ⟨Clower, hClower_nn, hbound⟩

omit [BoundarylessManifold I M] in
private theorem armPrincipalSlotPairing_le_dirichlet_top
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set A : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hA_def
  set B : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    operatorFieldApply (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (2 + n)
        (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁)) A with hB_def
  have hBfun : ∀ x : M,
      B.toFun x =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := by
    intro x
    rfl
  have hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hcross := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A B
    have heq :
        (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
          = (fun x => - tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
              (A.toFun x) (B.toFun x)) := by
      funext x
      rw [hBfun x, SmoothCcTensor.toFun_apply,
        toModel_negGInvDiffSlotApplied_eq (I := I) g₀ g₁ (2 + n) x (A.toSection x),
        show (- TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
            = (-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) from
          (neg_one_smul ℝ _).symm,
        tensorInnerPointwise_smul_right]
      ring
    rw [heq]
    exact hcross.neg
  have hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A A
  have htool := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorL2Inner_slotΛ_le
    (I := I) (M := M) g₀ (2 + n) (κ := δ / (1 - δ))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
    (fun x => tensorInnerPointwise_negGInvDiffSlot_le
      (I := I) (M := M) g₀ g₁ h htie hδ_lt hδ_nn hδ (2 + n) x (A.toSection x))
    hWS_int hWW_int
  have hnorm :
      tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) =
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := by
    have hAA : tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1) A.toFun A.toFun =
        (⟪A, A⟫_ℝ : ℝ) := (SmoothCcTensor.inner_def (I := I) (M := M) A A).symm
    rw [show (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) = A.toFun from rfl,
      hAA, real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
  have hslot :
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (δ / (1 - δ)) *
          tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
            (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
            (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) := htool
  rw [hnorm] at hslot
  exact hslot

private theorem dirichlet_top_le_spectral_add_lower
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cgap : ℝ, 0 ≤ Cgap ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 ≤
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
    (I := I) (M := M) g₀ n

private theorem oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → metricCauchySchwarzBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          tensorL2Inner (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun ≤
            (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨rem, hsplit, Clower₁, hClower₁_nn, hrem⟩ :=
    oneMinusConnLapIter_pairing_fold (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    dirichlet_top_le_spectral_add_lower (I := I) (M := M) g₀ n
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  refine ⟨(δ / (1 - δ)) * Cgap + Clower₁, by positivity, fun u₀ => ?_⟩
  rw [hsplit u₀]
  have htop := armPrincipalSlotPairing_le_dirichlet_top
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ u₀
  have hg := hgap u₀
  have hr := hrem u₀
  have hMnp_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 :=
    sq_nonneg _
  have hstep : armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
        (δ / (1 - δ)) * Cgap *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
    calc armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀
        ≤ (δ / (1 - δ)) *
            ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := htop
      _ ≤ (δ / (1 - δ)) *
            (‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hg hκ_nn
      _ = (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          (δ / (1 - δ)) * Cgap *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by ring
  nlinarith [hstep, hr, hMnp_nn]

theorem deTurckPrincipalCometricArm_spectralPairing_tsum_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → metricCauchySchwarzBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) ≤
            2 * (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨2 * Clower, by positivity, fun u₀ => ?_⟩
  have hpair :=
    spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner (I := I) (M := M) g₀ n u₀
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)
  rw [hpair]
  have hb := hbound u₀
  have hgoal :
      2 * (δ / (1 - δ) + 1 / 4) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          2 * Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 =
        2 * ((δ / (1 - δ) + 1 / 4) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) := by
    ring
  rw [hgoal]
  linarith [hb]

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → metricCauchySchwarzBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    deTurckPrincipalCometricArm_spectralPairing_tsum_le (I := I) (M := M) g₀ n
      g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨Clower, hClower_nn, fun u₀ => ?_⟩
  have hinner :
      (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) =
        ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) :=
    tensorHs.inner_def (I := I) (M := M)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
  rw [hinner]
  exact hbound u₀

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_lt_one
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ → metricCauchySchwarzBound (I := I) g₀ h δ →
      ∃ Cupper Clower : ℝ, Cupper < 1 ∧ 0 ≤ Cupper ∧ 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * Cupper *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_le hδ_nn hδ
  have hδ_lt : δ < 1 := by linarith
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  have hone_sub : (0 : ℝ) < 1 - δ := by linarith
  have hκ_le : δ / (1 - δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hone_sub]
    linarith
  refine ⟨δ / (1 - δ) + 1 / 4, Clower, by linarith, by positivity, hClower_nn, hbound⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
