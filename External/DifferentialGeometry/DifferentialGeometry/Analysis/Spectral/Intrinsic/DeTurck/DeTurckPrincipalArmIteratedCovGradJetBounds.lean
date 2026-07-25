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
omit [NeZero (Module.finrank ℝ E)] in
theorem armJet_norm_comp (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ)
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have h1 : ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      tensorL2Norm (I := I) (M := M) g₀ 0 ((s + j) + i)
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have h2 : ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ =
      tensorL2Norm (I := I) (M := M) g₀ 0 (s + (j + i))
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [h1, h2,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i)
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have ha : (0 : ℝ) ≤
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ :=
    norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, hsq]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armJet_norm_order_congr (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem armJet_appCcRS_norm_le (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : SmoothCcTensor g₀ 0 b,
      ‖ccOperatorFieldComp (I := I) (M := M) g₀ 0 b c Φ V‖ ≤ C * ‖V‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hCop⟩ :=
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀ 0 b c Φ
  refine ⟨Real.sqrt Cop, Real.sqrt_nonneg _, fun V => ?_⟩
  set Z : SmoothCcTensor g₀ 0 c := ccOperatorFieldComp (I := I) (M := M) g₀ 0 b c Φ V with hZ_def
  have hZn : ‖Z‖ = tensorL2Norm (I := I) (M := M) g₀ 0 c Z.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) Z
  have hVn : ‖V‖ = tensorL2Norm (I := I) (M := M) g₀ 0 b V.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) V
  have hZL2 : ‖Z‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Z.toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hZn, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ c Z]
  have hVL2 : ‖V‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hVn, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ b V]
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Z.toSection x) ≤
      Cop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x) :=
    fun x => hCop V x
  have hVint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Connection.integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 b V
  have hZsq_le : ‖Z‖ ^ 2 ≤ Cop * ‖V‖ ^ 2 := by
    rw [hZL2, hVL2]
    have hg_int : MeasureTheory.Integrable
        (fun x => Cop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      hVint.const_mul Cop
    have hmono :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => riemannianFiberNormSq_nonneg (I := I) (M := M)
          g₀ 0 c x _)) hg_int
        (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul] at hmono
    linarith
  have hVnn : 0 ≤ ‖V‖ := norm_nonneg _
  have hZnn : 0 ≤ ‖Z‖ := norm_nonneg _
  rw [← Real.sqrt_sq hZnn]
  calc Real.sqrt (‖Z‖ ^ 2) ≤ Real.sqrt (Cop * ‖V‖ ^ 2) := Real.sqrt_le_sqrt hZsq_le
    _ = Real.sqrt Cop * ‖V‖ := by
        rw [Real.sqrt_mul hCop_nn, Real.sqrt_sq hVnn]

omit [NeZero (Module.finrank ℝ E)] in
theorem armJet_iteratedCovGrad_appCc_le (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    ∃ Cf : ℕ → ℝ, (∀ q, 0 ≤ Cf q) ∧ ∀ (q : ℕ) (W : SmoothCcTensor g₀ 0 b),
      ‖iteratedCovGrad (I := I) g₀ 0 c q (operatorFieldApply (I := I) (M := M) g₀ b c Φ W)‖ ≤
        Cf q * ∑ k ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 b k W‖ := by
  classical
  choose CC hCC_nn hCC using fun (q k : ℕ) =>
    armJet_appCcRS_norm_le (I := I) (M := M) g₀ (b + k) (c + q)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ q k)
  refine ⟨fun q => ∑ k ∈ Finset.range (q + 1), CC q k,
    fun q => Finset.sum_nonneg (fun k _ => hCC_nn q k), fun q W => ?_⟩
  rw [iteratedCovGrad_operatorFieldApply_eq (I := I) (M := M) g₀ b c Φ W q]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ Finset.range (q + 1),
      ‖ccOperatorFieldComp (I := I) (M := M) g₀ 0 (b + k) (c + q)
          (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ q k)
          (iteratedCovGrad (I := I) g₀ 0 b k W)‖ ≤
        CC q k * ∑ j ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 b j W‖ := by
    intro k hk
    refine le_trans (hCC q k (iteratedCovGrad (I := I) g₀ 0 b k W)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCC_nn q k)
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 b j W‖)
      (fun j _ => norm_nonneg _) hk
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

private theorem armJet_lapGrad_commutator_le
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + m) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  classical
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S => ?_⟩
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz, norm_zero]
    exact mul_nonneg (le_refl 0) (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => K p + Cm (p + 1), fun p => add_nonneg (hK_nn p) (hCm_nn (p + 1)),
      fun p S => ?_⟩
    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
            (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      change rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S
      with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p]
    refine le_trans (norm_add_le _ _) ?_
    have harm1 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ ≤
          K p * fullSum := by
      have hKb := hK p gradm
      have hreindex : ∀ a, ‖iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := by
        intro a
        rw [hgradm, armJet_norm_comp (I := I) (M := M) g₀ s m a S]
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      have hsub : ∑ a ∈ Finset.range (p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ ≤ fullSum := by
        rw [hfullSum]
        have hIco : ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ =
            ∑ b ∈ Finset.Ico m (m + (p + 2)),
              ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
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
      calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖
          ≤ K p * ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := hKb
        _ ≤ K p * fullSum := mul_le_mul_of_nonneg_left hsub (hK_nn p)
    have harm2 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ ≤
          Cm (p + 1) * fullSum := by
      have hcomp :
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + m) (p + 1) comm_m‖ := by
        have h := armJet_norm_comp (I := I) (M := M) g₀ (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := hCm (p + 1) S
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    have hfinal : K p * fullSum + Cm (p + 1) * fullSum =
        (K p + Cm (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖
        ≤ K p * fullSum + Cm (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (K p + Cm (p + 1)) * fullSum := hfinal

private theorem armJet_iterGrad_rawConnLap_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
          C * ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  intro s
  obtain ⟨K, hK_one, hK⟩ :=
    exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen (I := I) (M := M) g₀
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    armJet_lapGrad_commutator_le (I := I) (M := M) g₀ a s
  have hK_nn : 0 ≤ K := le_trans (by norm_num) hK_one
  refine ⟨K + Cfun 0, add_nonneg hK_nn (hCfun_nn 0), fun S => ?_⟩
  set FULL : ℝ := ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFULL
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hlap_second :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
          (iteratedCovGrad (I := I) g₀ 0 s a S)‖ ≤
        K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
    have hgen := hK (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)
    rw [DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)),
      DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + a)
            (iteratedCovGrad (I := I) g₀ 0 s a S)))] at hgen
    have hcomp :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + a)
              (iteratedCovGrad (I := I) g₀ 0 s a S))‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
      have h := armJet_norm_comp (I := I) (M := M) g₀ s a 2 S
      have heq :
          iteratedCovGrad (I := I) g₀ 0 (s + a) 2 (iteratedCovGrad (I := I) g₀ 0 s a S) =
            covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
              (covGrad (I := I) (M := M) g₀ 0 (s + a)
                (iteratedCovGrad (I := I) g₀ 0 s a S)) :=
        rfl
      rw [heq] at h
      rw [h]
    rw [hcomp] at hgen
    exact hgen
  have hcomm :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
          (iteratedCovGrad (I := I) g₀ 0 s a S) -
          iteratedCovGrad (I := I) g₀ 0 s a
            (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
    have h := hCfun 0 S
    simpa only [iteratedCovGrad_zero, Nat.add_zero] using h
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
            (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
              (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := by
    have := norm_sub_le
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S))
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
        iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
    simpa using this
  have hsecond_le : ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.single_le_sum
      (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 s b S‖)
      (fun b _ => norm_nonneg _) ?_
    rw [Finset.mem_range]
    omega
  have hsub_le : ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
    intro b hb
    rw [Finset.mem_range] at hb ⊢
    omega
  calc ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖
      ≤ ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
            (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
              (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := htri
    _ ≤ K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ +
          Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ :=
        add_le_add hlap_second hcomm
    _ ≤ K * FULL + Cfun 0 * FULL :=
        add_le_add (mul_le_mul_of_nonneg_left hsecond_le hK_nn)
          (mul_le_mul_of_nonneg_left hsub_le (hCfun_nn 0))
    _ = (K + Cfun 0) * FULL := by ring

theorem armJet_iteratedCovGrad_iterL_le (g₀ : SmoothRiemannianMetric I M) (s a : ℕ) :
    ∃ Cf : ℕ → ℝ, (∀ p, 0 ≤ Cf p) ∧ ∀ (p : ℕ) (v : SmoothCcTensor g₀ 0 s),
      ‖iteratedCovGrad (I := I) g₀ 0 s p (oneMinusConnLapSmoothIter (I := I) g₀ 0 s a v)‖ ≤
        Cf p * ∑ q ∈ Finset.range (p + 2 * a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ := by
  classical
  induction a with
  | zero =>
    refine ⟨fun _ => 1, fun _ => zero_le_one, fun p v => ?_⟩
    rw [oneMinusConnLapSmoothIter_zero, one_mul]
    refine Finset.single_le_sum
      (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 s q v‖)
      (fun q _ => norm_nonneg _) ?_
    rw [Finset.mem_range]
    omega
  | succ a ih =>
    obtain ⟨Cf, hCf_nn, hCf⟩ := ih
    choose C5 hC5_nn hC5 using fun p => armJet_iterGrad_rawConnLap_le (I := I) (M := M) g₀ p s
    refine ⟨fun p => Cf p + C5 p * ∑ b ∈ Finset.range (p + 3), Cf b, fun p => ?_, fun p v => ?_⟩
    · exact add_nonneg (hCf_nn p)
        (mul_nonneg (hC5_nn p) (Finset.sum_nonneg (fun b _ => hCf_nn b)))
    · set X : SmoothCcTensor g₀ 0 s := oneMinusConnLapSmoothIter (I := I) g₀ 0 s a v with hX_def
      have hsucc : oneMinusConnLapSmoothIter (I := I) g₀ 0 s (a + 1) v =
          X - rawTensorConnLapSmooth (I := I) g₀ 0 s X := by
        rw [oneMinusConnLapSmoothIter_succ]
        rfl
      rw [hsucc, iteratedCovGrad_sub (I := I) (M := M) g₀ 0 s p]
      refine le_trans (norm_sub_le _ _) ?_
      set SFULL : ℝ := ∑ q ∈ Finset.range (p + 2 * (a + 1) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ with hSFULL
      have hSFULL_nn : 0 ≤ SFULL := Finset.sum_nonneg (fun q _ => norm_nonneg _)
      have hmono : ∀ {m : ℕ}, m ≤ p + 2 * (a + 1) + 1 →
          ∑ q ∈ Finset.range m, ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ ≤ SFULL := by
        intro m hm
        rw [hSFULL]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => norm_nonneg _)
        exact Finset.range_subset_range.mpr hm
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 s p X‖ ≤ Cf p * SFULL := by
        refine le_trans (hCf p v) ?_
        exact mul_le_mul_of_nonneg_left (hmono (by omega)) (hCf_nn p)
      have h2 : ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapSmooth (I := I) g₀ 0 s X)‖ ≤
          C5 p * ((∑ b ∈ Finset.range (p + 3), Cf b) * SFULL) := by
        refine le_trans (hC5 p X) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hC5_nn p)
        have hb : ∀ b ∈ Finset.range (p + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 s b X‖ ≤ Cf b * SFULL := by
          intro b hb
          rw [Finset.mem_range] at hb
          refine le_trans (hCf b v) ?_
          exact mul_le_mul_of_nonneg_left (hmono (by omega)) (hCf_nn b)
        refine le_trans (Finset.sum_le_sum hb) ?_
        rw [← Finset.sum_mul]
      calc ‖iteratedCovGrad (I := I) g₀ 0 s p X‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapSmooth (I := I) g₀ 0 s X)‖
          ≤ Cf p * SFULL + C5 p * ((∑ b ∈ Finset.range (p + 3), Cf b) * SFULL) :=
            add_le_add h1 h2
        _ = (Cf p + C5 p * ∑ b ∈ Finset.range (p + 3), Cf b) * SFULL := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem armJet_abs_pairing_le (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) :
    |tensorL2Inner (I := I) (M := M) g₀ 0 s A.toFun B.toFun| ≤ ‖A‖ * ‖B‖ := by
  have h := SmoothCcTensor.inner_def (I := I) (M := M) A B
  rw [← h]
  exact abs_real_inner_le_norm A B

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem armJet_jetSum_mono (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {m m' : ℕ}
    (h : m ≤ m') (v : SmoothCcTensor g₀ 0 s) :
    ∑ q ∈ Finset.range m, ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ ≤
      ∑ q ∈ Finset.range m', ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun _ _ _ => norm_nonneg _)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem armJet_jetSum_covGrad_le (g₀ : SmoothRiemannianMetric I M) (s m : ℕ)
    (v : SmoothCcTensor g₀ 0 s) :
    ∑ q ∈ Finset.range m,
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q (covGrad (I := I) (M := M) g₀ 0 s v)‖ ≤
      ∑ q ∈ Finset.range (m + 1), ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ := by
  have hterm : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q (covGrad (I := I) (M := M) g₀ 0 s v)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 s (q + 1) v‖ := by
    intro q
    have h0 : covGrad (I := I) (M := M) g₀ 0 s v = iteratedCovGrad (I := I) g₀ 0 s 1 v := rfl
    rw [h0, armJet_norm_comp (I := I) (M := M) g₀ s 1 q v]
    exact armJet_norm_order_congr (I := I) (M := M) g₀ s (by omega) v
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  have h := Finset.sum_range_succ' (fun q => ‖iteratedCovGrad (I := I) g₀ 0 s q v‖) m
  have h0 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s 0 v‖ := norm_nonneg _
  linarith [h]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem armJet_jetProduct_le (g₀ : SmoothRiemannianMetric I M) (n p q : ℕ)
    (hp : p ≤ n + 2) (hq : q ≤ n + 2) (hpq : p + q ≤ 2 * n + 3)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
      (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) ≤
    (∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
      (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) := by
  have hnn : ∀ m : ℕ, 0 ≤ ∑ j ∈ Finset.range m, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
    fun m => Finset.sum_nonneg (fun j _ => norm_nonneg _)
  rcases le_total p q with hle | hle
  · have hp' : p ≤ n + 1 := by omega
    exact mul_le_mul (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hp' u₀)
      (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hq u₀) (hnn q) (hnn (n + 1))
  · have hq' : q ≤ n + 1 := by omega
    calc (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
        = (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) := mul_comm _ _
      _ ≤ (∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
        mul_le_mul (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hq' u₀)
          (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hp u₀) (hnn p) (hnn (n + 1))

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
