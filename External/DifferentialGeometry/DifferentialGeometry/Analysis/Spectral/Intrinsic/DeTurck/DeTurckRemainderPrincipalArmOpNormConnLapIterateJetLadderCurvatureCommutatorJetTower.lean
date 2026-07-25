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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCometricDoubleTraceTransport


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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedCovGrad_iteratedCovGrad_eq (g : SmoothRiemannianMetric I M) (r s j i : ℕ)
    (Ψ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + j) i (iteratedCovGrad (I := I) g r s j Ψ)‖ =
      ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖ := by
  have hnn1 : 0 ≤ ‖iteratedCovGrad (I := I) g r (s + j) i
      (iteratedCovGrad (I := I) g r s j Ψ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖ := norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g r (s + j) i
        (iteratedCovGrad (I := I) g r s j Ψ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖ ^ 2 := by
    simp only [SmoothCcTensor.norm_def]
    rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r
        ((s + j) + i),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r
        (s + (j + i))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g r s j i Ψ x
  nlinarith [hsq, hnn1, hnn2,
    sq_nonneg (‖iteratedCovGrad (I := I) g r (s + j) i
        (iteratedCovGrad (I := I) g r s j Ψ)‖ -
      ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖)]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bal_icg_zero_tensor (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_sub (I := I) (M := M) g r s j
    (0 : SmoothCcTensor g r s) (0 : SmoothCcTensor g r s)
  rw [sub_self, sub_self] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma normSq_le_sum_normSq_of_pointwise_fiberNormSq_window (g : SmoothRiemannianMetric I M)
    {rz sz rw : ℕ} (Z : SmoothCcTensor g rz sz) (c : ℝ) (_hc : 0 ≤ c)
    (sw : ℕ → ℕ) (F : (i : ℕ) → SmoothCcTensor g rw (sw i)) (n : ℕ)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g rz sz x (Z.toSection x) ≤
      c * ∑ i ∈ Finset.range n,
        riemannianFiberNormSq (I := I) (M := M) g rw (sw i) x ((F i).toSection x)) :
    ‖Z‖ ^ 2 ≤ c * ∑ i ∈ Finset.range n, ‖F i‖ ^ 2 := by
  have hint : MeasureTheory.Integrable
      (fun x => c * ∑ i ∈ Finset.range n,
        riemannianFiberNormSq (I := I) (M := M) g rw (sw i) x ((F i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.Integrable.const_mul ?_ c
    exact MeasureTheory.integrable_finset_sum _ (fun i _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g rw (sw i) (F i))
  have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g rz sz
    Z _ hint hpt
  rw [MeasureTheory.integral_const_mul] at h1
  rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g rw (sw i) (F i))] at h1
  refine le_trans h1 (le_of_eq ?_)
  refine congrArg (fun t => c * t) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g rw (sw i)]

lemma bal_sq_sum_le_sum_sq {n : ℕ} (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) :
    ∑ i ∈ Finset.range n, (u i) ^ 2 ≤ (∑ i ∈ Finset.range n, u i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : 0 ≤ ∑ i ∈ Finset.range n, u i :=
      Finset.sum_nonneg (fun i _ => hu i)
    nlinarith [ih, hu n, sq_nonneg (u n)]

private lemma bal_shift_sq_sum_le (u : ℕ → ℝ) (hu : ∀ b, 0 ≤ u b) (j m : ℕ) (hm : m ≤ 2) :
    ∑ i ∈ Finset.range (1 + j), (u (i + m)) ^ 2 ≤ (∑ b ∈ Finset.range (j + 3), u b) ^ 2 := by
  have h1 : ∑ i ∈ Finset.range (1 + j), (u (i + m)) ^ 2 =
      ∑ b ∈ Finset.image (· + m) (Finset.range (1 + j)), (u b) ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
  rw [h1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => sq_nonneg _))
    (bal_sq_sum_le_sum_sq u hu)
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  have := Finset.mem_range.mp hi
  exact Finset.mem_range.mpr (by omega)

set_option maxHeartbeats 1000000 in
private lemma bal_ptcRS_jet_le (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + 1) j
            (pointwiseTensorCurvRS (I := I) (M := M) g r s S)‖ ≤
          K j * ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  obtain ⟨Q₀, Q₁, Q₂, hQ⟩ :=
    exists_pointwiseTensorCurvRS_homField_jetDecomposition (I := I) (M := M) g r s
  obtain ⟨cc₀, hcc₀_nn, hcc₀⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g r s (s + 1) Q₀
  obtain ⟨cc₁, hcc₁_nn, hcc₁⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 1 (s + 1) Q₁
  obtain ⟨cc₂, hcc₂_nn, hcc₂⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 2 (s + 1) Q₂
  refine ⟨fun j => Real.sqrt (cc₀ j) + Real.sqrt (cc₁ j) + Real.sqrt (cc₂ j),
    fun j => by positivity, fun j S => ?_⟩
  set Sj : ℝ := ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g r s b S‖ with hSj_def
  have hSj_nn : 0 ≤ Sj := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have h₀ : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S)‖ ≤ Real.sqrt (cc₀ j) * Sj := by
    have hsq := normSq_le_sum_normSq_of_pointwise_fiberNormSq_window (I := I) (M := M) g
      (iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S))
      (cc₀ j) (hcc₀_nn j) (fun i => s + i)
      (fun i => iteratedCovGrad (I := I) g r s i S) (j + 1) (fun x => hcc₀ S j x)
    have hsum_le : ∑ i ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 ≤ Sj ^ 2 := by
      have := bal_shift_sq_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b => norm_nonneg _) j 0 (by omega)
      simpa [Nat.add_comm 1 j] using this
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hSj_nn)
    rw [mul_pow, Real.sq_sqrt (hcc₀_nn j)]
    exact le_trans hsq (mul_le_mul_of_nonneg_left hsum_le (hcc₀_nn j))
  have h₁ : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
        (iteratedCovGrad (I := I) g r s 1 S))‖ ≤ Real.sqrt (cc₁ j) * Sj := by
    have hsq := normSq_le_sum_normSq_of_pointwise_fiberNormSq_window (I := I) (M := M) g
      (iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (iteratedCovGrad (I := I) g r s 1 S)))
      (cc₁ j) (hcc₁_nn j) (fun i => s + (i + 1))
      (fun i => iteratedCovGrad (I := I) g r s (i + 1) S) (1 + j) (fun x => hcc₁ S j x)
    have hsum_le : ∑ i ∈ Finset.range (1 + j),
        ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 ≤ Sj ^ 2 :=
      bal_shift_sq_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b => norm_nonneg _) j 1 (by omega)
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hSj_nn)
    rw [mul_pow, Real.sq_sqrt (hcc₁_nn j)]
    exact le_trans hsq (mul_le_mul_of_nonneg_left hsum_le (hcc₁_nn j))
  have h₂ : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) Q₂
        (iteratedCovGrad (I := I) g r s 2 S))‖ ≤ Real.sqrt (cc₂ j) * Sj := by
    have hsq := normSq_le_sum_normSq_of_pointwise_fiberNormSq_window (I := I) (M := M) g
      (iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) Q₂
          (iteratedCovGrad (I := I) g r s 2 S)))
      (cc₂ j) (hcc₂_nn j) (fun i => s + (i + 2))
      (fun i => iteratedCovGrad (I := I) g r s (i + 2) S) (1 + j) (fun x => hcc₂ S j x)
    have hsum_le : ∑ i ∈ Finset.range (1 + j),
        ‖iteratedCovGrad (I := I) g r s (i + 2) S‖ ^ 2 ≤ Sj ^ 2 :=
      bal_shift_sq_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b => norm_nonneg _) j 2 (by omega)
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hSj_nn)
    rw [mul_pow, Real.sq_sqrt (hcc₂_nn j)]
    exact le_trans hsq (mul_le_mul_of_nonneg_left hsum_le (hcc₂_nn j))
  have htri : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S)‖ ≤
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S)‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (covGrad (I := I) (M := M) g r s S))‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) Q₂
          (iteratedCovGrad (I := I) g r s 2 S))‖ := by
    rw [hQ S, iteratedCovGrad_add, iteratedCovGrad_add]
    refine le_trans (norm_add_le _ _) ?_
    have h := norm_add_le
      (iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S))
      (iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (covGrad (I := I) (M := M) g r s S)))
    linarith
  have hcov1 : covGrad (I := I) (M := M) g r s S = iteratedCovGrad (I := I) g r s 1 S := rfl
  rw [hcov1] at htri
  refine le_trans htri ?_
  calc ‖iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S)‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (iteratedCovGrad (I := I) g r s 1 S))‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) Q₂
          (iteratedCovGrad (I := I) g r s 2 S))‖
      ≤ Real.sqrt (cc₀ j) * Sj + Real.sqrt (cc₁ j) * Sj + Real.sqrt (cc₂ j) * Sj :=
        add_le_add (add_le_add h₀ h₁) h₂
    _ = (Real.sqrt (cc₀ j) + Real.sqrt (cc₁ j) + Real.sqrt (cc₂ j)) * Sj := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_eq_iteratedCovGrad_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s X = iteratedCovGrad (I := I) g r s 1 X := rfl

private lemma bal_shift_sum_le (u : ℕ → ℝ) (hu : ∀ b, 0 ≤ u b) (k m n : ℕ)
    (hkm : ∀ i < k, i + m < n) :
    ∑ b ∈ Finset.range k, u (b + m) ≤ ∑ b ∈ Finset.range n, u b := by
  have h1 : ∑ b ∈ Finset.range k, u (b + m) =
      ∑ b ∈ Finset.image (· + m) (Finset.range k), u b := by
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hu b)
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_range.mpr (hkm i (Finset.mem_range.mp hi))

private lemma bal_comm_tower (g : SmoothRiemannianMetric I M) (r s : ℕ) (m : ℕ) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + m) j
            (rawTensorConnLapSmooth (I := I) g r (s + m)
                (iteratedCovGrad (I := I) g r s m S) -
              iteratedCovGrad (I := I) g r s m
                (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          K j * ∑ b ∈ Finset.range (m + j + 2), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  induction m with
  | zero =>
    refine ⟨fun _ => 0, fun _ => le_refl 0, fun j S => ?_⟩
    have hz : rawTensorConnLapSmooth (I := I) g r (s + 0)
          (iteratedCovGrad (I := I) g r s 0 S) -
        iteratedCovGrad (I := I) g r s 0 (rawTensorConnLapSmooth (I := I) g r s S) = 0 := by
      simp only [iteratedCovGrad_zero]
      exact sub_self _
    rw [hz, bal_icg_zero_tensor, norm_zero, zero_mul]
  | succ m ih =>
    obtain ⟨Km, hKm_nn, hKm⟩ := ih
    obtain ⟨Kp, hKp_nn, hKp⟩ := bal_ptcRS_jet_le (I := I) (M := M) g r (s + m)
    refine ⟨fun j => Kp j + Km (j + 1), fun j => add_nonneg (hKp_nn j) (hKm_nn (j + 1)),
      fun j S => ?_⟩
    set Y : SmoothCcTensor g r (s + m) := iteratedCovGrad (I := I) g r s m S with hY_def
    set Cm : SmoothCcTensor g r (s + m) :=
      rawTensorConnLapSmooth (I := I) g r (s + m) Y -
        iteratedCovGrad (I := I) g r s m (rawTensorConnLapSmooth (I := I) g r s S)
      with hCm_def
    have hid : rawTensorConnLapSmooth (I := I) g r (s + (m + 1))
          (iteratedCovGrad (I := I) g r s (m + 1) S) -
        iteratedCovGrad (I := I) g r s (m + 1) (rawTensorConnLapSmooth (I := I) g r s S) =
        pointwiseTensorCurvRS (I := I) (M := M) g r (s + m) Y +
          covGrad (I := I) (M := M) g r (s + m) Cm := by
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ, hCm_def]
      rw [covGrad_sub (I := I) (M := M) g r (s + m)]
      change rawTensorConnLapSmooth (I := I) g r ((s + m) + 1)
          (covGrad (I := I) (M := M) g r (s + m) Y) -
          covGrad (I := I) (M := M) g r (s + m)
            (iteratedCovGrad (I := I) g r s m (rawTensorConnLapSmooth (I := I) g r s S)) =
        (rawTensorConnLapSmooth (I := I) g r ((s + m) + 1)
            (covGrad (I := I) (M := M) g r (s + m) Y) -
          covGrad (I := I) (M := M) g r (s + m)
            (rawTensorConnLapSmooth (I := I) g r (s + m) Y)) +
        (covGrad (I := I) (M := M) g r (s + m) (rawTensorConnLapSmooth (I := I) g r (s + m) Y) -
          covGrad (I := I) (M := M) g r (s + m)
            (iteratedCovGrad (I := I) g r s m (rawTensorConnLapSmooth (I := I) g r s S)))
      abel
    rw [hid, iteratedCovGrad_add]
    refine le_trans (norm_add_le _ _) ?_
    have hpiece1 : ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
        (pointwiseTensorCurvRS (I := I) (M := M) g r (s + m) Y)‖ ≤
        Kp j * ∑ b ∈ Finset.range ((m + 1) + j + 2),
          ‖iteratedCovGrad (I := I) g r s b S‖ := by
      refine le_trans (hKp j Y) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKp_nn j)
      have hcomp : ∀ b, ‖iteratedCovGrad (I := I) g r (s + m) b Y‖ =
          ‖iteratedCovGrad (I := I) g r s (m + b) S‖ := fun b =>
        norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g r s m b S
      calc ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g r (s + m) b Y‖
          = ∑ b ∈ Finset.range (j + 3),
              ‖iteratedCovGrad (I := I) g r s (b + m) S‖ := by
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [hcomp b, show m + b = b + m from by omega]
        _ ≤ ∑ b ∈ Finset.range ((m + 1) + j + 2),
              ‖iteratedCovGrad (I := I) g r s b S‖ :=
            bal_shift_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
              (fun b => norm_nonneg _) (j + 3) m ((m + 1) + j + 2) (fun i hi => by omega)
    have hpiece2 : ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
        (covGrad (I := I) (M := M) g r (s + m) Cm)‖ ≤
        Km (j + 1) * ∑ b ∈ Finset.range ((m + 1) + j + 2),
          ‖iteratedCovGrad (I := I) g r s b S‖ := by
      have hnc : ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
          (covGrad (I := I) (M := M) g r (s + m) Cm)‖ =
          ‖iteratedCovGrad (I := I) g r (s + m) (1 + j) Cm‖ := by
        rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g r (s + m) Cm]
        exact norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g r (s + m) 1 j Cm
      rw [hnc, show 1 + j = j + 1 from by omega]
      refine le_trans (hKm (j + 1) S) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKm_nn (j + 1))
      have hsub : Finset.range (m + (j + 1) + 2) ⊆ Finset.range ((m + 1) + j + 2) :=
        fun x hx => Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hx; omega)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => norm_nonneg _)
    calc ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
          (pointwiseTensorCurvRS (I := I) (M := M) g r (s + m) Y)‖ +
        ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
          (covGrad (I := I) (M := M) g r (s + m) Cm)‖
        ≤ Kp j * ∑ b ∈ Finset.range ((m + 1) + j + 2),
              ‖iteratedCovGrad (I := I) g r s b S‖ +
            Km (j + 1) * ∑ b ∈ Finset.range ((m + 1) + j + 2),
              ‖iteratedCovGrad (I := I) g r s b S‖ := add_le_add hpiece1 hpiece2
      _ = (Kp j + Km (j + 1)) * ∑ b ∈ Finset.range ((m + 1) + j + 2),
            ‖iteratedCovGrad (I := I) g r s b S‖ := by ring

set_option maxHeartbeats 1600000 in
private lemma bal_G2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ S : SmoothCcTensor g r s,
      ‖rawTensorConnLapSmooth (I := I) g r s S‖ ≤
        ‖iteratedCovGrad (I := I) g r s 2 S‖ +
          c * (‖iteratedCovGrad (I := I) g r s 1 S‖ + ‖S‖) := by
  classical
  obtain ⟨Kp, hKp_nn, hKp⟩ := bal_ptcRS_jet_le (I := I) (M := M) g r s
  refine ⟨Kp 0 + 1, by linarith [hKp_nn 0], fun S => ?_⟩
  have hW := weitzenbock_integrated_covGrad_l2_normSq_rs (I := I) (M := M) g r s S
  have hicg2 : covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S) =
      iteratedCovGrad (I := I) g r s 2 S := rfl
  have hicg1 : covGrad (I := I) (M := M) g r s S = iteratedCovGrad (I := I) g r s 1 S := rfl
  have hptc : rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
      covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) =
      pointwiseTensorCurvRS (I := I) (M := M) g r s S := rfl
  rw [hicg2, hptc] at hW
  rw [show tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
      (iteratedCovGrad (I := I) g r s 2 S).toFun =
      ‖iteratedCovGrad (I := I) g r s 2 S‖ from (SmoothCcTensor.norm_def _).symm] at hW
  rw [show tensorL2Norm (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s S).toFun =
      ‖rawTensorConnLapSmooth (I := I) g r s S‖ from (SmoothCcTensor.norm_def _).symm] at hW
  have hCS : |tensorL2Inner (I := I) (M := M) g r (s + 1)
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
      (covGrad (I := I) (M := M) g r s S).toFun| ≤
      ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ *
        ‖covGrad (I := I) (M := M) g r s S‖ := by
    have h := DifferentialGeometry.Integral.L2.abs_tensorL2Inner_le (I := I) (M := M) g r (s + 1)
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
      (covGrad (I := I) (M := M) g r s S).toFun
      (SmoothCcTensor.memL2_toFun (I := I) (M := M)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S))
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) (covGrad (I := I) (M := M) g r s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S)
        (covGrad (I := I) (M := M) g r s S))
    rw [show tensorL2Norm (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun =
        ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ from
      (SmoothCcTensor.norm_def _).symm] at h
    rw [show tensorL2Norm (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S).toFun =
        ‖covGrad (I := I) (M := M) g r s S‖ from (SmoothCcTensor.norm_def _).symm] at h
    exact h
  have hptc_le : ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ ≤
      Kp 0 * (‖S‖ + ‖iteratedCovGrad (I := I) g r s 1 S‖ +
        ‖iteratedCovGrad (I := I) g r s 2 S‖) := by
    have h := hKp 0 S
    have h0 : ‖iteratedCovGrad (I := I) g r (s + 1) 0
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S)‖ =
        ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ := by
      rw [iteratedCovGrad_zero]
    have hsum : ∑ b ∈ Finset.range (0 + 3), ‖iteratedCovGrad (I := I) g r s b S‖ =
        ‖S‖ + ‖iteratedCovGrad (I := I) g r s 1 S‖ +
          ‖iteratedCovGrad (I := I) g r s 2 S‖ := by
      rw [show (0 + 3 : ℕ) = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, iteratedCovGrad_zero]
    rw [h0, hsum] at h
    exact h
  set a0 : ℝ := ‖S‖ with ha0
  set a1 : ℝ := ‖iteratedCovGrad (I := I) g r s 1 S‖ with ha1
  set a2 : ℝ := ‖iteratedCovGrad (I := I) g r s 2 S‖ with ha2
  have ha0_nn : 0 ≤ a0 := norm_nonneg _
  have ha1_nn : 0 ≤ a1 := norm_nonneg _
  have ha2_nn : 0 ≤ a2 := norm_nonneg _
  have hgrad_eq : ‖covGrad (I := I) (M := M) g r s S‖ = a1 := by rw [hicg1]
  have hsq : ‖rawTensorConnLapSmooth (I := I) g r s S‖ ^ 2 ≤
      a2 ^ 2 + Kp 0 * (a0 + a1 + a2) * a1 := by
    have h1 : ‖rawTensorConnLapSmooth (I := I) g r s S‖ ^ 2 =
        a2 ^ 2 + tensorL2Inner (I := I) (M := M) g r (s + 1)
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by linarith [hW]
    rw [h1]
    have h2 : tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun ≤
        Kp 0 * (a0 + a1 + a2) * a1 := by
      refine le_trans (le_abs_self _) (le_trans hCS ?_)
      rw [hgrad_eq]
      exact mul_le_mul_of_nonneg_right hptc_le (by rw [← hgrad_eq]; exact norm_nonneg _)
    linarith
  have hrhs_nn : 0 ≤ a2 + (Kp 0 + 1) * (a1 + a0) := by
    have := hKp_nn 0
    nlinarith
  refine le_of_sq_le_sq ?_ hrhs_nn
  have e1 : Kp 0 * a2 * a1 ≤ 2 * (Kp 0 + 1) * a2 * (a1 + a0) := by
    nlinarith [mul_nonneg ha2_nn ha1_nn, mul_nonneg ha2_nn ha0_nn, hKp_nn 0,
      mul_nonneg (mul_nonneg (hKp_nn 0) ha2_nn) ha0_nn,
      mul_nonneg (mul_nonneg (hKp_nn 0) ha2_nn) ha1_nn]
  have e2 : Kp 0 * (a0 + a1) * a1 ≤ (Kp 0 + 1) ^ 2 * (a1 + a0) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (hKp_nn 0) (add_nonneg ha0_nn ha1_nn)) ha0_nn,
      mul_nonneg (mul_nonneg (hKp_nn 0) (hKp_nn 0)) (sq_nonneg (a1 + a0)),
      mul_nonneg (hKp_nn 0) (sq_nonneg (a1 + a0)), sq_nonneg (a1 + a0)]
  have esplit : Kp 0 * (a0 + a1 + a2) * a1 =
      Kp 0 * (a0 + a1) * a1 + Kp 0 * a2 * a1 := by ring
  have expand : (a2 + (Kp 0 + 1) * (a1 + a0)) ^ 2 =
      a2 ^ 2 + 2 * (Kp 0 + 1) * a2 * (a1 + a0) + (Kp 0 + 1) ^ 2 * (a1 + a0) ^ 2 := by ring
  rw [expand]
  linarith [hsq, e1, e2, esplit]

lemma exists_iteratedCovGrad_rawTensorConnLapSmooth_window_le (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℝ, (∀ b, 0 ≤ c b) ∧
      ∀ (b : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
          c b * ∑ b' ∈ Finset.range (b + 3), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
  classical
  have hG2fam : ∀ b : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ Y : SmoothCcTensor g r (s + b),
      ‖rawTensorConnLapSmooth (I := I) g r (s + b) Y‖ ≤
        ‖iteratedCovGrad (I := I) g r (s + b) 2 Y‖ +
          c * (‖iteratedCovGrad (I := I) g r (s + b) 1 Y‖ + ‖Y‖) :=
    fun b => bal_G2 (I := I) (M := M) g r (s + b)
  choose cG hcG_nn hcG using hG2fam
  have hTfam : ∀ m : ℕ, ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + m) j
            (rawTensorConnLapSmooth (I := I) g r (s + m)
                (iteratedCovGrad (I := I) g r s m S) -
              iteratedCovGrad (I := I) g r s m
                (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          K j * ∑ b ∈ Finset.range (m + j + 2), ‖iteratedCovGrad (I := I) g r s b S‖ :=
    fun m => bal_comm_tower (I := I) (M := M) g r s m
  choose KT hKT_nn hKT using hTfam
  refine ⟨fun b => 1 + 2 * cG b + KT b 0,
    fun b => by have := hcG_nn b; have := hKT_nn b 0; linarith, fun b S => ?_⟩
  set Sb : ℝ := ∑ b' ∈ Finset.range (b + 3), ‖iteratedCovGrad (I := I) g r s b' S‖
    with hSb_def
  have hSb_nn : 0 ≤ Sb := Finset.sum_nonneg (fun b' _ => norm_nonneg _)
  have hsingle : ∀ b' : ℕ, b' < b + 3 →
      ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Sb := by
    intro b' hb'
    exact Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
      (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
  have hdecomp : iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S) =
      rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
        (rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)) := by
    abel
  rw [hdecomp]
  refine le_trans (norm_sub_le _ _) ?_
  have hpiece1 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S)‖ ≤ (1 + 2 * cG b) * Sb := by
    refine le_trans (hcG b (iteratedCovGrad (I := I) g r s b S)) ?_
    have h2 : ‖iteratedCovGrad (I := I) g r (s + b) 2 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g r s b 2 S
    have h1 : ‖iteratedCovGrad (I := I) g r (s + b) 1 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g r s b 1 S
    rw [h2, h1]
    have e2 : ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ ≤ Sb := hsingle (b + 2) (by omega)
    have e1 : ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ ≤ Sb := hsingle (b + 1) (by omega)
    have e0 : ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Sb := hsingle b (by omega)
    nlinarith [hcG_nn b, hSb_nn]
  have hpiece2 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S) -
        iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
      KT b 0 * Sb := by
    have h := hKT b 0 S
    have h0 : ‖iteratedCovGrad (I := I) g r (s + b) 0
        (rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S))‖ =
        ‖rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S)‖ := by
      rw [iteratedCovGrad_zero]
    rw [h0] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKT_nn b 0)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b' _ _ => norm_nonneg _)
    exact fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  calc ‖rawTensorConnLapSmooth (I := I) g r (s + b)
        (iteratedCovGrad (I := I) g r s b S)‖ +
      ‖rawTensorConnLapSmooth (I := I) g r (s + b)
          (iteratedCovGrad (I := I) g r s b S) -
        iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖
      ≤ (1 + 2 * cG b) * Sb + KT b 0 * Sb := add_le_add hpiece1 hpiece2
    _ = (1 + 2 * cG b + KT b 0) * Sb := by ring

omit [CompactSpace M] [I.Boundaryless] in
private lemma bal_iter_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 1 S =
      S - rawTensorConnLapSmooth (I := I) g r s S := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, oneMinusConnLapSmoothIter_succ,
    oneMinusConnLapSmoothIter_zero]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
private lemma bal_iter_succ_inner (g : SmoothRiemannianMetric I M) (r s : ℕ) (q : ℕ)
    (S : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (q + 1) S =
      oneMinusConnLapSmoothIter (I := I) g r s q S -
        oneMinusConnLapSmoothIter (I := I) g r s q
          (rawTensorConnLapSmooth (I := I) g r s S) := by
  rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g r s q 1 S,
    bal_iter_one (I := I) (M := M) g r s S]
  exact oneMinusConnLapSmoothIter_sub (I := I) (M := M) g r s q S
    (rawTensorConnLapSmooth (I := I) g r s S)

private lemma bal_sum_lap_jets (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (cL : ℕ → ℝ) (hcL_nn : ∀ b, 0 ≤ cL b)
    (hcL : ∀ (b : ℕ) (S : SmoothCcTensor g r s),
      ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
        cL b * ∑ b' ∈ Finset.range (b + 3), ‖iteratedCovGrad (I := I) g r s b' S‖)
    (K : ℕ) (S : SmoothCcTensor g r s) :
    ∑ b ∈ Finset.range K,
        ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
      (∑ b ∈ Finset.range K, cL b) *
        ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
  have hbig_nn : 0 ≤ ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ :=
    Finset.sum_nonneg (fun b' _ => norm_nonneg _)
  calc ∑ b ∈ Finset.range K,
      ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖
      ≤ ∑ b ∈ Finset.range K, cL b *
          ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        refine le_trans (hcL b S) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hcL_nn b)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b' _ _ => norm_nonneg _)
        have hbK := Finset.mem_range.mp hb
        exact fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
    _ = (∑ b ∈ Finset.range K, cL b) *
          ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
        rw [Finset.sum_mul]

lemma exists_iteratedCovGrad_connLapSmoothingIterate_window_le (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ γ q, 0 ≤ c γ q) ∧
      ∀ (γ q : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s γ (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ ≤
          c γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  obtain ⟨cL, hcL_nn, hcL⟩ := exists_iteratedCovGrad_rawTensorConnLapSmooth_window_le (I := I) (M := M) g r s
  have hmain : ∀ q : ℕ, ∃ c : ℕ → ℝ, (∀ γ, 0 ≤ c γ) ∧
      ∀ (γ : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s γ (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ ≤
          c γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
    intro q
    induction q with
    | zero =>
      refine ⟨fun _ => 1, fun _ => zero_le_one, fun γ S => ?_⟩
      rw [oneMinusConnLapSmoothIter_zero, one_mul]
      exact Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    | succ q ih =>
      obtain ⟨cq, hcq_nn, hcq⟩ := ih
      refine ⟨fun γ => cq γ * (1 + ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b),
        fun γ => mul_nonneg (hcq_nn γ)
          (by have : 0 ≤ ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b :=
                Finset.sum_nonneg (fun b _ => hcL_nn b)
              linarith),
        fun γ S => ?_⟩
      have hsplit := bal_iter_succ_inner (I := I) (M := M) g r s q S
      rw [hsplit, iteratedCovGrad_sub]
      refine le_trans (norm_sub_le _ _) ?_
      have hbig_nn : 0 ≤ ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
          ‖iteratedCovGrad (I := I) g r s b S‖ :=
        Finset.sum_nonneg (fun b _ => norm_nonneg _)
      have hmono : ∑ b ∈ Finset.range (γ + 2 * q + 1),
          ‖iteratedCovGrad (I := I) g r s b S‖ ≤
          ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
            ‖iteratedCovGrad (I := I) g r s b S‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
          (fun b _ _ => norm_nonneg _)
      have h1 : ‖iteratedCovGrad (I := I) g r s γ
          (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ ≤
          cq γ * ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
            ‖iteratedCovGrad (I := I) g r s b S‖ :=
        le_trans (hcq γ S) (mul_le_mul_of_nonneg_left hmono (hcq_nn γ))
      have h2 : ‖iteratedCovGrad (I := I) g r s γ
          (oneMinusConnLapSmoothIter (I := I) g r s q
            (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          (cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
            ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
              ‖iteratedCovGrad (I := I) g r s b S‖ := by
        refine le_trans (hcq γ (rawTensorConnLapSmooth (I := I) g r s S)) ?_
        have hsum := bal_sum_lap_jets (I := I) (M := M) g r s cL hcL_nn hcL
          (γ + 2 * q + 1) S
        have hK2 : γ + 2 * q + 1 + 2 = γ + 2 * (q + 1) + 1 := by omega
        rw [hK2] at hsum
        calc cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1),
            ‖iteratedCovGrad (I := I) g r s b
              (rawTensorConnLapSmooth (I := I) g r s S)‖
            ≤ cq γ * ((∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
                ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                  ‖iteratedCovGrad (I := I) g r s b S‖) :=
              mul_le_mul_of_nonneg_left hsum (hcq_nn γ)
          _ = (cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
                ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                  ‖iteratedCovGrad (I := I) g r s b S‖ := by ring
      calc ‖iteratedCovGrad (I := I) g r s γ
            (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ +
          ‖iteratedCovGrad (I := I) g r s γ
            (oneMinusConnLapSmoothIter (I := I) g r s q
              (rawTensorConnLapSmooth (I := I) g r s S))‖
          ≤ cq γ * ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                ‖iteratedCovGrad (I := I) g r s b S‖ +
              (cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
                ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                  ‖iteratedCovGrad (I := I) g r s b S‖ := add_le_add h1 h2
        _ = cq γ * (1 + ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
              ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                ‖iteratedCovGrad (I := I) g r s b S‖ := by ring
  choose cfun hcfun_nn hcfun using hmain
  exact ⟨fun γ q => cfun q γ, fun γ q => hcfun_nn q γ, fun γ q S => hcfun q γ S⟩

private lemma bal_lap_jets_exact (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℝ, (∀ b, 0 ≤ c b) ∧
      ∀ (b : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
          ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ +
            c b * ∑ b' ∈ Finset.range (b + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
  classical
  have hG2fam : ∀ b : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ Y : SmoothCcTensor g r (s + b),
      ‖rawTensorConnLapSmooth (I := I) g r (s + b) Y‖ ≤
        ‖iteratedCovGrad (I := I) g r (s + b) 2 Y‖ +
          c * (‖iteratedCovGrad (I := I) g r (s + b) 1 Y‖ + ‖Y‖) :=
    fun b => bal_G2 (I := I) (M := M) g r (s + b)
  choose cG hcG_nn hcG using hG2fam
  have hTfam : ∀ m : ℕ, ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + m) j
            (rawTensorConnLapSmooth (I := I) g r (s + m)
                (iteratedCovGrad (I := I) g r s m S) -
              iteratedCovGrad (I := I) g r s m
                (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          K j * ∑ b ∈ Finset.range (m + j + 2), ‖iteratedCovGrad (I := I) g r s b S‖ :=
    fun m => bal_comm_tower (I := I) (M := M) g r s m
  choose KT hKT_nn hKT using hTfam
  refine ⟨fun b => cG b + cG b + KT b 0,
    fun b => by have := hcG_nn b; have := hKT_nn b 0; linarith, fun b S => ?_⟩
  set Sb : ℝ := ∑ b' ∈ Finset.range (b + 2), ‖iteratedCovGrad (I := I) g r s b' S‖
    with hSb_def
  have hSb_nn : 0 ≤ Sb := Finset.sum_nonneg (fun b' _ => norm_nonneg _)
  have hsingle : ∀ b' : ℕ, b' < b + 2 →
      ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Sb := by
    intro b' hb'
    exact Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
      (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
  have hdecomp : iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S) =
      rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
        (rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)) := by
    abel
  rw [hdecomp]
  refine le_trans (norm_sub_le _ _) ?_
  have hpiece1 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S)‖ ≤
      ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ + (cG b + cG b) * Sb := by
    refine le_trans (hcG b (iteratedCovGrad (I := I) g r s b S)) ?_
    have h2 : ‖iteratedCovGrad (I := I) g r (s + b) 2 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g r s b 2 S
    have h1 : ‖iteratedCovGrad (I := I) g r (s + b) 1 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g r s b 1 S
    rw [h2, h1]
    have e1 : ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ ≤ Sb := hsingle (b + 1) (by omega)
    have e0 : ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Sb := hsingle b (by omega)
    nlinarith [hcG_nn b]
  have hpiece2 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S) -
        iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
      KT b 0 * Sb := by
    have h := hKT b 0 S
    have h0 : ‖iteratedCovGrad (I := I) g r (s + b) 0
        (rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S))‖ =
        ‖rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S)‖ := by
      rw [iteratedCovGrad_zero]
    rw [h0] at h
    exact h
  linarith [hpiece1, hpiece2]

lemma bal_Ccore (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℝ, (∀ p, 0 ≤ c p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g r s),
        ‖oneMinusConnLapSmoothIter (I := I) g r s p S‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p) S‖ +
            c p * ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g r s b S‖ ∧
        ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p S)‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ +
            c p * ∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  obtain ⟨cL, hcL_nn, hcL⟩ := exists_iteratedCovGrad_rawTensorConnLapSmooth_window_le (I := I) (M := M) g r s
  obtain ⟨cE, hcE_nn, hcE⟩ := bal_lap_jets_exact (I := I) (M := M) g r s
  have hmain : ∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ S : SmoothCcTensor g r s,
        ‖oneMinusConnLapSmoothIter (I := I) g r s p S‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p) S‖ +
            c * ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g r s b S‖ ∧
        ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p S)‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ +
            c * ∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
    intro p
    induction p with
    | zero =>
      refine ⟨0, le_refl 0, fun S => ⟨?_, ?_⟩⟩
      · rw [oneMinusConnLapSmoothIter_zero]
        simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
        rw [iteratedCovGrad_zero]
      · rw [oneMinusConnLapSmoothIter_zero]
        change ‖covGrad (I := I) (M := M) g r s S‖ ≤
          ‖iteratedCovGrad (I := I) g r s 1 S‖ +
            0 * ∑ b ∈ Finset.range 1, ‖iteratedCovGrad (I := I) g r s b S‖
        rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g r s S]
        simp
    | succ p ih =>
      obtain ⟨cp, hcp_nn, hcp⟩ := ih
      set CL : ℝ := ∑ b ∈ Finset.range (2 * p + 1), cL b with hCL_def
      have hCL_nn : 0 ≤ CL := Finset.sum_nonneg (fun b _ => hcL_nn b)
      refine ⟨1 + cE (2 * p) + cE (2 * p + 1) + cp * (2 + CL),
        by nlinarith [hcE_nn (2 * p), hcE_nn (2 * p + 1)], fun S => ?_⟩
      set ΔS : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
      have hsplit := bal_iter_succ_inner (I := I) (M := M) g r s p S
      constructor
      · set Big : ℝ := ∑ b ∈ Finset.range (2 * (p + 1)),
          ‖iteratedCovGrad (I := I) g r s b S‖ with hBig_def
        have hBig_nn : 0 ≤ Big := Finset.sum_nonneg (fun b _ => norm_nonneg _)
        have hsingleB : ∀ b' : ℕ, b' < 2 * (p + 1) →
            ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Big := fun b' hb' =>
          Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
            (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
        have hmonoB : ∑ b ∈ Finset.range (2 * p),
            ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Big :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
            (fun b _ _ => norm_nonneg _)
        rw [hsplit]
        refine le_trans (norm_sub_le _ _) ?_
        have h1 := (hcp S).1
        have h2 := (hcp ΔS).1
        have htop : ‖iteratedCovGrad (I := I) g r s (2 * p) ΔS‖ ≤
            ‖iteratedCovGrad (I := I) g r s (2 * (p + 1)) S‖ + cE (2 * p) * Big := by
          have h := hcE (2 * p) S
          rw [show 2 * p + 2 = 2 * (p + 1) from by omega, ← hBig_def] at h
          exact h
        have hlow : ∑ b ∈ Finset.range (2 * p),
            ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ CL * Big := by
          have h := bal_sum_lap_jets (I := I) (M := M) g r s cL hcL_nn hcL (2 * p) S
          have hle1 : ∑ b ∈ Finset.range (2 * p), cL b ≤ CL := by
            rw [hCL_def]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
              (fun b _ _ => hcL_nn b)
          rw [show 2 * p + 2 = 2 * (p + 1) from by omega, ← hBig_def] at h
          refine le_trans h (mul_le_mul_of_nonneg_right hle1 hBig_nn)
        have htop_prev : ‖iteratedCovGrad (I := I) g r s (2 * p) S‖ ≤ Big :=
          hsingleB (2 * p) (by omega)
        calc ‖oneMinusConnLapSmoothIter (I := I) g r s p S‖ +
            ‖oneMinusConnLapSmoothIter (I := I) g r s p ΔS‖
            ≤ (‖iteratedCovGrad (I := I) g r s (2 * p) S‖ +
                cp * ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g r s b S‖) +
              (‖iteratedCovGrad (I := I) g r s (2 * p) ΔS‖ +
                cp * ∑ b ∈ Finset.range (2 * p),
                  ‖iteratedCovGrad (I := I) g r s b ΔS‖) := add_le_add h1 h2
          _ ≤ ‖iteratedCovGrad (I := I) g r s (2 * (p + 1)) S‖ +
              (1 + cE (2 * p) + cE (2 * p + 1) + cp * (2 + CL)) * Big := by
            have e1 : cp * ∑ b ∈ Finset.range (2 * p),
                ‖iteratedCovGrad (I := I) g r s b S‖ ≤ cp * Big :=
              mul_le_mul_of_nonneg_left hmonoB hcp_nn
            have e2 : cp * ∑ b ∈ Finset.range (2 * p),
                ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ cp * (CL * Big) :=
              mul_le_mul_of_nonneg_left hlow hcp_nn
            nlinarith [hcE_nn (2 * p + 1), hcp_nn, hCL_nn, hBig_nn, htop, htop_prev]
      · set Big : ℝ := ∑ b ∈ Finset.range (2 * (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g r s b S‖ with hBig_def
        have hBig_nn : 0 ≤ Big := Finset.sum_nonneg (fun b _ => norm_nonneg _)
        have hsingleB : ∀ b' : ℕ, b' < 2 * (p + 1) + 1 →
            ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Big := fun b' hb' =>
          Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
            (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
        have hmonoB : ∑ b ∈ Finset.range (2 * p + 1),
            ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Big :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
            (fun b _ _ => norm_nonneg _)
        rw [hsplit, covGrad_sub]
        refine le_trans (norm_sub_le _ _) ?_
        have h1 := (hcp S).2
        have h2 := (hcp ΔS).2
        have htop : ‖iteratedCovGrad (I := I) g r s (2 * p + 1) ΔS‖ ≤
            ‖iteratedCovGrad (I := I) g r s (2 * (p + 1) + 1) S‖ +
              cE (2 * p + 1) * Big := by
          have h := hcE (2 * p + 1) S
          rw [show 2 * p + 1 + 2 = 2 * (p + 1) + 1 from by omega, ← hBig_def] at h
          exact h
        have hlow : ∑ b ∈ Finset.range (2 * p + 1),
            ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ CL * Big := by
          have h := bal_sum_lap_jets (I := I) (M := M) g r s cL hcL_nn hcL (2 * p + 1) S
          rw [show 2 * p + 1 + 2 = 2 * (p + 1) + 1 from by omega, ← hBig_def,
            ← hCL_def] at h
          exact h
        have htop_prev : ‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ ≤ Big :=
          hsingleB (2 * p + 1) (by omega)
        calc ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p S)‖ +
            ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p ΔS)‖
            ≤ (‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ +
                cp * ∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g r s b S‖) +
              (‖iteratedCovGrad (I := I) g r s (2 * p + 1) ΔS‖ +
                cp * ∑ b ∈ Finset.range (2 * p + 1),
                  ‖iteratedCovGrad (I := I) g r s b ΔS‖) := add_le_add h1 h2
          _ ≤ ‖iteratedCovGrad (I := I) g r s (2 * (p + 1) + 1) S‖ +
              (1 + cE (2 * p) + cE (2 * p + 1) + cp * (2 + CL)) * Big := by
            have e1 : cp * ∑ b ∈ Finset.range (2 * p + 1),
                ‖iteratedCovGrad (I := I) g r s b S‖ ≤ cp * Big :=
              mul_le_mul_of_nonneg_left hmonoB hcp_nn
            have e2 : cp * ∑ b ∈ Finset.range (2 * p + 1),
                ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ cp * (CL * Big) :=
              mul_le_mul_of_nonneg_left hlow hcp_nn
            nlinarith [hcE_nn (2 * p), hcp_nn, hCL_nn, hBig_nn, htop, htop_prev]
  choose cfun hcfun_nn hcfun using hmain
  exact ⟨cfun, hcfun_nn, fun p S => hcfun p S⟩

end BalLadder

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
