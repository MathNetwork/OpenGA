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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCurvatureCommutatorJetTower


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

private lemma bal_hs_mono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w := tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w := tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

lemma exists_iteratedCovGrad_succ_le_tensorHs_add_mul_tensorHs (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ u : SmoothCcTensor g₀ 0 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℝ) + 1) u‖ +
          Cg * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) u‖ := by
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ n
  refine ⟨Real.sqrt Cgap, Real.sqrt_nonneg _, fun u => ?_⟩
  have h := hgap u
  rw [SmoothCcTensor.norm_toL2] at h
  set A : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℝ) + 1) u‖ with hA_def
  set B : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) u‖ with hB_def
  have hA_nn : 0 ≤ A := norm_nonneg _
  have hB_nn : 0 ≤ B := norm_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  have hs : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
  nlinarith [h, mul_nonneg (mul_nonneg hA_nn (Real.sqrt_nonneg Cgap)) hB_nn]

private lemma bal_hs_logConvex (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) T₀‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) T₀‖ *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ := by
  have hv := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tensorHs_incl_norm_sq_le
    (I := I) (M := M) (g := g₀) (r := 0) (s := 2) (a := (k : ℝ))
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℝ) + 2) T₀)
  rw [tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
        (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith) T₀,
      tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
        (show (k : ℝ) ≤ (k : ℝ) + 2 by linarith) T₀] at hv
  rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring) T₀,
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring) T₀]
  exact hv

private lemma bal_hs_extreme_interp {f : ℕ → ℝ} (hf_nn : ∀ k, 0 ≤ f k)
    (hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k)
    (hmono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k')
    {B : ℝ} {m₀ : ℕ} (hB : ∀ k, k ≤ m₀ → f k ≤ B)
    {α β γ : ℕ} (hαγ : α ≤ γ) (hβγ : β ≤ γ) (hsum : α + β ≤ m₀ + γ) :
    f α * f β ≤ B * f γ := by
  have hkey : ∀ σ₁ σ₂ : ℕ, σ₁ ≤ σ₂ → σ₁ ≤ γ → σ₂ ≤ γ → σ₁ + σ₂ ≤ m₀ + γ →
      f σ₁ * f σ₂ ≤ B * f γ := by
    intro σ₁ σ₂ hle h1γ h2γ hs
    by_cases hge : γ ≤ σ₁ + σ₂
    · have hex := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.logConvex_extreme_pair
        hf_nn hlc (σ₁ := σ₁) (σ₂ := σ₂) (τ₁ := σ₁ + σ₂ - γ) (τ₂ := γ)
        (by omega) hle (by omega) (by omega)
      have hlowB : f (σ₁ + σ₂ - γ) ≤ B := hB _ (by omega)
      exact le_trans hex (mul_le_mul_of_nonneg_right hlowB (hf_nn γ))
    · have hex := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.logConvex_extreme_pair
        hf_nn hlc (σ₁ := σ₁) (σ₂ := σ₂) (τ₁ := 0) (τ₂ := σ₁ + σ₂)
        (Nat.zero_le _) hle (by omega) (by omega)
      have hf0B : f 0 ≤ B := hB 0 (Nat.zero_le _)
      have hαβγ : f (σ₁ + σ₂) ≤ f γ := hmono (by omega)
      exact le_trans hex (mul_le_mul hf0B hαβγ (hf_nn _) (le_trans (hf_nn 0) hf0B))
  rcases le_total α β with hab | hab
  · exact hkey α β hab hαγ hβγ hsum
  · rw [mul_comm]; exact hkey β α hab hβγ hαγ (by omega)

lemma bal_sqrt_pair_two (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    Real.sqrt ((a + b) ^ 2 + (c + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := by
  have hcs : a * b + c * d ≤ Real.sqrt (a ^ 2 + c ^ 2) * Real.sqrt (b ^ 2 + d ^ 2) := by
    have h1 : (a * b + c * d) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a * d - b * c)]
    have h2 : 0 ≤ a * b + c * d := by positivity
    have h3 : Real.sqrt ((a * b + c * d) ^ 2) ≤
        Real.sqrt ((a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2)) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq h2, Real.sqrt_mul (by positivity)] at h3
    exact h3
  have hrhs_nn : 0 ≤ Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := by positivity
  have hexp : (a + b) ^ 2 + (c + d) ^ 2 ≤
      (Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2)) ^ 2 := by
    have e1 : Real.sqrt (a ^ 2 + c ^ 2) ^ 2 = a ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (b ^ 2 + d ^ 2) ^ 2 = b ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith [hcs]
  calc Real.sqrt ((a + b) ^ 2 + (c + d) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hexp
    _ = Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := Real.sqrt_sq hrhs_nn

lemma bal_sqrt_mono_pair {x' x y' y : ℝ} (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (hx : x' ≤ x) (hy : y' ≤ y) :
    Real.sqrt (x' ^ 2 + y' ^ 2) ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  refine Real.sqrt_le_sqrt ?_
  have h1 : x' ^ 2 ≤ x ^ 2 := by nlinarith
  have h2 : y' ^ 2 ≤ y ^ 2 := by nlinarith
  linarith

set_option maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bal_h1_sum (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (F : ℕ → SmoothCcTensor g₀ 0 2) :
    Real.sqrt (‖∑ i ∈ Finset.range n, F i‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i)‖ ^ 2) ≤
      ∑ i ∈ Finset.range n,
        Real.sqrt (‖F i‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 (F i)‖ ^ 2) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have hcg0 : covGrad (I := I) (M := M) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := covGrad_sub (I := I) (M := M) g₀ 0 2
        (0 : SmoothCcTensor g₀ 0 2) (0 : SmoothCcTensor g₀ 0 2)
      rw [sub_self, sub_self] at h
      exact h
    rw [hcg0, norm_zero]
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hcg : covGrad (I := I) (M := M) g₀ 0 2 ((∑ i ∈ Finset.range n, F i) + F n) =
        covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i) +
          covGrad (I := I) (M := M) g₀ 0 2 (F n) :=
      covGrad_add (I := I) (M := M) g₀ 0 2 _ _
    have hm : Real.sqrt (‖(∑ i ∈ Finset.range n, F i) + F n‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 ((∑ i ∈ Finset.range n, F i) + F n)‖ ^ 2) ≤
        Real.sqrt ((‖∑ i ∈ Finset.range n, F i‖ + ‖F n‖) ^ 2 +
          (‖covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i)‖ +
            ‖covGrad (I := I) (M := M) g₀ 0 2 (F n)‖) ^ 2) := by
      rw [hcg]
      exact bal_sqrt_mono_pair (norm_nonneg _) (norm_nonneg _)
        (norm_add_le _ _) (norm_add_le _ _)
    have hp2 := bal_sqrt_pair_two ‖∑ i ∈ Finset.range n, F i‖ ‖F n‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i)‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 (F n)‖
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    refine le_trans hm (le_trans hp2 ?_)
    exact add_le_add ih (le_refl _)

lemma tensorHs_norm_mul_le_ball_mul_tensorHs (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    {u v γ : ℕ} (hv : v ≤ γ) (hsum : u + v ≤ (a + 2) + γ) (hu : u ≤ γ ∨ u ≤ a + 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((u : ℕ) : ℝ) T₀‖ *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((v : ℕ) : ℝ) T₀‖ ≤
    R₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((γ : ℕ) : ℝ) T₀‖ := by
  set f : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hf_def
  have hf_nn : ∀ k, 0 ≤ f k := fun k => norm_nonneg _
  have hf_mono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k' := by
    intro k k' hk
    exact bal_hs_mono (I := I) (M := M) g₀ (by exact_mod_cast hk) T₀
  have hf_lc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k := fun k =>
    bal_hs_logConvex (I := I) (M := M) g₀ T₀ k
  have hf_ball : ∀ k, k ≤ a + 2 → f k ≤ R₀ := by
    intro k hk
    have h1 : f k ≤ f (a + 2) := hf_mono hk
    have h2 : f (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact le_trans h1 hball
  rcases hu with huγ | hua
  · exact bal_hs_extreme_interp hf_nn hf_lc (fun {k k'} h => hf_mono h) hf_ball
      huγ hv hsum
  · have h1 : f u ≤ R₀ := hf_ball u hua
    have h2 : f v ≤ f γ := hf_mono hv
    calc f u * f v ≤ R₀ * f v := mul_le_mul_of_nonneg_right h1 (hf_nn v)
      _ ≤ R₀ * f γ := mul_le_mul_of_nonneg_left h2 hR₀

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_le_of_sq_envelope_bound (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa)
    (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (henv : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2)
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ≤
      Real.sqrt (Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
        εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ := by
  have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hrhs_nn : 0 ≤ Real.sqrt (Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
      εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ := by
    have := Real.sqrt_nonneg (Kc i)
    have := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀)
    nlinarith
  refine le_of_sq_le_sq ?_ hrhs_nn
  have hsq_sum : ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤
      (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ^ 2 :=
    bal_sq_sum_le_sum_sq _ (fun j => norm_nonneg _)
  have hKsq : Real.sqrt (Kc i) ^ 2 = Kc i := Real.sq_sqrt (hKc_nn i)
  have h := henv i
  nlinarith [h, hsq_sum, hKc_nn i, hS_nn, Real.sqrt_nonneg (Kc i), hεa_nn,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀),
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg (Kc i)) hS_nn)
      (mul_nonneg hεa_nn (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀))),
    mul_nonneg (Real.sqrt_nonneg (Kc i))
      (mul_nonneg hεa_nn (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀)))]

lemma exists_iteratedCovGrad_le_const_mul_tensorHs (g₀ : SmoothRiemannianMetric I M) :
    ∃ CJ : ℕ → ℝ, (∀ j, 0 ≤ CJ j) ∧
      ∀ (j : ℕ) (T : SmoothCcTensor g₀ 0 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
          CJ j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) T‖ := by
  classical
  have hfam := fun n => exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
    (I := I) (M := M) g₀ n
  choose CJ hCJ using hfam
  refine ⟨CJ, fun j => (hCJ j).1, fun j T => ?_⟩
  refine le_trans ?_ ((hCJ j).2 T)
  exact Finset.single_le_sum
    (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 2 b T‖)
    (fun b _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma tensorL2NormSq_le_of_pointwise_fiberNormSq_le_two_sum (g : SmoothRiemannianMetric I M)
    {rz sz : ℕ} (Z : SmoothCcTensor g rz sz)
    (n1 n2 : ℕ) (c1 c2 : ℕ → ℝ) (_hc1 : ∀ i, 0 ≤ c1 i) (_hc2 : ∀ i, 0 ≤ c2 i)
    (rw1 sw1 : ℕ → ℕ) (F1 : (i : ℕ) → SmoothCcTensor g (rw1 i) (sw1 i))
    (rw2 sw2 : ℕ → ℕ) (F2 : (i : ℕ) → SmoothCcTensor g (rw2 i) (sw2 i))
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g rz sz x (Z.toSection x) ≤
      (∑ i ∈ Finset.range n1,
        c1 i * riemannianFiberNormSq (I := I) (M := M) g (rw1 i) (sw1 i) x
          ((F1 i).toSection x)) +
      ∑ i ∈ Finset.range n2,
        c2 i * riemannianFiberNormSq (I := I) (M := M) g (rw2 i) (sw2 i) x
          ((F2 i).toSection x)) :
    ‖Z‖ ^ 2 ≤ (∑ i ∈ Finset.range n1, c1 i * ‖F1 i‖ ^ 2) +
      ∑ i ∈ Finset.range n2, c2 i * ‖F2 i‖ ^ 2 := by
  have hint1 : ∀ i ∈ Finset.range n1, MeasureTheory.Integrable
      (fun x => c1 i * riemannianFiberNormSq (I := I) (M := M) g (rw1 i) (sw1 i) x
        ((F1 i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun i _ => (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g
      (rw1 i) (sw1 i) (F1 i)).const_mul _
  have hint2 : ∀ i ∈ Finset.range n2, MeasureTheory.Integrable
      (fun x => c2 i * riemannianFiberNormSq (I := I) (M := M) g (rw2 i) (sw2 i) x
        ((F2 i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun i _ => (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g
      (rw2 i) (sw2 i) (F2 i)).const_mul _
  have hint : MeasureTheory.Integrable
      (fun x =>
        (∑ i ∈ Finset.range n1,
          c1 i * riemannianFiberNormSq (I := I) (M := M) g (rw1 i) (sw1 i) x
            ((F1 i).toSection x)) +
        ∑ i ∈ Finset.range n2,
          c2 i * riemannianFiberNormSq (I := I) (M := M) g (rw2 i) (sw2 i) x
            ((F2 i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) :=
    ((MeasureTheory.integrable_finset_sum _ hint1).add
      (MeasureTheory.integrable_finset_sum _ hint2))
  have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g rz sz
    Z _ hint hpt
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_finset_sum _ hint1)
    (MeasureTheory.integrable_finset_sum _ hint2),
    MeasureTheory.integral_finset_sum _ hint1,
    MeasureTheory.integral_finset_sum _ hint2] at h1
  refine le_trans h1 (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g
        (rw1 i) (sw1 i)]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g
        (rw2 i) (sw2 i)]

lemma smoothCcToTensorHs_norm_mono_of_le (g₀ : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g₀ 0 2)
    {j k : ℕ} (hjk : j ≤ k) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ :=
  bal_hs_mono (I := I) (M := M) g₀ (by exact_mod_cast hjk) T₀

lemma exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CC : ℕ → ℕ → ℝ, (∀ γ q, 0 ≤ CC γ q) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (γ q : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 γ
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ ≤
            CC γ q * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((γ + 2 * q + 2 : ℕ) : ℝ) T₀‖) := by
  classical
  obtain ⟨cit, hcit_nn, hcit⟩ := exists_iteratedCovGrad_connLapSmoothingIterate_window_le (I := I) (M := M) g₀ 2 2
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  refine ⟨fun γ q => cit γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)),
    fun γ q => mul_nonneg (hcit_nn γ q) (Finset.sum_nonneg (fun b _ => by
      have h1 : 0 ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h2 := Real.sqrt_nonneg (Kc b)
      have h3 := hCJ_nn (b + 2)
      nlinarith)), ?_⟩
  intro C₀ T₀ henv γ q
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((γ + 2 * q + 2 : ℕ) : ℝ) T₀‖
    with hfdef
  have hf_nn : 0 ≤ fT := norm_nonneg _
  refine le_trans (hcit γ q C₀) ?_
  have hterm : ∀ b ∈ Finset.range (γ + 2 * q + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
          (1 + fT) := by
    intro b hb
    have hbmem := Finset.mem_range.mp hb
    refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b) ?_
    have hjets : ∀ j ∈ Finset.range (b + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ CJ j * fT := by
      intro j hj
      have hjb := Finset.mem_range.mp hj
      refine le_trans (hCJ j T₀) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCJ_nn j)
      exact smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ (by omega)
    have hsum : ∑ j ∈ Finset.range (b + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (∑ j ∈ Finset.range (b + 2), CJ j) * fT := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hjets
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * fT := by
      refine le_trans (hCJ (b + 2) T₀) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCJ_nn (b + 2))
      exact smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ (by omega)
    have hCJsum_nn : 0 ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
      Finset.sum_nonneg (fun j _ => hCJ_nn j)
    nlinarith [Real.sqrt_nonneg (Kc b), hεa_nn, hCJ_nn (b + 2), hf_nn, hsum, htop,
      mul_nonneg (Real.sqrt_nonneg (Kc b)) hCJsum_nn,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg (Kc b)) hCJsum_nn) hf_nn]
  calc cit γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖
      ≤ cit γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
            (1 + fT) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (hcit_nn γ q)
    _ = cit γ q * (∑ b ∈ Finset.range (γ + 2 * q + 1),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))) *
            (1 + fT) := by
        rw [← Finset.sum_mul]
        ring

lemma riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CCS : ℕ → ℕ → ℝ, (∀ γ q, 0 ≤ CCS γ q) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (γ q : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + γ) x
              ((iteratedCovGrad (I := I) g₀ 2 2 γ
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)).toSection x) ≤
            (CCS γ q * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((γ + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 : ℕ) : ℝ) T₀‖)) ^ 2 := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  have hfam := fun γ : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 2 (2 + γ)
  choose Csh hCsh_nn hCsh using hfam
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  refine ⟨fun γ q => Csh γ * ∑ t ∈ Finset.range w, CC (γ + t) q,
    fun γ q => mul_nonneg (hCsh_nn γ) (Finset.sum_nonneg (fun t _ => hCC_nn (γ + t) q)),
    ?_⟩
  intro C₀ T₀ henv γ q x
  dsimp only
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀
    ((γ + w + 2 * q + 1 : ℕ) : ℝ) T₀‖ with hfT_def
  have hfT_nn : 0 ≤ fT := norm_nonneg _
  have h := hCsh γ (iteratedCovGrad (I := I) g₀ 2 2 γ
    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)) x
  refine le_trans h ?_
  have hterm : ∀ t ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g₀ 2 (2 + γ) t
          (iteratedCovGrad (I := I) g₀ 2 2 γ
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))‖ ^ 2 ≤
        (CC (γ + t) q * (1 + fT)) ^ 2 := by
    intro t ht
    have htw := Finset.mem_range.mp ht
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 2 (2 + γ) t
        (iteratedCovGrad (I := I) g₀ 2 2 γ
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 2 2 (γ + t)
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ 2 2 γ t
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
    rw [hcomp]
    have hb := hCC C₀ T₀ henv (γ + t) q
    have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((γ + t + 2 * q + 2 : ℕ) : ℝ) T₀‖ ≤ fT := by
      rw [hfT_def]
      exact smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ (by omega)
    have hle : ‖iteratedCovGrad (I := I) g₀ 2 2 (γ + t)
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ ≤
        CC (γ + t) q * (1 + fT) := by
      refine le_trans hb ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCC_nn (γ + t) q)
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (sq_nonneg (Csh γ))) ?_
  have hsq : ∑ t ∈ Finset.range w, (CC (γ + t) q * (1 + fT)) ^ 2 ≤
      ((∑ t ∈ Finset.range w, CC (γ + t) q) * (1 + fT)) ^ 2 := by
    have h1 : ∑ t ∈ Finset.range w, (CC (γ + t) q * (1 + fT)) ^ 2 ≤
        (∑ t ∈ Finset.range w, CC (γ + t) q * (1 + fT)) ^ 2 :=
      bal_sq_sum_le_sum_sq _ (fun t => mul_nonneg (hCC_nn (γ + t) q) (by linarith))
    rw [← Finset.sum_mul] at h1
    exact h1
  calc Csh γ ^ 2 * ∑ t ∈ Finset.range w, (CC (γ + t) q * (1 + fT)) ^ 2
      ≤ Csh γ ^ 2 * ((∑ t ∈ Finset.range w, CC (γ + t) q) * (1 + fT)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((Csh γ * ∑ t ∈ Finset.range w, CC (γ + t) q) * (1 + fT)) ^ 2 := by ring

lemma exists_iteratedCovGrad_rawTensorConnLapSmooth_le_mul_tensorHs (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDL : ℕ → ℝ, (∀ l, 0 ≤ CDL l) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2) (l : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
          CDL l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨cL, hcL_nn, hcL⟩ := exists_iteratedCovGrad_rawTensorConnLapSmooth_window_le (I := I) (M := M) g₀ 0 2
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  refine ⟨fun l => cL l * ∑ b ∈ Finset.range (l + 3), CJ b,
    fun l => mul_nonneg (hcL_nn l) (Finset.sum_nonneg (fun b _ => hCJ_nn b)), ?_⟩
  intro T₀ l
  refine le_trans (hcL l T₀) ?_
  have hterm : ∀ b ∈ Finset.range (l + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 b T₀‖ ≤
        CJ b * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ := by
    intro b hb
    have hbl := Finset.mem_range.mp hb
    refine le_trans (hCJ b T₀) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCJ_nn b)
    exact smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ (by omega)
  calc cL l * ∑ b ∈ Finset.range (l + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 b T₀‖
      ≤ cL l * ∑ b ∈ Finset.range (l + 3),
          CJ b * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (hcL_nn l)
    _ = cL l * (∑ b ∈ Finset.range (l + 3), CJ b) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ := by
        rw [← Finset.sum_mul]
        ring

lemma riemannianFiberNormSq_iteratedCovGrad_rawTensorConnLapSmooth_le_sq_tensorHs (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDS : ℕ → ℝ, (∀ l, 0 ≤ CDS l) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2) (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).toSection x) ≤
          (CDS l * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((l + (Module.finrank ℝ E / 2 + 2) + 1 : ℕ) : ℝ) T₀‖) ^ 2 := by
  classical
  obtain ⟨CDL, hCDL_nn, hCDL⟩ := exists_iteratedCovGrad_rawTensorConnLapSmooth_le_mul_tensorHs (I := I) (M := M) g₀
  have hfam := fun l : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + l)
  choose Csh hCsh_nn hCsh using hfam
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  refine ⟨fun l => Csh l * ∑ t ∈ Finset.range w, CDL (l + t),
    fun l => mul_nonneg (hCsh_nn l) (Finset.sum_nonneg (fun t _ => hCDL_nn (l + t))), ?_⟩
  intro T₀ l x
  dsimp only
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + w + 1 : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : 0 ≤ fT := norm_nonneg _
  have h := hCsh l (iteratedCovGrad (I := I) g₀ 0 2 l
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)) x
  refine le_trans h ?_
  have hterm : ∀ t ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + l) t
          (iteratedCovGrad (I := I) g₀ 0 2 l
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ ^ 2 ≤
        (CDL (l + t) * fT) ^ 2 := by
    intro t ht
    have htw := Finset.mem_range.mp ht
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 0 (2 + l) t
        (iteratedCovGrad (I := I) g₀ 0 2 l
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (l + t)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ 0 2 l t
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
    rw [hcomp]
    have hb := hCDL T₀ (l + t)
    have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((l + t + 2 : ℕ) : ℝ) T₀‖ ≤ fT := by
      rw [hfT_def]
      exact smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ (by omega)
    have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 (l + t)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤ CDL (l + t) * fT := by
      refine le_trans hb ?_
      exact mul_le_mul_of_nonneg_left hmono (hCDL_nn (l + t))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (sq_nonneg (Csh l))) ?_
  have hsq : ∑ t ∈ Finset.range w, (CDL (l + t) * fT) ^ 2 ≤
      ((∑ t ∈ Finset.range w, CDL (l + t)) * fT) ^ 2 := by
    have h1 : ∑ t ∈ Finset.range w, (CDL (l + t) * fT) ^ 2 ≤
        (∑ t ∈ Finset.range w, CDL (l + t) * fT) ^ 2 :=
      bal_sq_sum_le_sum_sq _ (fun t => mul_nonneg (hCDL_nn (l + t)) hfT_nn)
    rw [← Finset.sum_mul] at h1
    exact h1
  calc Csh l ^ 2 * ∑ t ∈ Finset.range w, (CDL (l + t) * fT) ^ 2
      ≤ Csh l ^ 2 * ((∑ t ∈ Finset.range w, CDL (l + t)) * fT) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((Csh l * ∑ t ∈ Finset.range w, CDL (l + t)) * fT) ^ 2 := by ring

lemma riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDS0 : ℕ → ℝ, (∀ β, 0 ≤ CDS0 β) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2) (β : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + β) x
            ((iteratedCovGrad (I := I) g₀ 0 2 β T₀).toSection x) ≤
          (CDS0 β * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((β + (Module.finrank ℝ E / 2 + 1) : ℕ) : ℝ) T₀‖) ^ 2 := by
  classical
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  have hfam := fun β : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + β)
  choose Csh hCsh_nn hCsh using hfam
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  refine ⟨fun β => Csh β * ∑ t ∈ Finset.range w, CJ (β + t),
    fun β => mul_nonneg (hCsh_nn β) (Finset.sum_nonneg (fun t _ => hCJ_nn (β + t))), ?_⟩
  intro T₀ β x
  dsimp only
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀
    ((β + (Module.finrank ℝ E / 2 + 1) : ℕ) : ℝ) T₀‖ with hfT_def
  have hfT_nn : 0 ≤ fT := norm_nonneg _
  have h := hCsh β (iteratedCovGrad (I := I) g₀ 0 2 β T₀) x
  refine le_trans h ?_
  have hterm : ∀ t ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + β) t
          (iteratedCovGrad (I := I) g₀ 0 2 β T₀)‖ ^ 2 ≤ (CJ (β + t) * fT) ^ 2 := by
    intro t ht
    have htw := Finset.mem_range.mp ht
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 0 (2 + β) t
        (iteratedCovGrad (I := I) g₀ 0 2 β T₀)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (β + t) T₀‖ :=
      norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ 0 2 β t T₀
    rw [hcomp]
    have hb := hCJ (β + t) T₀
    have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((β + t : ℕ) : ℝ) T₀‖ ≤ fT := by
      rw [hfT_def]
      exact smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ (by omega)
    have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 (β + t) T₀‖ ≤ CJ (β + t) * fT :=
      le_trans hb (mul_le_mul_of_nonneg_left hmono (hCJ_nn (β + t)))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (sq_nonneg (Csh β))) ?_
  have hsq : ∑ t ∈ Finset.range w, (CJ (β + t) * fT) ^ 2 ≤
      ((∑ t ∈ Finset.range w, CJ (β + t)) * fT) ^ 2 := by
    have h1 : ∑ t ∈ Finset.range w, (CJ (β + t) * fT) ^ 2 ≤
        (∑ t ∈ Finset.range w, CJ (β + t) * fT) ^ 2 :=
      bal_sq_sum_le_sum_sq _ (fun t => mul_nonneg (hCJ_nn (β + t)) hfT_nn)
    rw [← Finset.sum_mul] at h1
    exact h1
  calc Csh β ^ 2 * ∑ t ∈ Finset.range w, (CJ (β + t) * fT) ^ 2
      ≤ Csh β ^ 2 * ((∑ t ∈ Finset.range w, CJ (β + t)) * fT) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((Csh β * ∑ t ∈ Finset.range w, CJ (β + t)) * fT) ^ 2 := by ring

end BalLadder

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
