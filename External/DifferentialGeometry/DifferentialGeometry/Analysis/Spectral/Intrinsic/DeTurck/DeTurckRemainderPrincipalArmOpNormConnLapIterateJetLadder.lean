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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCurvatureCommutatorJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCoefficientFieldSobolevEnvelope

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

set_option maxHeartbeats 1600000 in
private lemma bal_gridcore (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    (q j dc d₂ dw : ℕ) (hdc : dc ≤ 1) (hd₂ : d₂ ≤ 2)
    (hdw : dw ≤ Module.finrank ℝ E / 2 + 3)
    (hdw' : Module.finrank ℝ E / 2 + 1 ≤ dw)
    {sz : ℕ} (Z : SmoothCcTensor g₀ 0 sz)
    (sc : ℕ → ℕ) (Cf : (i : ℕ) → SmoothCcTensor g₀ 2 (sc i))
    (cC cCS : ℕ → ℝ) (hcC_nn : ∀ i, 0 ≤ cC i) (hcCS_nn : ∀ i, 0 ≤ cCS i)
    (hCL2 : ∀ i, ‖Cf i‖ ≤ cC i *
      (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((dc + i + 2 * q + 2 : ℕ) : ℝ) T₀‖))
    (hCsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) ≤
        (cCS i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((dc + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 : ℕ) : ℝ) T₀‖)) ^ 2)
    (sd : ℕ → ℕ) (Df : (l : ℕ) → SmoothCcTensor g₀ 0 (sd l))
    (cD cDS : ℕ → ℝ) (hcD_nn : ∀ l, 0 ≤ cD l) (_hcDS_nn : ∀ l, 0 ≤ cDS l)
    (hDL2 : ∀ l, ‖Df l‖ ≤ cD l *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + d₂ : ℕ) : ℝ) T₀‖)
    (hDsup : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        (cDS l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dw : ℕ) : ℝ) T₀‖) ^ 2)
    (G : ℝ) (hG : 0 ≤ G)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
      G * ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)) :
    ‖Z‖ ≤ Real.sqrt (G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2))) *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set γ' : ℕ := j + 2 * q + 3 with hγ_def
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    have h1 : fT k ≤ fT (a + 2) := hfT_mono hk
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact le_trans h1 hball
  set SApred : ℕ → Prop := fun i => dc + i + w + 2 * q + 1 ≤ a + 2 with hSA_def
  have hSAdec : DecidablePred SApred := fun i => by
    rw [hSA_def]
    infer_instance
  set c1 : ℝ := G * ∑ i ∈ (Finset.range (j + 1)).filter SApred,
    (cCS i * (1 + R₀)) ^ 2 with hc1_def
  have hc1_nn : 0 ≤ c1 :=
    mul_nonneg hG (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  set c2 : ℕ → ℝ := fun i => G * (if SApred i then 0 else
    ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) with hc2_def
  have hc2_nn : ∀ i, 0 ≤ c2 i := by
    intro i
    rw [hc2_def]
    dsimp only
    split_ifs with h
    · simp
    · exact mul_nonneg hG (Finset.sum_nonneg (fun l _ => sq_nonneg _))
  have hpt2 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
      (∑ l ∈ Finset.range (j + 1),
        c1 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)) +
      ∑ i ∈ Finset.range (j + 1),
        c2 i * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
          ((Cf i).toSection x) := by
    intro x
    refine le_trans (hpt x) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (j + 1)) SApred]
    have hSApart : ∑ i ∈ (Finset.range (j + 1)).filter SApred,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        (∑ i ∈ (Finset.range (j + 1)).filter SApred, (cCS i * (1 + R₀)) ^ 2) *
          ∑ l ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiSA : SApred i := (Finset.mem_filter.mp hi).2
      have hCf_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
          ((Cf i).toSection x) ≤ (cCS i * (1 + R₀)) ^ 2 := by
        refine le_trans (hCsup i x) ?_
        have hf_le : fT (dc + i + w + 2 * q + 1) ≤ R₀ := hfT_ball _ hiSA
        have h1 : cCS i * (1 + fT (dc + i + w + 2 * q + 1)) ≤ cCS i * (1 + R₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (hcCS_nn i)
          linarith
        refine pow_le_pow_left₀ ?_ h1 2
        have := hfT_nn (dc + i + w + 2 * q + 1)
        have := hcCS_nn i
        positivity
      have hDsum_le : ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
          ∑ l ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (sd l) x _)
      have hD_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (sd l) x _)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)
          ≤ (cCS i * (1 + R₀)) ^ 2 *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
            mul_le_mul_of_nonneg_right hCf_le hD_nn
        _ ≤ (cCS i * (1 + R₀)) ^ 2 *
            ∑ l ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
            mul_le_mul_of_nonneg_left hDsum_le (sq_nonneg _)
    have hSBpart : ∑ i ∈ (Finset.range (j + 1)).filter (fun i => ¬ SApred i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        ∑ i ∈ Finset.range (j + 1),
          (if SApred i then 0 else
            ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum (fun i hi => ?_)
      split_ifs with h
      · simp
      · have hDsum_le : ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
            ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2 :=
          Finset.sum_le_sum (fun l _ => hDsup l x)
        have hC_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
            ((Cf i).toSection x) :=
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (sc i) x _
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)
            ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2 :=
              mul_le_mul_of_nonneg_left hDsum_le hC_nn
          _ = (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) := by
              ring
    have hGmul := mul_le_mul_of_nonneg_left (add_le_add hSApart hSBpart) hG
    refine le_trans hGmul (le_of_eq ?_)
    rw [mul_add]
    congr 1
    · rw [← Finset.mul_sum, hc1_def]
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hc2_def]
      dsimp only
      ring
  have hL2 := tensorL2NormSq_le_of_pointwise_fiberNormSq_le_two_sum (I := I) (M := M) g₀ Z (j + 1) (j + 1)
    (fun _ => c1) c2 (fun _ => hc1_nn) hc2_nn
    (fun _ => 0) sd Df (fun _ => 2) sc Cf hpt2
  have hSAfinal : ∑ l ∈ Finset.range (j + 1), c1 * ‖Df l‖ ^ 2 ≤
      (G * (∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2)) * fT γ' ^ 2 := by
    have hc1_le : c1 ≤ G * ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2 := by
      rw [hc1_def]
      refine mul_le_mul_of_nonneg_left ?_ hG
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg _)
    have hterm : ∀ l ∈ Finset.range (j + 1), ‖Df l‖ ^ 2 ≤ (cD l) ^ 2 * fT γ' ^ 2 := by
      intro l hl
      have hlj := Finset.mem_range.mp hl
      have h1 : ‖Df l‖ ≤ cD l * fT γ' := by
        refine le_trans (hDL2 l) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hcD_nn l)
        exact hfT_mono (by omega)
      calc ‖Df l‖ ^ 2 ≤ (cD l * fT γ') ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (cD l) ^ 2 * fT γ' ^ 2 := by ring
    calc ∑ l ∈ Finset.range (j + 1), c1 * ‖Df l‖ ^ 2
        ≤ ∑ l ∈ Finset.range (j + 1),
            (G * ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
              ((cD l) ^ 2 * fT γ' ^ 2) := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul hc1_le (hterm l hl) (sq_nonneg _) ?_
          exact mul_nonneg hG (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      _ = (G * (∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
            (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2)) * fT γ' ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
  have hSBfinal : ∑ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2 ≤
      (G * (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) * fT γ' ^ 2 := by
    have hterm : ∀ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2 ≤
        G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2) *
          fT γ' ^ 2) := by
      intro i hi
      have hij := Finset.mem_range.mp hi
      rw [hc2_def]
      dsimp only
      split_ifs with hSA
      · have h0 : G * 0 * ‖Cf i‖ ^ 2 = 0 := by ring
        rw [h0]
        have : (0:ℝ) ≤ G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
            (1 + R₀) ^ 2) * fT γ' ^ 2) := by positivity
        linarith
      · have hSB : ¬ (dc + i + w + 2 * q + 1 ≤ a + 2) := hSA
        have hcell : ∀ l ∈ Finset.range (j + 1 - i),
            (cDS l * fT (l + dw)) ^ 2 * ‖Cf i‖ ^ 2 ≤
              (cDS l) ^ 2 * ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by
          intro l hl
          have hlj := Finset.mem_range.mp hl
          have hCf : ‖Cf i‖ ≤ cC i * (1 + fT (dc + i + 2 * q + 2)) := hCL2 i
          have hscore : fT (l + dw) * (1 + fT (dc + i + 2 * q + 2)) ≤ (1 + R₀) * fT γ' := by
            have hu_le : l + dw ≤ γ' := by omega
            have h1 : fT (l + dw) * 1 = fT (l + dw) := by ring
            have h2 : fT (l + dw) ≤ fT γ' := hfT_mono hu_le
            have h3 : fT (l + dw) * fT (dc + i + 2 * q + 2) ≤ R₀ * fT γ' := by
              have := tensorHs_norm_mul_le_ball_mul_tensorHs (I := I) (M := M) g₀ a hR₀ T₀ hball
                (u := l + dw) (v := dc + i + 2 * q + 2) (γ := γ')
                (by omega) (by omega) (Or.inl hu_le)
              exact this
            calc fT (l + dw) * (1 + fT (dc + i + 2 * q + 2))
                = fT (l + dw) + fT (l + dw) * fT (dc + i + 2 * q + 2) := by ring
              _ ≤ fT γ' + R₀ * fT γ' := add_le_add h2 h3
              _ = (1 + R₀) * fT γ' := by ring
          have hprod : fT (l + dw) * ‖Cf i‖ ≤ cDS l * 0 + cC i * ((1 + R₀) * fT γ') := by
            have h1 : fT (l + dw) * ‖Cf i‖ ≤
                fT (l + dw) * (cC i * (1 + fT (dc + i + 2 * q + 2))) :=
              mul_le_mul_of_nonneg_left hCf (hfT_nn _)
            have h2 : fT (l + dw) * (cC i * (1 + fT (dc + i + 2 * q + 2))) =
                cC i * (fT (l + dw) * (1 + fT (dc + i + 2 * q + 2))) := by ring
            rw [h2] at h1
            refine le_trans h1 ?_
            have h3 := mul_le_mul_of_nonneg_left hscore (hcC_nn i)
            linarith
          have hprod' : fT (l + dw) * ‖Cf i‖ ≤ cC i * ((1 + R₀) * fT γ') := by
            linarith [hprod]
          have hboth_nn : 0 ≤ fT (l + dw) * ‖Cf i‖ :=
            mul_nonneg (hfT_nn _) (norm_nonneg _)
          have hsq := pow_le_pow_left₀ hboth_nn hprod' 2
          calc (cDS l * fT (l + dw)) ^ 2 * ‖Cf i‖ ^ 2
              = (cDS l) ^ 2 * (fT (l + dw) * ‖Cf i‖) ^ 2 := by ring
            _ ≤ (cDS l) ^ 2 * (cC i * ((1 + R₀) * fT γ')) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
            _ = (cDS l) ^ 2 * ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by ring
        have hsum : (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            ‖Cf i‖ ^ 2 ≤
            (∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by
          rw [Finset.sum_mul]
          refine le_trans (Finset.sum_le_sum hcell) ?_
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
            (fun l _ _ => sq_nonneg _)
        calc G * (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            ‖Cf i‖ ^ 2
            = G * ((∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
              ‖Cf i‖ ^ 2) := by ring
          _ ≤ G * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2))) :=
              mul_le_mul_of_nonneg_left hsum hG
          _ = G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              (1 + R₀) ^ 2) * fT γ' ^ 2) := by ring
    calc ∑ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2
        ≤ ∑ i ∈ Finset.range (j + 1),
            G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              (1 + R₀) ^ 2) * fT γ' ^ 2) := Finset.sum_le_sum hterm
      _ = (G * (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
            ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) * fT γ' ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  have htot : ‖Z‖ ^ 2 ≤ (G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
      (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
      (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2))) * fT γ' ^ 2 := by
    refine le_trans hL2 ?_
    have := add_le_add hSAfinal hSBfinal
    refine le_trans this (le_of_eq ?_)
    ring
  have hCB_nn : 0 ≤ G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
      (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
      (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) := by
    have h1 : 0 ≤ ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h2 : 0 ≤ ∑ l ∈ Finset.range (j + 1), (cD l) ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have h3 : 0 ≤ ∑ i ∈ Finset.range (j + 1), (cC i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h4 : 0 ≤ ∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have h5 : (0:ℝ) ≤ (1 + R₀) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 h2, mul_nonneg h3 (mul_nonneg h4 h5)]
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (hfT_nn γ'))
  rw [mul_pow, Real.sq_sqrt hCB_nn]
  exact htot

private lemma bal_fT_index_congr (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) {k k' : ℕ} (h : k = k') :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k' : ℕ) : ℝ) T₀‖ := by
  subst h; rfl

set_option maxHeartbeats 1600000 in
private lemma bal_block1 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CB : ℕ → ℕ → ℝ, (∀ q j, 0 ≤ CB q j) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q j : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CDL, hCDL_nn, hCDL⟩ := exists_iteratedCovGrad_rawTensorConnLapSmooth_le_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS, hCDS_nn, hCDS⟩ := riemannianFiberNormSq_iteratedCovGrad_rawTensorConnLapSmooth_le_sq_tensorHs (I := I) (M := M) g₀
  refine ⟨fun q j => Real.sqrt (diagonalGridGrowthFactor (E := E) j *
      ((∑ i ∈ Finset.range (j + 1), (CCS i q * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (CDL l) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (CC i q) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (CDS l) ^ 2) * (1 + R₀) ^ 2))),
    fun q j => Real.sqrt_nonneg _, ?_⟩
  intro C₀ T₀ hball henv q j
  refine bal_gridcore (I := I) (M := M) g₀ a ha_super hR₀ T₀ hball q j 0 2
    (Module.finrank ℝ E / 2 + 3) (by omega) (by omega) (by omega) (by omega)
    (iteratedCovGrad (I := I) g₀ 0 2 j
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
    (fun i => 2 + i)
    (fun i => iteratedCovGrad (I := I) g₀ 2 2 i
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))
    (fun i => CC i q) (fun i => CCS i q) (fun i => hCC_nn i q) (fun i => hCCS_nn i q)
    (fun i => ?_) (fun i x => ?_)
    (fun l => 2 + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 2 l
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
    CDL CDS hCDL_nn hCDS_nn
    (fun l => ?_) (fun l x => ?_)
    (diagonalGridGrowthFactor (E := E) j) (appCcGdiag_nonneg (E := E) j)
    (fun x => ?_)
  · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀ (show 0 + i + 2 * q + 2 = i + 2 * q + 2
      from by omega)]
    exact hCC C₀ T₀ henv i q
  · have h := hCCS C₀ T₀ henv i q x
    rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
      (show 0 + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 =
        i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 from by omega)]
    exact h
  · exact hCDL T₀ l
  · have h := hCDS T₀ l x
    rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
      (show l + (Module.finrank ℝ E / 2 + 3) = l + (Module.finrank ℝ E / 2 + 2) + 1
        from by omega)]
    exact h
  · exact riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀ 2 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀) j x

private lemma bal_DTwrap (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDT : ℝ, 0 ≤ CDT ∧ ∀ (Y : SmoothCcTensor g₀ 0 (2 + 2)) (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2) Y)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) j * CDT * ∑ l' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) := by
  classical
  have hfam := fun i' : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ (2 + 2) (2 + i')
  choose Csh hCsh_nn hCsh using hfam
  set DT₂ : SmoothCcTensor g₀ (2 + 2) 2 := DeTurck.cometricDoubleTraceField (I := I) g₀ 2
    with hDT_def
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  have hvanish : ∀ k : ℕ, 1 ≤ k → ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 k DT₂‖ = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show 1 + k' = k' + 1 from by omega]
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ (2 + 2) 2 DT₂
      (DeTurck.cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2) k']
    exact norm_zero
  set CDT : ℝ := Csh 0 ^ 2 * ∑ t ∈ Finset.range w,
    ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 t DT₂‖ ^ 2 with hCDT_def
  have hCDT_nn : 0 ≤ CDT :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun t _ => sq_nonneg _))
  refine ⟨CDT, hCDT_nn, fun Y j x => ?_⟩
  have hgrid := riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + 2) 2
    DT₂ Y j x
  refine le_trans hgrid ?_
  have hDTsup : ∀ i' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) ≤
        (if i' = 0 then CDT else 0) := by
    intro i'
    match i' with
    | 0 =>
      rw [if_pos rfl]
      have h := hCsh 0 (iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂) x
      refine le_trans h ?_
      rw [hCDT_def]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))
      have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + 0) t
          (iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂)‖ =
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 (0 + t) DT₂‖ :=
        norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ (2 + 2) 2 0 t DT₂
      rw [hcomp, show (0 + t : ℕ) = t from by omega]
    | (k + 1) =>
      rw [if_neg (Nat.succ_ne_zero k)]
      have h := hCsh (k + 1) (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂) x
      refine le_trans h ?_
      have hz : ∑ t ∈ Finset.range w,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + (k + 1)) t
            (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂)‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero (fun t _ => ?_)
        have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + (k + 1)) t
            (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂)‖ =
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 ((k + 1) + t) DT₂‖ :=
          norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ (2 + 2) 2 (k + 1) t DT₂
        rw [hcomp, hvanish ((k + 1) + t) (by omega)]
        norm_num
      rw [hz, mul_zero]
  have hterm : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) *
        ∑ l' ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) ≤
      (if i' = 0 then CDT * ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) else 0) := by
    intro i' hi'
    have hY_nn : 0 ≤ ∑ l' ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) :=
      Finset.sum_nonneg (fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
    split_ifs with h0
    · subst h0
      refine mul_le_mul (le_trans (hDTsup 0) (by rw [if_pos rfl])) ?_ hY_nn hCDT_nn
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l' _ _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
      exact fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega)
    · have hle := hDTsup i'
      rw [if_neg h0] at hle
      have hrf_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (2 + 2) _ x _
      have hzero : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) = 0 :=
        le_antisymm hle hrf_nn
      rw [hzero, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) j)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (j + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  rw [← mul_assoc]

private lemma bal_grid_mono {A B : ℕ → ℝ} (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {l' j : ℕ} (hl' : l' ≤ j) :
    ∑ α ∈ Finset.range (l' + 1), A α * ∑ β ∈ Finset.range (l' + 1 - α), B β ≤
      ∑ α ∈ Finset.range (j + 1), A α * ∑ β ∈ Finset.range (j + 1 - α), B β := by
  refine le_trans (Finset.sum_le_sum (fun α _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
      (fun α _ _ => mul_nonneg (hA α) (Finset.sum_nonneg (fun β _ => hB β))))
  refine mul_le_mul_of_nonneg_left ?_ (hA α)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
    (fun β _ _ => hB β)

set_option maxHeartbeats 3200000 in
private lemma bal_block23 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CB : ℕ → ℕ → ℝ, (∀ q j, 0 ≤ CB q j) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q j : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDT, hCDT_nn, hCDT⟩ := bal_DTwrap (I := I) (M := M) g₀
  set n : ℕ := Module.finrank ℝ E with hn_def
  set G : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * CDT *
    ((j + 1 : ℕ) * (diagonalGridGrowthFactor (E := E) j * n)) with hG_def
  have hG_nn : ∀ j, 0 ≤ G j := fun j => by
    have h1 := appCcGdiag_nonneg (E := E) j
    have h2 : (0:ℝ) ≤ (j + 1 : ℕ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  refine ⟨fun q j => Real.sqrt (G j *
      ((∑ i ∈ Finset.range (j + 1), (CCS (1 + i) q * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (CJ (1 + l)) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (CC (1 + i) q) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (CDS0 (1 + l)) ^ 2) * (1 + R₀) ^ 2))),
    fun q j => Real.sqrt_nonneg _, ?_⟩
  intro C₀ T₀ hball henv q j
  set Ĉq : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀
    with hĈq_def
  have hcore : ∀ {sz : ℕ} (Z : SmoothCcTensor g₀ 0 sz),
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
        G j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
            ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x)) →
      ‖Z‖ ≤ Real.sqrt (G j *
        ((∑ i ∈ Finset.range (j + 1), (CCS (1 + i) q * (1 + R₀)) ^ 2) *
          (∑ l ∈ Finset.range (j + 1), (CJ (1 + l)) ^ 2) +
          (∑ i ∈ Finset.range (j + 1), (CC (1 + i) q) ^ 2) *
            ((∑ l ∈ Finset.range (j + 1), (CDS0 (1 + l)) ^ 2) * (1 + R₀) ^ 2))) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
    intro sz Z hpt
    refine bal_gridcore (I := I) (M := M) g₀ a ha_super hR₀ T₀ hball q j 1 1
      (Module.finrank ℝ E / 2 + 2) (by omega) (by omega) (by omega) (by omega)
      Z (fun i => 2 + (1 + i))
      (fun i => iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq)
      (fun i => CC (1 + i) q) (fun i => CCS (1 + i) q)
      (fun i => hCC_nn (1 + i) q) (fun i => hCCS_nn (1 + i) q)
      (fun i => ?_) (fun i x => ?_)
      (fun l => 2 + (1 + l))
      (fun l => iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀)
      (fun l => CJ (1 + l)) (fun l => CDS0 (1 + l))
      (fun l => hCJ_nn (1 + l)) (fun l => hCDS0_nn (1 + l))
      (fun l => ?_) (fun l x => ?_)
      (G j) (hG_nn j) hpt
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show 1 + i + 2 * q + 2 = (1 + i) + 2 * q + 2 from by omega)]
      exact hCC C₀ T₀ henv (1 + i) q
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show 1 + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 =
          (1 + i) + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 from by omega)]
      exact hCCS C₀ T₀ henv (1 + i) q x
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show (l + 1 : ℕ) = 1 + l from by omega)]
      exact hCJ (1 + l) T₀
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show l + (Module.finrank ℝ E / 2 + 2) =
          (1 + l) + (Module.finrank ℝ E / 2 + 1) from by omega)]
      exact hCDS0 T₀ (1 + l) x
  have hGd_mono : ∀ {l' : ℕ}, l' ≤ j → diagonalGridGrowthFactor (E := E) l' ≤ diagonalGridGrowthFactor (E := E) j := by
    intro l' hl'
    have hbase : (1 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by
      have : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith
    exact pow_le_pow_right₀ hbase hl'
  have hYgrid : ∀ (Cf' : SmoothCcTensor g₀ (2 + 1) (2 + 2)),
      (∀ (α : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
            ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α Cf').toSection x) ≤
          (n : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
            ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x)) →
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))).toSection x) ≤
          G j * ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x) := by
    intro Cf' hCf' x
    have hβconv : ∀ (β : ℕ),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) := by
      intro β
      rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 0 2 T₀]
      exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 β T₀ x
    set gridj : ℝ := ∑ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x) with hgridj_def
    have hgridj_nn : 0 ≤ gridj :=
      Finset.sum_nonneg (fun i _ => mul_nonneg
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 _ x _)
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)))
    have hY : ∀ l' : ℕ, l' ≤ j →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj := by
      intro l' hl'
      have hgrid := riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀
        (2 + 1) (2 + 2) Cf' (covGrad (I := I) (M := M) g₀ 0 2 T₀) l' x
      refine le_trans hgrid ?_
      have hterm : ∀ α ∈ Finset.range (l' + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
              ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α Cf').toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
                ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) ≤
          (n : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x)) := by
        intro α _
        have hsum_eq : ∑ β ∈ Finset.range (l' + 1 - α),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
                (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) =
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) :=
          Finset.sum_congr rfl (fun β _ => hβconv β)
        rw [hsum_eq]
        have hs_nn : 0 ≤ ∑ β ∈ Finset.range (l' + 1 - α),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) :=
          Finset.sum_nonneg (fun β _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
        have h := mul_le_mul_of_nonneg_right (hCf' α x) hs_nn
        refine le_trans h (le_of_eq ?_)
        ring
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
        (appCcGdiag_nonneg (E := E) l')) ?_
      have hpull : ∑ α ∈ Finset.range (l' + 1),
          (n : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x)) =
          (n : ℝ) * ∑ α ∈ Finset.range (l' + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
              ∑ β ∈ Finset.range (l' + 1 - α),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) := by
        rw [Finset.mul_sum]
      rw [hpull]
      have hmono := bal_grid_mono
        (A := fun α => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
          ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x))
        (B := fun β => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x))
        (fun α => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 _ x _)
        (fun β => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _) hl'
      calc diagonalGridGrowthFactor (E := E) l' * ((n : ℝ) * ∑ α ∈ Finset.range (l' + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
              ∑ β ∈ Finset.range (l' + 1 - α),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x))
          ≤ diagonalGridGrowthFactor (E := E) l' * ((n : ℝ) * gridj) := by
            refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) l')
            exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
        _ ≤ diagonalGridGrowthFactor (E := E) j * ((n : ℝ) * gridj) := by
            refine mul_le_mul_of_nonneg_right (hGd_mono hl') ?_
            exact mul_nonneg (Nat.cast_nonneg _) hgridj_nn
        _ = diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj := by ring
    have hDT := hCDT (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)) j x
    refine le_trans hDT ?_
    have hsum_le : ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
        ((j + 1 : ℕ) : ℝ) * (diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj) := by
      have h1 : ∀ l' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj :=
        fun l' hl' => hY l' (by have := Finset.mem_range.mp hl'; omega)
      refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc diagonalGridGrowthFactor (E := E) j * CDT * ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) j * CDT *
            (((j + 1 : ℕ) : ℝ) * (diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj)) := by
          refine mul_le_mul_of_nonneg_left hsum_le ?_
          exact mul_nonneg (appCcGdiag_nonneg (E := E) j) hCDT_nn
      _ = G j * gridj := by
          rw [hG_def]
          push_cast
          ring
  constructor
  · refine hcore (iteratedCovGrad (I := I) g₀ 0 2 j
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 2 2 Ĉq))
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)))) ?_
    refine hYgrid (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 2 2 Ĉq)) ?_
    intro α x
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 2 2 Ĉq) α x
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
    rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 2 2 Ĉq]
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 2 2 1 α Ĉq x
  · refine hcore (iteratedCovGrad (I := I) g₀ 0 2 j
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq))
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)))) ?_
    refine hYgrid (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)) ?_
    intro α x
    have hconv : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
        ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + (1 + α)) x
          ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 1) (1 + α)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)).toSection x) := by
      rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)]
      exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ (2 + 1) (2 + 1) 1 α
        (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq) x
    rw [hconv]
    exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 2 Ĉq (1 + α) x

private lemma bal_slotExt_norm (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g₀ r s) :
    ‖slotExtend (I := I) (M := M) g₀ r s Φ‖ ≤
      Real.sqrt (Module.finrank ℝ E) * ‖Φ‖ := by
  have hsq := normSq_le_sum_normSq_of_pointwise_fiberNormSq_window (I := I) (M := M) g₀
    (slotExtend (I := I) (M := M) g₀ r s Φ) (Module.finrank ℝ E : ℝ) (Nat.cast_nonneg _)
    (fun _ => s) (fun _ => Φ) 1 (fun x => ?_)
  · rw [Finset.sum_range_one] at hsq
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hsq
  · rw [Finset.sum_range_one]
    have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r s Φ 0 x
    rw [show iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) 0
        (slotExtend (I := I) (M := M) g₀ r s Φ) =
      slotExtend (I := I) (M := M) g₀ r s Φ from iteratedCovGrad_zero _ _ _ _] at h
    rw [show iteratedCovGrad (I := I) g₀ r s 0 Φ = Φ from iteratedCovGrad_zero _ _ _ _] at h
    exact h

set_option maxHeartbeats 3200000 in
lemma exists_connLapIterate_appCc_sobolevHs_bound (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KT : ℕ → ℝ, (∀ p, 0 ≤ KT p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ), 0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          ‖operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ≤
            B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ +
              KT p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (I := I) (M := M) g₀
  obtain ⟨c22, hc22_nn, hc22⟩ := bal_Ccore (I := I) (M := M) g₀ 2 2
  have hgapfam := fun k : ℕ => exists_iteratedCovGrad_succ_le_tensorHs_add_mul_tensorHs (I := I) (M := M) g₀ k
  choose Cg hCg_nn hCg using hgapfam
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set KE1 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) + εa * CJ (2 * p + 2)) +
    c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE1_def
  have hKE1_nn : ∀ p, 0 ≤ KE1 p := by
    intro p
    have h1 : ∀ b : ℕ, 0 ≤ Real.sqrt (Kc b) *
        (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2) := by
      intro b
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (b + 2)) => hCJ_nn j)
      have := Real.sqrt_nonneg (Kc b)
      have := hCJ_nn (b + 2)
      nlinarith
    rw [hKE1_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p)) => h1 b)
    have := h1 (2 * p)
    have := hc22_nn p
    nlinarith
  refine ⟨fun p => CCS 0 p * (1 + R₀) * CJ 0 +
      (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
        CDS0 0 * (1 + R₀) * KE1 p),
    fun p => ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ CCS 0 p * (1 + R₀) * CJ 0 :=
      mul_nonneg (mul_nonneg (hCCS_nn 0 p) (by linarith)) (hCJ_nn 0)
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa * Cg (2 * p + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (hCg_nn _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * KE1 p :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith)) (hKE1_nn p)
    linarith
  intro C₀ T₀ B hB hball hdata henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    refine le_trans (hfT_mono hk) ?_
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2]
    exact hball
  set Φp : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀
    with hΦp_def
  by_cases hcase : w + 2 * p + 2 ≤ a + 2
  · have hsupΦ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (Φp.toSection x) ≤ (CCS 0 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 0 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have hf_le : fT (0 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 0 p * (1 + fT (0 + w + 2 * p + 1)) ≤ CCS 0 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 0 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (0 + w + 2 * p + 1)
      have := hCCS_nn 0 p
      nlinarith
    have hX : ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
        CCS 0 p * (1 + R₀) * ‖T₀‖ := by
      refine operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2 2
        Φp T₀ (CCS 0 p * (1 + R₀)) ?_ hsupΦ
      have := hCCS_nn 0 p
      nlinarith
    have hT0 : ‖T₀‖ ≤ CJ 0 * fT (2 * p + 1) := by
      have h := hCJ 0 T₀
      rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 0)
    have htot : ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
        CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := by
      refine le_trans hX ?_
      have h := mul_le_mul_of_nonneg_left hT0 (by
        have := hCCS_nn 0 p
        nlinarith : (0:ℝ) ≤ CCS 0 p * (1 + R₀))
      calc CCS 0 p * (1 + R₀) * ‖T₀‖
          ≤ CCS 0 p * (1 + R₀) * (CJ 0 * fT (2 * p + 1)) := h
        _ = CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := by ring
    have hBεa_nn : 0 ≤ B * εa * fT (2 * p + 2) :=
      mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
    have hrest_nn : 0 ≤ (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
        CDS0 0 * (1 + R₀) * KE1 p) * fT (2 * p + 1) := by
      have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa * Cg (2 * p + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (hCg_nn _)
      have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * KE1 p :=
        mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith)) (hKE1_nn p)
      exact mul_nonneg (by linarith) (hfT_nn _)
    calc ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖
        ≤ CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := htot
      _ ≤ B * εa * fT (2 * p + 2) +
          (CCS 0 p * (1 + R₀) * CJ 0 +
            (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
              CDS0 0 * (1 + R₀) * KE1 p)) * fT (2 * p + 1) := by
          have h1 : 0 ≤ (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
              CDS0 0 * (1 + R₀) * KE1 p) * fT (2 * p + 1) := hrest_nn
          nlinarith [hBεa_nn]
  · set Bh : ℝ := CDS0 0 * fT (0 + (n / 2 + 1)) with hBh_def
    have hBh_nn : 0 ≤ Bh := mul_nonneg (hCDS0_nn 0) (hfT_nn _)
    set Bm : ℝ := min B Bh with hBm_def
    have hBm_nn : 0 ≤ Bm := le_min hB hBh_nn
    have hBm_pt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Bm ^ 2 := by
      intro x
      rcases le_total B Bh with h | h
      · rw [hBm_def, min_eq_left h]
        exact hdata x
      · rw [hBm_def, min_eq_right h]
        have hd := hCDS0 T₀ 0 x
        rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
          iteratedCovGrad_zero _ _ _ _] at hd
        exact hd
    have hX : ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤ ‖Φp‖ * Bm :=
      operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀ 2 2
        Φp T₀ Bm hBm_nn hBm_pt
    have hΦcore := (hc22 p C₀).1
    have henvsum : ∀ (k : ℕ), k ≤ 2 * p + 2 →
        ∑ j ∈ Finset.range k, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (∑ j ∈ Finset.range k, CJ j) * fT (2 * p + 1) := by
      intro k hk
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hjk := Finset.mem_range.mp hj
      refine le_trans (hCJ j T₀) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn j)
    set f₁ : ℝ := fT (2 * p + 1) with hf₁_def
    have hf₁_nn : 0 ≤ f₁ := hfT_nn _
    set u : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ with hu_def
    have hu_nn : 0 ≤ u := norm_nonneg _
    have hone_aux : ∀ (X : ℝ), 0 ≤ X → 1 + X * f₁ ≤ (1 + X) * (1 + f₁) := by
      intro X hX
      nlinarith
    have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
        (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)) *
          (1 + f₁) + εa * u := by
      refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv
        (2 * p)) ?_
      have hs := henvsum (2 * p + 2) (by omega)
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₁) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p)))
      have hueq : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ = u := rfl
      nlinarith [hεa_nn, hu_nn]
    have hlowC : ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (∑ b ∈ Finset.range (2 * p),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))) *
          (1 + f₁) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hb2p := Finset.mem_range.mp hb
      refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b) ?_
      have hs := henvsum (b + 2) (by omega)
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (b + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₁) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc b))
      have h3 : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f₁ := by
        refine le_trans (hCJ (b + 2) T₀) ?_
        exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn (b + 2))
      have h4 := mul_le_mul_of_nonneg_left h3 hεa_nn
      nlinarith [hεa_nn, hCJ_nn (b + 2), hf₁_nn]
    have hkey : ‖Φp‖ ≤ εa * u + KE1 p * (1 + f₁) := by
      refine le_trans hΦcore ?_
      have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
      rw [hKE1_def]
      have hε2p2 : (0:ℝ) ≤ εa * CJ (2 * p + 2) * (1 + f₁) :=
        mul_nonneg (mul_nonneg hεa_nn (hCJ_nn _)) (by linarith)
      nlinarith [htopC]
    have hgap := hCg (2 * p + 1) T₀
    have hc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc1] at hgap
    have hu_le : u ≤ fT (2 * p + 2) + Cg (2 * p + 1) * f₁ := hgap
    have hBm_le_B : Bm ≤ B := min_le_left _ _
    have hBm_le_Bh : Bm ≤ Bh := min_le_right _ _
    have hBh_le : Bh ≤ CDS0 0 * R₀ := by
      rw [hBh_def]
      refine mul_le_mul_of_nonneg_left ?_ (hCDS0_nn 0)
      exact hfT_ball _ (by omega)
    have hBh_le_f₁ : Bh ≤ CDS0 0 * f₁ := by
      rw [hBh_def, hf₁_def]
      refine mul_le_mul_of_nonneg_left ?_ (hCDS0_nn 0)
      exact hfT_mono (by omega)
    have hfinal : ‖Φp‖ * Bm ≤
        B * εa * fT (2 * p + 2) +
          (CDS0 0 * R₀ * εa * Cg (2 * p + 1) + CDS0 0 * (1 + R₀) * KE1 p) * f₁ := by
      have hexp : ‖Φp‖ * Bm ≤ (εa * u + KE1 p * (1 + f₁)) * Bm :=
        mul_le_mul_of_nonneg_right hkey hBm_nn
      have h1 : εa * u * Bm ≤ εa * (fT (2 * p + 2) + Cg (2 * p + 1) * f₁) * Bm := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu_le hεa_nn) hBm_nn
      have h2 : εa * fT (2 * p + 2) * Bm ≤ εa * fT (2 * p + 2) * B :=
        mul_le_mul_of_nonneg_left hBm_le_B (mul_nonneg hεa_nn (hfT_nn _))
      have h3 : εa * (Cg (2 * p + 1) * f₁) * Bm ≤
          εa * (Cg (2 * p + 1) * f₁) * (CDS0 0 * R₀) :=
        mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le)
          (mul_nonneg hεa_nn (mul_nonneg (hCg_nn _) hf₁_nn))
      have h4 : KE1 p * 1 * Bm ≤ KE1 p * (CDS0 0 * f₁) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le_f₁) (hKE1_nn p)
      have h5 : KE1 p * f₁ * Bm ≤ KE1 p * f₁ * (CDS0 0 * R₀) :=
        mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le)
          (mul_nonneg (hKE1_nn p) hf₁_nn)
      nlinarith [hexp, h1, h2, h3, h4, h5]
    refine le_trans hX ?_
    simp only [hfT_def, hf₁_def] at hfinal
    refine le_trans hfinal ?_
    have hextra : 0 ≤ CCS 0 p * (1 + R₀) * CJ 0 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCCS_nn 0 p) (by linarith)) (hCJ_nn 0))
        (norm_nonneg _)
    nlinarith [hextra]

set_option maxHeartbeats 3200000 in
lemma exists_connLapIterate_appCc_covGrad_sobolevHs_bound_odd (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KT : ℕ → ℝ, (∀ p, 0 ≤ KT p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ), 0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          Real.sqrt (‖operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g₀ 0 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀)‖ ^ 2) ≤
            B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖ +
              KT p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (I := I) (M := M) g₀
  obtain ⟨c22, hc22_nn, hc22⟩ := bal_Ccore (I := I) (M := M) g₀ 2 2
  have hgapfam := fun k : ℕ =>
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ k
  choose Cq hCq_nn hCq using hgapfam
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set KE1 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) + εa * CJ (2 * p + 2)) +
    c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE1_def
  set KE2 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p + 1)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) + εa * CJ (2 * p + 3)) +
    c22 p * ∑ b ∈ Finset.range (2 * p + 1),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE2_def
  have hterm_nn : ∀ b : ℕ, 0 ≤ Real.sqrt (Kc b) *
      (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2) := by
    intro b
    have h1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (b + 2)) => hCJ_nn j)
    have h2 := Real.sqrt_nonneg (Kc b)
    have h3 := hCJ_nn (b + 2)
    nlinarith
  have hKE1_nn : ∀ p, 0 ≤ KE1 p := by
    intro p
    rw [hKE1_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p)) => hterm_nn b)
    have := hterm_nn (2 * p)
    have := hc22_nn p
    nlinarith
  have hKE2_nn : ∀ p, 0 ≤ KE2 p := by
    intro p
    rw [hKE2_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p + 1)) => hterm_nn b)
    have := hterm_nn (2 * p + 1)
    have := hc22_nn p
    nlinarith
  refine ⟨fun p =>
      (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
      (CDS0 0 * R₀ * εa * Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
        CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)),
    fun p => ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
        Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) := by
      have := hCCS_nn 0 p
      have := hCCS_nn 1 p
      have := hCJ_nn 0
      have := hCJ_nn 1
      have := Real.sqrt_nonneg (n : ℝ)
      have ha1 : (0:ℝ) ≤ CCS 0 p * CJ 0 := mul_nonneg (hCCS_nn 0 p) (hCJ_nn 0)
      have ha2 : (0:ℝ) ≤ CCS 1 p * CJ 0 := mul_nonneg (hCCS_nn 1 p) (hCJ_nn 0)
      have ha3 : (0:ℝ) ≤ Real.sqrt n * CCS 0 p * CJ 1 :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCCS_nn 0 p)) (hCJ_nn 1)
      nlinarith
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa *
        Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (Real.sqrt_nonneg _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith))
        (add_nonneg (hKE1_nn p) (hKE2_nn p))
    have h4 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1)) (hCC_nn 0 p))
        (by linarith)
    linarith
  intro C₀ T₀ B hB hball hdata henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    refine le_trans (hfT_mono hk) ?_
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2]
    exact hball
  set Φp : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀
    with hΦp_def
  set Xp : SmoothCcTensor g₀ 0 2 := operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀ with hXp_def
  have hsplit : covGrad (I := I) (M := M) g₀ 0 2 Xp =
      operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp) (covGrad (I := I) (M := M) g₀ 0 2 T₀) :=
    covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ 2 2 Φp T₀
  set f₂ : ℝ := fT (2 * p + 2) with hf₂_def
  have hf₂_nn : 0 ≤ f₂ := hfT_nn _
  have hT0f : ‖T₀‖ ≤ CJ 0 * f₂ := by
    have h := hCJ 0 T₀
    rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
      iteratedCovGrad_zero _ _ _ _] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 0)
  have hGT0f : ‖covGrad (I := I) (M := M) g₀ 0 2 T₀‖ ≤ CJ 1 * f₂ := by
    have h := hCJ 1 T₀
    rw [show iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
      covGrad (I := I) (M := M) g₀ 0 2 T₀ from
        (covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 0 2 T₀).symm] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 1)
  by_cases hcase : w + 2 * p + 2 ≤ a + 2
  · have hsupΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (Φp.toSection x) ≤ (CCS 0 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 0 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have hf_le : fT (0 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 0 p * (1 + fT (0 + w + 2 * p + 1)) ≤ CCS 0 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 0 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (0 + w + 2 * p + 1)
      have := hCCS_nn 0 p
      nlinarith
    have hsupΦ1 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 1) x
        ((covGrad (I := I) (M := M) g₀ 2 2 Φp).toSection x) ≤
        (CCS 1 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 1 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 1 Φp =
        covGrad (I := I) (M := M) g₀ 2 2 Φp from
          (covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 2 2 Φp).symm] at h
      refine le_trans h ?_
      have hf_le : fT (1 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 1 p * (1 + fT (1 + w + 2 * p + 1)) ≤ CCS 1 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 1 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (1 + w + 2 * p + 1)
      have := hCCS_nn 1 p
      nlinarith
    have hsupSE : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) (2 + 1) x
        ((slotExtend (I := I) (M := M) g₀ 2 2 Φp).toSection x) ≤
        (Real.sqrt n * (CCS 0 p * (1 + R₀))) ^ 2 := by
      intro x
      have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 2 Φp 0 x
      rw [show iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 1) 0
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp) =
        slotExtend (I := I) (M := M) g₀ 2 2 Φp from iteratedCovGrad_zero _ _ _ _] at h
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have h2 := hsupΦ0 x
      have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
      have hns : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x (Φp.toSection x)]
    have hXb : ‖Xp‖ ≤ CCS 0 p * (1 + R₀) * (CJ 0 * f₂) := by
      have hn0' : (0:ℝ) ≤ CCS 0 p * (1 + R₀) :=
        mul_nonneg (hCCS_nn 0 p) (by linarith)
      have h := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2 2
        Φp T₀ (CCS 0 p * (1 + R₀)) hn0' hsupΦ0
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hT0f hn0'
    have hGXb : ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
        CCS 1 p * (1 + R₀) * (CJ 0 * f₂) +
          Real.sqrt n * (CCS 0 p * (1 + R₀)) * (CJ 1 * f₂) := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hn1' : (0:ℝ) ≤ CCS 1 p * (1 + R₀) :=
        mul_nonneg (hCCS_nn 1 p) (by linarith)
      have hn2' : (0:ℝ) ≤ Real.sqrt n * (CCS 0 p * (1 + R₀)) :=
        mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hCCS_nn 0 p) (by linarith))
      have h1 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2
        (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ (CCS 1 p * (1 + R₀))
        hn1' hsupΦ1
      have h2 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀
        (2 + 1) (2 + 1) (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) (Real.sqrt n * (CCS 0 p * (1 + R₀)))
        hn2' hsupSE
      have h1' : CCS 1 p * (1 + R₀) * ‖T₀‖ ≤ CCS 1 p * (1 + R₀) * (CJ 0 * f₂) :=
        mul_le_mul_of_nonneg_left hT0f hn1'
      have h2' : Real.sqrt n * (CCS 0 p * (1 + R₀)) *
          ‖covGrad (I := I) (M := M) g₀ 0 2 T₀‖ ≤
          Real.sqrt n * (CCS 0 p * (1 + R₀)) * (CJ 1 * f₂) :=
        mul_le_mul_of_nonneg_left hGT0f hn2'
      linarith [le_trans h1 h1', le_trans h2 h2']
    have hpair : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
        ‖Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ := by
      have h := bal_sqrt_pair_two ‖Xp‖ 0 0 ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖
        (norm_nonneg _) (le_refl 0) (le_refl 0) (norm_nonneg _)
      simpa using h
    refine le_trans hpair ?_
    have hBεa_nn : 0 ≤ B * εa * fT (2 * p + 3) :=
      mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
    have henv_nn : (0:ℝ) ≤ (CDS0 0 * R₀ * εa *
        Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
        CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)) * f₂ := by
      have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa *
          Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (Real.sqrt_nonneg _)
      have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) :=
        mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith))
          (add_nonneg (hKE1_nn p) (hKE2_nn p))
      have h4 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) :=
        mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1)) (hCC_nn 0 p))
          (by linarith)
      exact mul_nonneg (by linarith) hf₂_nn
    simp only [hf₂_def, hfT_def] at hXb hGXb
    nlinarith [hXb, hGXb, hBεa_nn, henv_nn]
  · set Bh : ℝ := CDS0 0 * fT (0 + (n / 2 + 1)) with hBh_def
    have hBh_nn : 0 ≤ Bh := mul_nonneg (hCDS0_nn 0) (hfT_nn _)
    set Bm : ℝ := min B Bh with hBm_def
    have hBm_nn : 0 ≤ Bm := le_min hB hBh_nn
    have hBm_pt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Bm ^ 2 := by
      intro x
      rcases le_total B Bh with h | h
      · rw [hBm_def, min_eq_left h]
        exact hdata x
      · rw [hBm_def, min_eq_right h]
        have hd := hCDS0 T₀ 0 x
        rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
          iteratedCovGrad_zero _ _ _ _] at hd
        exact hd
    have hBm_le_B : Bm ≤ B := min_le_left _ _
    have hBm_le_Bh : Bm ≤ Bh := min_le_right _ _
    have hBh_le : Bh ≤ CDS0 0 * R₀ := by
      rw [hBh_def]
      exact mul_le_mul_of_nonneg_left (hfT_ball _ (by omega)) (hCDS0_nn 0)
    have hBh_le_f₂ : Bh ≤ CDS0 0 * f₂ := by
      rw [hBh_def, hf₂_def]
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCDS0_nn 0)
    set u₂ : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ with hu₂_def
    set u₃ : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 3) T₀‖ with hu₃_def
    have hu₂_nn : 0 ≤ u₂ := norm_nonneg _
    have hu₃_nn : 0 ≤ u₃ := norm_nonneg _
    have hone_aux : ∀ (X : ℝ), 0 ≤ X → 1 + X * f₂ ≤ (1 + X) * (1 + f₂) := by
      intro X hX
      nlinarith
    have henvsum : ∀ (k : ℕ), k ≤ 2 * p + 3 →
        ∑ j ∈ Finset.range k, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (∑ j ∈ Finset.range k, CJ j) * f₂ := by
      intro k hk
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hjk := Finset.mem_range.mp hj
      refine le_trans (hCJ j T₀) ?_
      rw [hf₂_def]
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn j)
    have henvC : ∀ (b : ℕ), b + 2 ≤ 2 * p + 3 → b + 2 ≤ 2 * p + 2 →
        ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
            (1 + f₂) := by
      intro b hb hb2
      refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b) ?_
      have hs := henvsum (b + 2) hb
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (b + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₂) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc b))
      have h3 : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f₂ := by
        refine le_trans (hCJ (b + 2) T₀) ?_
        rw [hf₂_def]
        exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn (b + 2))
      have h4 := mul_le_mul_of_nonneg_left h3 hεa_nn
      nlinarith [hεa_nn, hCJ_nn (b + 2), hf₂_nn]
    have hXb : ‖Xp‖ ≤ Bm * εa * u₂ + Bm * (KE1 p * (1 + f₂)) := by
      have hX : ‖Xp‖ ≤ ‖Φp‖ * Bm :=
        operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀ 2 2
          Φp T₀ Bm hBm_nn hBm_pt
      have hΦcore := (hc22 p C₀).1
      have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
          (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)) *
            (1 + f₂) + εa * u₂ := by
        refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv
          (2 * p)) ?_
        have hs := henvsum (2 * p + 2) (by omega)
        have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 2), CJ j :=
          Finset.sum_nonneg (fun j _ => hCJ_nn j)
        have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
            (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₂) := by
          refine le_trans ?_ (hone_aux _ hCJsum_nn)
          linarith
        have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p)))
        nlinarith [hεa_nn, hu₂_nn]
      have hlowC : ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
          (∑ b ∈ Finset.range (2 * p),
            (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
              εa * CJ (b + 2))) * (1 + f₂) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hb2p := Finset.mem_range.mp hb
        exact henvC b (by omega) (by omega)
      have hkey : ‖Φp‖ ≤ εa * u₂ + KE1 p * (1 + f₂) := by
        refine le_trans hΦcore ?_
        have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
        rw [hKE1_def]
        have hε2p2 : (0:ℝ) ≤ εa * CJ (2 * p + 2) * (1 + f₂) :=
          mul_nonneg (mul_nonneg hεa_nn (hCJ_nn _)) (by linarith)
        nlinarith [htopC]
      calc ‖Xp‖ ≤ ‖Φp‖ * Bm := hX
        _ ≤ (εa * u₂ + KE1 p * (1 + f₂)) * Bm := mul_le_mul_of_nonneg_right hkey hBm_nn
        _ = Bm * εa * u₂ + Bm * (KE1 p * (1 + f₂)) := by ring
    have hGXb : ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
        Bm * εa * u₃ + (Bm * (KE2 p * (1 + f₂)) +
          Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂) := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hp1 : ‖operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖ ≤
          Bm * εa * u₃ + Bm * (KE2 p * (1 + f₂)) := by
        have hX := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀
          2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ Bm hBm_nn hBm_pt
        have hΦcore := (hc22 p C₀).2
        have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p + 1) C₀‖ ≤
            (Real.sqrt (Kc (2 * p + 1)) *
              (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j)) * (1 + f₂) + εa * u₃ := by
          refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv
            (2 * p + 1)) ?_
          have hs := henvsum (2 * p + 3) (by omega)
          have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 3), CJ j :=
            Finset.sum_nonneg (fun j _ => hCJ_nn j)
          have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
              (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) * (1 + f₂) := by
            refine le_trans ?_ (hone_aux _ hCJsum_nn)
            linarith
          have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p + 1)))
          nlinarith [hεa_nn, hu₃_nn]
        have hlowC : ∑ b ∈ Finset.range (2 * p + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
            (∑ b ∈ Finset.range (2 * p + 1),
              (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
                εa * CJ (b + 2))) * (1 + f₂) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun b hb => ?_)
          have hb2p := Finset.mem_range.mp hb
          exact henvC b (by omega) (by omega)
        have hkey : ‖covGrad (I := I) (M := M) g₀ 2 2 Φp‖ ≤
            εa * u₃ + KE2 p * (1 + f₂) := by
          refine le_trans hΦcore ?_
          have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
          rw [hKE2_def]
          have hε2p3 : (0:ℝ) ≤ εa * CJ (2 * p + 3) * (1 + f₂) :=
            mul_nonneg (mul_nonneg hεa_nn (hCJ_nn _)) (by linarith)
          nlinarith [htopC]
        calc ‖operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖
            ≤ ‖covGrad (I := I) (M := M) g₀ 2 2 Φp‖ * Bm := hX
          _ ≤ (εa * u₃ + KE2 p * (1 + f₂)) * Bm :=
              mul_le_mul_of_nonneg_right hkey hBm_nn
          _ = Bm * εa * u₃ + Bm * (KE2 p * (1 + f₂)) := by ring
      have hp2 : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖ ≤
          Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by
        have hdsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((covGrad (I := I) (M := M) g₀ 0 2 T₀).toSection x) ≤
            (CDS0 1 * fT (1 + (n / 2 + 1))) ^ 2 := by
          intro x
          have hd := hCDS0 T₀ 1 x
          rw [show iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
            covGrad (I := I) (M := M) g₀ 0 2 T₀ from
              (covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 0 2 T₀).symm] at hd
          exact hd
        have hX := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀
          (2 + 1) (2 + 1) (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
          (covGrad (I := I) (M := M) g₀ 0 2 T₀) (CDS0 1 * fT (1 + (n / 2 + 1)))
          (mul_nonneg (hCDS0_nn 1) (hfT_nn _)) hdsup
        have hse := bal_slotExt_norm (I := I) (M := M) g₀ 2 2 Φp
        have hΦpl2 : ‖Φp‖ ≤ CC 0 p * (1 + fT (0 + 2 * p + 2)) := by
          have h := hCC C₀ T₀ henv 0 p
          rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
            iteratedCovGrad_zero _ _ _ _] at h
          exact h
        have hprod : fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2)) ≤ (1 + R₀) * f₂ := by
          have hm1 : fT (1 + (n / 2 + 1)) ≤ f₂ := by
            rw [hf₂_def]
            exact hfT_mono (by omega)
          have hm2 : fT (1 + (n / 2 + 1)) * fT (0 + 2 * p + 2) ≤ R₀ * f₂ := by
            have hb1 : fT (1 + (n / 2 + 1)) ≤ R₀ := hfT_ball _ (by omega)
            have hm3 : fT (0 + 2 * p + 2) ≤ f₂ := by
              rw [hf₂_def]
              exact hfT_mono (by omega)
            have := mul_le_mul hb1 hm3 (hfT_nn _) hR₀
            linarith
          nlinarith [hfT_nn (1 + (n / 2 + 1)), hfT_nn (0 + 2 * p + 2)]
        calc ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖
            ≤ ‖slotExtend (I := I) (M := M) g₀ 2 2 Φp‖ *
              (CDS0 1 * fT (1 + (n / 2 + 1))) := hX
          _ ≤ (Real.sqrt n * ‖Φp‖) * (CDS0 1 * fT (1 + (n / 2 + 1))) := by
              refine mul_le_mul_of_nonneg_right hse ?_
              exact mul_nonneg (hCDS0_nn 1) (hfT_nn _)
          _ ≤ (Real.sqrt n * (CC 0 p * (1 + fT (0 + 2 * p + 2)))) *
              (CDS0 1 * fT (1 + (n / 2 + 1))) := by
              refine mul_le_mul_of_nonneg_right ?_
                (mul_nonneg (hCDS0_nn 1) (hfT_nn _))
              exact mul_le_mul_of_nonneg_left hΦpl2 (Real.sqrt_nonneg _)
          _ = Real.sqrt n * CC 0 p * CDS0 1 *
              (fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2))) := by ring
          _ ≤ Real.sqrt n * CC 0 p * CDS0 1 * ((1 + R₀) * f₂) := by
              refine mul_le_mul_of_nonneg_left hprod ?_
              exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCC_nn 0 p)) (hCDS0_nn 1)
          _ = Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by ring
      linarith [hp1, hp2]
    have hgap₂ : u₂ ^ 2 ≤ fT (2 * p + 2) ^ 2 + Cq (2 * p + 1) * fT (2 * p + 1) ^ 2 := by
      have h := hCq (2 * p + 1) T₀
      rw [SmoothCcTensor.norm_toL2] at h
      have hc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
          fT (2 * p + 2) :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hc] at h
      exact h
    have hgap₃ : u₃ ^ 2 ≤ fT (2 * p + 3) ^ 2 + Cq (2 * p + 2) * fT (2 * p + 2) ^ 2 := by
      have h := hCq (2 * p + 2) T₀
      rw [SmoothCcTensor.norm_toL2] at h
      have hc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 2 : ℕ) : ℝ) + 1) T₀‖ =
          fT (2 * p + 3) :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hc] at h
      exact h
    set CqP : ℝ := Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) with hCqP_def
    have hCqP_nn : 0 ≤ CqP := Real.sqrt_nonneg _
    have hupair : Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤ fT (2 * p + 3) + CqP * f₂ := by
      have hsq : CqP ^ 2 = 1 + Cq (2 * p + 1) + Cq (2 * p + 2) :=
        Real.sq_sqrt (by
          have := hCq_nn (2 * p + 1)
          have := hCq_nn (2 * p + 2)
          linarith)
      have hf₁f₂ : fT (2 * p + 1) ≤ f₂ := by
        rw [hf₂_def]
        exact hfT_mono (by omega)
      have hsum : u₂ ^ 2 + u₃ ^ 2 ≤ (fT (2 * p + 3) + CqP * f₂) ^ 2 := by
        have h23 : fT (2 * p + 2) ≤ fT (2 * p + 3) := hfT_mono (by omega)
        have hcross : 0 ≤ 2 * fT (2 * p + 3) * (CqP * f₂) := by
          have := hfT_nn (2 * p + 3)
          have := mul_nonneg hCqP_nn hf₂_nn
          nlinarith
        have hf₁sq : fT (2 * p + 1) ^ 2 ≤ f₂ ^ 2 := by
          nlinarith [hfT_nn (2 * p + 1)]
        have hf₂23 : fT (2 * p + 2) ^ 2 ≤ fT (2 * p + 3) ^ 2 := by
          nlinarith [hfT_nn (2 * p + 2)]
        nlinarith [hgap₂, hgap₃, hCq_nn (2 * p + 1), hCq_nn (2 * p + 2), hf₂_nn,
          hfT_nn (2 * p + 3), hf₁sq, hf₂23, hcross, hsq]
      calc Real.sqrt (u₂ ^ 2 + u₃ ^ 2)
          ≤ Real.sqrt ((fT (2 * p + 3) + CqP * f₂) ^ 2) := Real.sqrt_le_sqrt hsum
        _ = fT (2 * p + 3) + CqP * f₂ := Real.sqrt_sq (by
            have := hfT_nn (2 * p + 3)
            have := mul_nonneg hCqP_nn hf₂_nn
            linarith)
    set s₀ : ℝ := Bm * (KE1 p * (1 + f₂)) with hs₀_def
    set s₁ : ℝ := Bm * (KE2 p * (1 + f₂)) +
      Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ with hs₁_def
    have hs₀_nn : 0 ≤ s₀ := by
      rw [hs₀_def]
      exact mul_nonneg hBm_nn (mul_nonneg (hKE1_nn p) (by linarith))
    have hs₁_nn : 0 ≤ s₁ := by
      rw [hs₁_def]
      have h1 : (0:ℝ) ≤ Bm * (KE2 p * (1 + f₂)) :=
        mul_nonneg hBm_nn (mul_nonneg (hKE2_nn p) (by linarith))
      have h2 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1))
          (hCC_nn 0 p)) (by linarith)) hf₂_nn
      linarith
    have hBεu_nn : ∀ (v : ℝ), 0 ≤ v → 0 ≤ Bm * εa * v := fun v hv =>
      mul_nonneg (mul_nonneg hBm_nn hεa_nn) hv
    have hmono := bal_sqrt_mono_pair (norm_nonneg Xp)
      (norm_nonneg (covGrad (I := I) (M := M) g₀ 0 2 Xp)) hXb hGXb
    have htwo := bal_sqrt_pair_two (Bm * εa * u₂) s₀ (Bm * εa * u₃) s₁
      (hBεu_nn u₂ hu₂_nn) hs₀_nn (hBεu_nn u₃ hu₃_nn) hs₁_nn
    have hfactor : Real.sqrt ((Bm * εa * u₂) ^ 2 + (Bm * εa * u₃) ^ 2) =
        Bm * εa * Real.sqrt (u₂ ^ 2 + u₃ ^ 2) := by
      have h1 : (Bm * εa * u₂) ^ 2 + (Bm * εa * u₃) ^ 2 =
          (Bm * εa) ^ 2 * (u₂ ^ 2 + u₃ ^ 2) := by ring
      rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hBm_nn hεa_nn)]
    have hs01 : Real.sqrt (s₀ ^ 2 + s₁ ^ 2) ≤ s₀ + s₁ := by
      have h := bal_sqrt_pair_two s₀ 0 0 s₁ hs₀_nn (le_refl 0) (le_refl 0) hs₁_nn
      simpa [Real.sqrt_sq hs₀_nn, Real.sqrt_sq hs₁_nn] using h
    have hchain : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
        Bm * εa * fT (2 * p + 3) + Bm * εa * (CqP * f₂) + (s₀ + s₁) := by
      have h1 : Bm * εa * Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
          Bm * εa * (fT (2 * p + 3) + CqP * f₂) :=
        mul_le_mul_of_nonneg_left hupair (mul_nonneg hBm_nn hεa_nn)
      refine le_trans hmono (le_trans htwo ?_)
      rw [hfactor]
      refine le_trans (add_le_add h1 hs01) (le_of_eq ?_)
      ring
    have hsplit1 : Bm * εa * fT (2 * p + 3) ≤ B * εa * fT (2 * p + 3) := by
      have := mul_le_mul_of_nonneg_right hBm_le_B hεa_nn
      exact mul_le_mul_of_nonneg_right this (hfT_nn _)
    have hBm_leC : Bm ≤ CDS0 0 * R₀ := le_trans hBm_le_Bh hBh_le
    have hsplit2 : Bm * εa * (CqP * f₂) ≤ CDS0 0 * R₀ * εa * CqP * f₂ := by
      have h1 : Bm * εa ≤ CDS0 0 * R₀ * εa := mul_le_mul_of_nonneg_right hBm_leC hεa_nn
      have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hCqP_nn hf₂_nn)
      calc Bm * εa * (CqP * f₂) ≤ CDS0 0 * R₀ * εa * (CqP * f₂) := h2
        _ = CDS0 0 * R₀ * εa * CqP * f₂ := by ring
    have hsplits₀ : s₀ ≤ CDS0 0 * (1 + R₀) * KE1 p * f₂ := by
      rw [hs₀_def]
      have h1 : Bm * KE1 p ≤ CDS0 0 * f₂ * KE1 p :=
        mul_le_mul_of_nonneg_right (le_trans hBm_le_Bh hBh_le_f₂) (hKE1_nn p)
      have h2 : Bm * (KE1 p * f₂) ≤ CDS0 0 * R₀ * (KE1 p * f₂) :=
        mul_le_mul_of_nonneg_right hBm_leC (mul_nonneg (hKE1_nn p) hf₂_nn)
      linarith [h1, h2]
    have hsplits₁ : s₁ ≤ CDS0 0 * (1 + R₀) * KE2 p * f₂ +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by
      rw [hs₁_def]
      have h1 : Bm * KE2 p ≤ CDS0 0 * f₂ * KE2 p :=
        mul_le_mul_of_nonneg_right (le_trans hBm_le_Bh hBh_le_f₂) (hKE2_nn p)
      have h2 : Bm * (KE2 p * f₂) ≤ CDS0 0 * R₀ * (KE2 p * f₂) :=
        mul_le_mul_of_nonneg_right hBm_leC (mul_nonneg (hKE2_nn p) hf₂_nn)
      linarith [h1, h2]
    have hcrude_nn : (0:ℝ) ≤ (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
        Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) * f₂ := by
      have ha1 : (0:ℝ) ≤ CCS 0 p * CJ 0 := mul_nonneg (hCCS_nn 0 p) (hCJ_nn 0)
      have ha2 : (0:ℝ) ≤ CCS 1 p * CJ 0 := mul_nonneg (hCCS_nn 1 p) (hCJ_nn 0)
      have ha3 : (0:ℝ) ≤ Real.sqrt n * CCS 0 p * CJ 1 :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCCS_nn 0 p)) (hCJ_nn 1)
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hf₂_nn
    have hfinal : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
        B * εa * fT (2 * p + 3) +
          ((CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
            (CDS0 0 * R₀ * εa * CqP + CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
              Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀))) * f₂ := by
      have hring : ((CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
          Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
            (CDS0 0 * R₀ * εa * CqP + CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
              Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀))) * f₂ =
          (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
            Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) * f₂ +
          (CDS0 0 * R₀ * εa * CqP * f₂ +
            (CDS0 0 * (1 + R₀) * KE1 p * f₂ + CDS0 0 * (1 + R₀) * KE2 p * f₂) +
            Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂) := by ring
      rw [hring]
      linarith [hchain, hsplit1, hsplit2, hsplits₀, hsplits₁, hcrude_nn]
    rw [hf₂_def, hCqP_def] at hfinal
    simp only [hfT_def] at hfinal
    exact hfinal

set_option maxHeartbeats 1600000 in
lemma exists_deTurckRemainder_connLapIterate_sobolevHs_bound (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KZ : ℕ → ℕ → ℝ, (∀ q m, 0 ≤ KZ q m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q m : ℕ),
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                        (covGrad (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                        (slotExtend (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            KZ q m * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * m + 2 * q + 3 : ℕ) : ℝ) T₀‖ ∧
          ‖covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                        (covGrad (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                        (slotExtend (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))))‖ ≤
            KZ q m * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * m + 2 * q + 4 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CB1, hCB1_nn, hCB1⟩ := bal_block1 (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨CB23, hCB23_nn, hCB23⟩ := bal_block23 (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨c02, hc02_nn, hc02⟩ := bal_Ccore (I := I) (M := M) g₀ 0 2
  set CBtot : ℕ → ℕ → ℝ := fun q j => CB1 q j + 2 * CB23 q j with hCBtot_def
  have hCBtot_nn : ∀ q j, 0 ≤ CBtot q j := fun q j => by
    have := hCB1_nn q j
    have := hCB23_nn q j
    rw [hCBtot_def]
    dsimp only
    linarith
  refine ⟨fun q m => (CBtot q (2 * m) + c02 m * ∑ b ∈ Finset.range (2 * m), CBtot q b) +
      (CBtot q (2 * m + 1) + c02 m * ∑ b ∈ Finset.range (2 * m + 1), CBtot q b),
    fun q m => ?_, ?_⟩
  · have h1 := hCBtot_nn q (2 * m)
    have h2 := hCBtot_nn q (2 * m + 1)
    have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m), CBtot q b :=
      Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
    have h4 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m + 1), CBtot q b :=
      Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
    have := hc02_nn m
    have := mul_nonneg (hc02_nn m) h3
    have := mul_nonneg (hc02_nn m) h4
    linarith
  intro C₀ T₀ hball henv q m
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  set Eq : SmoothCcTensor g₀ 0 2 :=
    -(operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀)) with hEq_def
  have hjets : ∀ j : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 j Eq‖ ≤
      CBtot q j * fT (j + 2 * q + 3) := by
    intro j
    have hsplit : iteratedCovGrad (I := I) g₀ 0 2 j Eq =
        -(iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
          - iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                  (covGrad (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                (covGrad (I := I) (M := M) g₀ 0 2 T₀)))
          - iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                  (slotExtend (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))) := by
      rw [hEq_def, iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_neg]
    rw [hsplit]
    have h1 := hCB1 C₀ T₀ hball henv q j
    have h23 := hCB23 C₀ T₀ hball henv q j
    have hn1 := norm_sub_le
      (-(iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
        - iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                (covGrad (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
      (iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
    have hn2 := norm_sub_le
      (-(iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))))
      (iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
    rw [norm_neg] at hn2
    have hfold : CBtot q j * fT (j + 2 * q + 3) =
        CB1 q j * fT (j + 2 * q + 3) + CB23 q j * fT (j + 2 * q + 3) +
          CB23 q j * fT (j + 2 * q + 3) := by
      rw [hCBtot_def]
      dsimp only
      ring
    rw [hfold]
    have hfeq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ =
        fT (j + 2 * q + 3) := rfl
    rw [hfeq] at h1 h23
    linarith [h1, h23.1, h23.2, hn1, hn2]
  have hcore := hc02 m Eq
  constructor
  · refine le_trans hcore.1 ?_
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * m) Eq‖ ≤
        CBtot q (2 * m) * fT (2 * m + 2 * q + 3) := hjets (2 * m)
    have hlow : ∑ b ∈ Finset.range (2 * m), ‖iteratedCovGrad (I := I) g₀ 0 2 b Eq‖ ≤
        (∑ b ∈ Finset.range (2 * m), CBtot q b) * fT (2 * m + 2 * q + 3) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hbm := Finset.mem_range.mp hb
      refine le_trans (hjets b) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q b)
    have h2 := mul_le_mul_of_nonneg_left hlow (hc02_nn m)
    have hnn : 0 ≤ (CBtot q (2 * m + 1) + c02 m * ∑ b ∈ Finset.range (2 * m + 1),
        CBtot q b) * fT (2 * m + 2 * q + 3) := by
      have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m + 1), CBtot q b :=
        Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
      exact mul_nonneg (by
        have := hCBtot_nn q (2 * m + 1)
        have := mul_nonneg (hc02_nn m) h3
        linarith) (hfT_nn _)
    have hgoalf : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * m + 2 * q + 3 : ℕ) : ℝ) T₀‖ = fT (2 * m + 2 * q + 3) := rfl
    rw [hgoalf]
    nlinarith [htop, h2]
  · refine le_trans hcore.2 ?_
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * m + 1) Eq‖ ≤
        CBtot q (2 * m + 1) * fT (2 * m + 2 * q + 4) := by
      refine le_trans (hjets (2 * m + 1)) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q (2 * m + 1))
    have hlow : ∑ b ∈ Finset.range (2 * m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 b Eq‖ ≤
        (∑ b ∈ Finset.range (2 * m + 1), CBtot q b) * fT (2 * m + 2 * q + 4) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hbm := Finset.mem_range.mp hb
      refine le_trans (hjets b) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q b)
    have h2 := mul_le_mul_of_nonneg_left hlow (hc02_nn m)
    have hnn : 0 ≤ (CBtot q (2 * m) + c02 m * ∑ b ∈ Finset.range (2 * m),
        CBtot q b) * fT (2 * m + 2 * q + 4) := by
      have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m), CBtot q b :=
        Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
      exact mul_nonneg (by
        have := hCBtot_nn q (2 * m)
        have := mul_nonneg (hc02_nn m) h3
        linarith) (hfT_nn _)
    have hgoalf : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * m + 2 * q + 4 : ℕ) : ℝ) T₀‖ = fT (2 * m + 2 * q + 4) := rfl
    rw [hgoalf]
    nlinarith [htop, h2]
end BalLadder

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
