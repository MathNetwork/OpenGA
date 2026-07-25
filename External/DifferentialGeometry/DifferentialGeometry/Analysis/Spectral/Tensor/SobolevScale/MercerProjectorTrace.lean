import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Analysis.Integration.Measure.Properties


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace Mercer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def mercerHalfOrder : ℕ := Module.finrank ℝ E / 2 + 1

def mercerSobolevExp : ℕ := 2 * (2 * (Module.finrank ℝ E / 2 + 1))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mercerSobolevExp_gt_finrank :
    Module.finrank ℝ E < mercerSobolevExp (E := E) := by
  unfold mercerSobolevExp; omega

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma two_mul_mercerHalfOrder_gt_finrank :
    2 * mercerHalfOrder (E := E) > Module.finrank ℝ E := by
  unfold mercerHalfOrder; omega

def eigenSubLevel (g : SmoothRiemannianMetric I M) (Λ : ℝ) :
    Finset (TensorEigenIdx (I := I) (M := M) g 0 2) :=
  (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g 0 2 Λ).toFinset

omit [BoundarylessManifold I M] in
lemma mem_eigenSubLevel (g : SmoothRiemannianMetric I M) (Λ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    i ∈ eigenSubLevel (I := I) (M := M) g Λ ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
  unfold eigenSubLevel
  rw [Set.Finite.mem_toFinset]
  rfl

omit [BoundarylessManifold I M] in
private lemma finiteEigenCombo_toSection_apply (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (x : M) :
    (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
        (I := I) (M := M) g F c).toSection x =
      ∑ i ∈ F, c i • (eigenSmooth (I := I) (M := M) g i).toSection x := by
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo_eq,
    SmoothCcTensor.toSection_sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [DifferentialGeometry.PDE.RicciFlow.smoothCcTensor_toSection_smul_apply]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

private lemma eigenProjector_frame_component_sq_le (g : SmoothRiemannianMetric I M)
    {C : ℝ} (hC_nn : 0 ≤ C) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hC : ∀ (x : M)
        (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
        letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
        ‖(DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
            (I := I) (M := M) g (eigenSubLevel (I := I) (M := M) g Λ) c).toSection x‖ ≤
          C * (1 + Λ) ^ (2 * mercerHalfOrder (E := E)) *
            ‖((DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
              (I := I) (M := M) g (eigenSubLevel (I := I) (M := M) g Λ) c) :
              TensorL2 0 2 g)‖)
    (x : M)
    (v : TensorRSSpace 0 2 I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
    ∑ i ∈ eigenSubLevel (I := I) (M := M) g Λ,
        (inner ℝ ((eigenSmooth (I := I) (M := M) g i).toSection x) v) ^ 2 ≤
      (C * (1 + Λ) ^ (2 * mercerHalfOrder (E := E))) ^ 2 * ‖v‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  classical
  set S := eigenSubLevel (I := I) (M := M) g Λ with hS
  set c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => inner ℝ ((eigenSmooth (I := I) (M := M) g i).toSection x) v with hc
  set K := DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
    (I := I) (M := M) g S c with hK
  set D : ℝ := C * (1 + Λ) ^ (2 * mercerHalfOrder (E := E)) with hD
  have h1Λ_nn : (0 : ℝ) ≤ 1 + Λ := by linarith
  have hD_nn : 0 ≤ D := by
    have : (0 : ℝ) ≤ (1 + Λ) ^ (2 * mercerHalfOrder (E := E)) := pow_nonneg h1Λ_nn _
    exact mul_nonneg hC_nn this

  have hL2 : ‖(K : TensorL2 0 2 g)‖ ^ 2 = ∑ i ∈ S, (c i) ^ 2 :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo_l2NormSq
      (I := I) (M := M) g S c

  have hrepro : inner ℝ (K.toSection x) v = ∑ i ∈ S, (c i) ^ 2 := by
    rw [hK, finiteEigenCombo_toSection_apply (I := I) (M := M) g S c x, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left, hc, sq]

  have hCS : (∑ i ∈ S, (c i) ^ 2) ≤ ‖K.toSection x‖ * ‖v‖ := by
    rw [← hrepro]
    exact real_inner_le_norm _ _

  have hKx : ‖K.toSection x‖ ≤ D * ‖(K : TensorL2 0 2 g)‖ := hC x c
  set N : ℝ := ‖(K : TensorL2 0 2 g)‖ with hN
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hsum_nn : 0 ≤ ∑ i ∈ S, (c i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)

  have hNsq : N ^ 2 ≤ D * N * ‖v‖ := by
    rw [hN, hL2]
    calc ∑ i ∈ S, (c i) ^ 2 ≤ ‖K.toSection x‖ * ‖v‖ := hCS
      _ ≤ (D * N) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hKx (norm_nonneg _)
  have hN_le : N ≤ D * ‖v‖ := by
    rcases eq_or_lt_of_le hN_nn with hN0 | hN0
    · rw [← hN0]; exact mul_nonneg hD_nn (norm_nonneg _)
    · have h2 : N * N ≤ (D * ‖v‖) * N := by nlinarith [hNsq]
      exact le_of_mul_le_mul_right (by linarith [h2]) hN0

  calc ∑ i ∈ S, (c i) ^ 2 = N ^ 2 := by rw [hN, hL2]
    _ ≤ (D * ‖v‖) ^ 2 := by
        have hub : 0 ≤ D * ‖v‖ := mul_nonneg hD_nn (norm_nonneg _)
        nlinarith [hN_le, hN_nn]
    _ = D ^ 2 * ‖v‖ ^ 2 := by rw [mul_pow]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem eigenProjector_diagonal_le (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (x : M),
      ∑ i ∈ eigenSubLevel (I := I) (M := M) g Λ,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            ((eigenSmooth (I := I) (M := M) g i).toSection x) ≤
        C * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI instRB : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  set k₂ : ℕ := mercerHalfOrder (E := E) with hk₂
  have hsuper : 2 * k₂ > Module.finrank ℝ E := two_mul_mercerHalfOrder_gt_finrank (E := E)

  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck
      (I := I) (M := M) (g := g) (r := 0) (s := 2) (k := k₂) (m := 0) (by omega)

  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.eigenSpan_pouHs_le_spectral
      (I := I) (M := M) g (2 * k₂)
  set Cgard : ℝ := C₂ * (C₁ * (↑(2 * k₂) + 1)) with hCgard
  have hCgard_nn : 0 ≤ Cgard := by
    have : (0 : ℝ) ≤ C₁ * (↑(2 * k₂) + 1) := by positivity
    exact mul_nonneg (le_of_lt hC₂_pos) this

  have hCpt : ∀ (Λ : ℝ) (_hΛ : 0 ≤ Λ) (x : M)
      (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖(DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
          (I := I) (M := M) g (eigenSubLevel (I := I) (M := M) g Λ) c).toSection x‖ ≤
        Cgard * (1 + Λ) ^ (2 * k₂) *
          ‖((DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
            (I := I) (M := M) g (eigenSubLevel (I := I) (M := M) g Λ) c) :
            TensorL2 0 2 g)‖ := by
    intro Λ hΛ x c
    have h1Λ_nn : (0 : ℝ) ≤ 1 + Λ := by linarith
    set S := eigenSubLevel (I := I) (M := M) g Λ with hS
    set K := DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo
      (I := I) (M := M) g S c with hK

    have h1 : ‖K.toSection x‖ ≤
        C₂ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k₂) K‖ := hC₂ K x

    have h2 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k₂) K‖ =
        (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k₂) K).toReal :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq
        (I := I) (M := M) g (2 * k₂) K

    have h3 : (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k₂) K).toReal ≤
        (C₁ * (↑(2 * k₂) + 1)) *
          ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenComboHs
            (I := I) (M := M) g S c ((2 * (2 * k₂) : ℕ) : ℝ)‖ := hC₁ S c

    have h4 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenComboHs
          (I := I) (M := M) g S c ((2 * (2 * k₂) : ℕ) : ℝ)‖ ≤
        (1 + Λ) ^ (2 * k₂) * ‖(K : TensorL2 0 2 g)‖ := by
      have hspec :=
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenComboHs_norm_eq_sqrt_spectral
          (I := I) (M := M) g S c (2 * k₂)
      rw [hspec]
      have hL2 : ‖(K : TensorL2 0 2 g)‖ ^ 2 = ∑ i ∈ S, (c i) ^ 2 :=
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenCombo_l2NormSq
          (I := I) (M := M) g S c

      have hsum_le : ∑ i ∈ S,
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * (2 * k₂) : ℕ) : ℝ) *
            (c i) ^ 2 ≤
          (1 + Λ) ^ (2 * (2 * k₂)) * ∑ i ∈ S, (c i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hlt : 1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
          rw [hS, mem_eigenSubLevel (I := I) (M := M) g Λ i] at hi
          exact hi
        have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
            (I := I) (M := M) i
        have hbase_nn : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by linarith
        have hbase_le : 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ 1 + Λ := by linarith
        have hrpow_eq : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
              ((2 * (2 * k₂) : ℕ) : ℝ) =
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (2 * k₂)) := by
          rw [Real.rpow_natCast]
        rw [hrpow_eq]
        have hpow_le : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (2 * k₂)) ≤
            (1 + Λ) ^ (2 * (2 * k₂)) :=
          pow_le_pow_left₀ hbase_nn hbase_le (2 * (2 * k₂))
        exact mul_le_mul_of_nonneg_right hpow_le (sq_nonneg (c i))
      calc Real.sqrt
            (∑ i ∈ S, (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                ((2 * (2 * k₂) : ℕ) : ℝ) * (c i) ^ 2)
          ≤ Real.sqrt ((1 + Λ) ^ (2 * (2 * k₂)) * ∑ i ∈ S, (c i) ^ 2) :=
            Real.sqrt_le_sqrt hsum_le
        _ = (1 + Λ) ^ (2 * k₂) * ‖(K : TensorL2 0 2 g)‖ := by
            rw [← hL2]
            rw [show (2 * (2 * k₂)) = (2 * k₂) * 2 by ring, pow_mul]
            rw [show ((1 + Λ) ^ (2 * k₂)) ^ 2 * ‖(K : TensorL2 0 2 g)‖ ^ 2 =
                ((1 + Λ) ^ (2 * k₂) * ‖(K : TensorL2 0 2 g)‖) ^ 2 by ring]
            rw [Real.sqrt_sq (mul_nonneg (pow_nonneg h1Λ_nn _) (norm_nonneg _))]

    have hKL2_nn : 0 ≤ ‖(K : TensorL2 0 2 g)‖ := norm_nonneg _
    have hpowΛ_nn : 0 ≤ (1 + Λ) ^ (2 * k₂) := pow_nonneg h1Λ_nn _
    calc ‖K.toSection x‖
        ≤ C₂ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k₂) K‖ := h1
      _ = C₂ * (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k₂) K).toReal := by rw [h2]
      _ ≤ C₂ * ((C₁ * (↑(2 * k₂) + 1)) *
            ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.finiteEigenComboHs
              (I := I) (M := M) g S c ((2 * (2 * k₂) : ℕ) : ℝ)‖) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hC₂_pos)
      _ ≤ C₂ * ((C₁ * (↑(2 * k₂) + 1)) * ((1 + Λ) ^ (2 * k₂) * ‖(K : TensorL2 0 2 g)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₂_pos)
          refine mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = Cgard * (1 + Λ) ^ (2 * k₂) * ‖(K : TensorL2 0 2 g)‖ := by rw [hCgard]; ring

  set n2 : ℕ := (Module.finrank ℝ E) ^ (0 + 2) with hn2
  refine ⟨(n2 : ℝ) * Cgard ^ 2 + 1, by positivity, fun Λ x => ?_⟩

  rcases lt_or_ge Λ 0 with hΛneg | hΛ
  · have hempty : eigenSubLevel (I := I) (M := M) g Λ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [mem_eigenSubLevel (I := I) (M := M) g Λ i] at hi
      have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
          (I := I) (M := M) i
      linarith
    rw [hempty, Finset.sum_empty]
    rw [Real.rpow_natCast, mercerSobolevExp, pow_mul]
    positivity

  set b := stdOrthonormalBasis ℝ (TensorRSSpace 0 2 I x) with hb

  have hparseval : ∀ i,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((eigenSmooth (I := I) (M := M) g i).toSection x) =
        ∑ a, (inner ℝ ((eigenSmooth (I := I) (M := M) g i).toSection x) (b a)) ^ 2 := by
    intro i
    rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g 0 2 x _]
    exact (OrthonormalBasis.sum_sq_inner_left b
      ((eigenSmooth (I := I) (M := M) g i).toSection x)).symm

  calc ∑ i ∈ eigenSubLevel (I := I) (M := M) g Λ,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            ((eigenSmooth (I := I) (M := M) g i).toSection x)
      = ∑ i ∈ eigenSubLevel (I := I) (M := M) g Λ,
          ∑ a, (inner ℝ ((eigenSmooth (I := I) (M := M) g i).toSection x) (b a)) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => hparseval i)
    _ = ∑ a, ∑ i ∈ eigenSubLevel (I := I) (M := M) g Λ,
          (inner ℝ ((eigenSmooth (I := I) (M := M) g i).toSection x) (b a)) ^ 2 :=
        Finset.sum_comm
    _ ≤ ∑ _a : Fin (Module.finrank ℝ (TensorRSSpace 0 2 I x)),
          (Cgard * (1 + Λ) ^ (2 * k₂)) ^ 2 * ‖b _a‖ ^ 2 := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        exact eigenProjector_frame_component_sq_le (I := I) (M := M) g hCgard_nn Λ hΛ
          (hCpt Λ hΛ) x (b a)
    _ = ∑ _a : Fin (Module.finrank ℝ (TensorRSSpace 0 2 I x)),
          (Cgard * (1 + Λ) ^ (2 * k₂)) ^ 2 := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [b.orthonormal.1 a, one_pow, mul_one]
    _ = (n2 : ℝ) * (Cgard * (1 + Λ) ^ (2 * k₂)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          hn2, Tensor0SBundle.finrank_tensorRSSpace]
    _ ≤ ((n2 : ℝ) * Cgard ^ 2 + 1) * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by
        have hexp : ((mercerSobolevExp (E := E) : ℕ) : ℝ) = ((2 * (2 * k₂) : ℕ) : ℝ) := by
          rw [hk₂]; norm_cast
        rw [hexp, Real.rpow_natCast]
        rw [show (Cgard * (1 + Λ) ^ (2 * k₂)) ^ 2 = Cgard ^ 2 * (1 + Λ) ^ (2 * (2 * k₂)) by
          rw [mul_pow, ← pow_mul, mul_comm (2 * k₂) 2]]
        rw [show (n2 : ℝ) * (Cgard ^ 2 * (1 + Λ) ^ (2 * (2 * k₂))) =
          ((n2 : ℝ) * Cgard ^ 2) * (1 + Λ) ^ (2 * (2 * k₂)) by ring]
        have hpow_nn : (0 : ℝ) ≤ (1 + Λ) ^ (2 * (2 * k₂)) := pow_nonneg (by linarith) _
        nlinarith [hpow_nn]

omit [BoundarylessManifold I M] in
private theorem eigenSmooth_toL2_norm_eq_one (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖(eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g)‖ = 1 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set b := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (hCompact (I := I) (M := M) g) with hb_def
  have hbi : (eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g) = b i := by
    rw [hb_def, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply
      (I := I) (M := M) (hCompact (I := I) (M := M) g) i]
    exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2
        (I := I) (M := M) g 0 2 i
  rw [hbi]
  exact b.orthonormal.norm_eq_one i

omit [BoundarylessManifold I M] in
private theorem integral_riemannianFiberNormSq_eigenSmooth_eq_one
    (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((eigenSmooth (I := I) (M := M) g i).toSection x)
      ∂riemannianVolumeMeasure I M g = 1 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hkey := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g 2 (eigenSmooth (I := I) (M := M) g i)
  have hnorm : tensorL2Norm (I := I) (M := M) g 0 2
      (eigenSmooth (I := I) (M := M) g i).toFun =
      ‖eigenSmooth (I := I) (M := M) g i‖ :=
    DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
      (I := I) (M := M) g (eigenSmooth (I := I) (M := M) g i)
  have hnorm_l2 : ‖eigenSmooth (I := I) (M := M) g i‖ =
      ‖(eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g)‖ := by
    rw [← SmoothCcTensor.toL2_apply, SmoothCcTensor.norm_toL2]
  rw [← hkey, hnorm, hnorm_l2, eigenSmooth_toL2_norm_eq_one (I := I) (M := M) g i,
    one_pow]

theorem eigenProjector_card_le_mercer (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 < K ∧ ∀ Λ : ℝ,
      (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ) ≤
        K * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨C, hC, hdiag⟩ := eigenProjector_diagonal_le (I := I) (M := M) g
  set vol : ℝ := ((riemannianVolumeMeasure I M g) Set.univ).toReal with hvol_def
  have hvol_nonneg : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨C * vol + 1, by positivity, fun Λ => ?_⟩
  set F := eigenSubLevel (I := I) (M := M) g Λ with hF_def

  have hcard : (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ) = (F.card : ℝ) := by
    have hset : {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} = (F : Set _) := by
      ext i
      rw [Set.mem_setOf_eq, Finset.mem_coe,
        mem_eigenSubLevel (I := I) (M := M) g Λ i]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard]

  have hcard_sum : (F.card : ℝ) =
      ∫ x, (∑ i ∈ F, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((eigenSmooth (I := I) (M := M) g i).toSection x))
        ∂riemannianVolumeMeasure I M g := by
    rw [integral_finset_sum F
      (fun i _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 2
        (eigenSmooth (I := I) (M := M) g i))]
    rw [Finset.sum_congr rfl
      (fun i _ => integral_riemannianFiberNormSq_eigenSmooth_eq_one (I := I) (M := M) g i)]
    simp
  rw [hcard_sum]

  have hint_le : ∫ x, (∑ i ∈ F, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((eigenSmooth (I := I) (M := M) g i).toSection x))
        ∂riemannianVolumeMeasure I M g ≤
      ∫ _x, (C * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ))
        ∂riemannianVolumeMeasure I M g := by
    refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact Finset.sum_nonneg (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)
    · exact Filter.Eventually.of_forall (fun x => hdiag Λ x)
  refine le_trans hint_le ?_
  rw [integral_const, smul_eq_mul]
  have : (riemannianVolumeMeasure I M g).real Set.univ = vol := by
    rw [hvol_def, MeasureTheory.measureReal_def]
  rw [this]
  have hpow_nonneg : (0 : ℝ) ≤ (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, mercerSobolevExp, pow_mul]; positivity
  have hbase : vol * (C * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ)) =
      (C * vol) * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by ring
  rw [hbase]
  nlinarith [hpow_nonneg]

end Mercer
end Spectral
end Analysis
end DifferentialGeometry

end
