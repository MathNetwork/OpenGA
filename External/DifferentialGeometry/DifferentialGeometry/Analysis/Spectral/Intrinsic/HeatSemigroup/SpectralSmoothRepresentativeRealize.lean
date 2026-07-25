import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenComboGardingReduction
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M)


theorem eigenSpan_pouHs_le_spectral (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2))
        (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 → ℝ),
        (tensorPouSobolevHsNorm (I := I) (M := M) g k
            (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
          (C * (k + 1)) *
            ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    DifferentialGeometry.Integral.Connection.exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
      (I := I) (M := M) g 2 k
  refine ⟨C, hC_nn, fun F c => ?_⟩
  exact eigenSpan_pouHs_le_spectral_of_elliptic (I := I) (M := M) g F c k hC_nn
    (hC (finiteEigenCombo (I := I) (M := M) g F c))

omit [BoundarylessManifold I M] in
theorem finiteEigenComboHs_tensorHsToL2_eq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ
        (finiteEigenComboHs (I := I) (M := M) g F c σ) =
      (finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) with hb_def
  apply b.repr.injective
  ext i
  have hlhs : (b.repr (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ
        (finiteEigenComboHs (I := I) (M := M) g F c σ))) i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ
          (finiteEigenComboHs (I := I) (M := M) g F c σ)) i := rfl
  have hrhs : (b.repr ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g))) i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)) i := rfl
  rw [hlhs, hrhs,
    tensorHsToL2_tensorL2Coeff (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ]
  exact finiteEigenComboHs_coeff_eq (I := I) (M := M) g F c σ i

def eigenIdxFinset (n : ℕ) :
    Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
  (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g 0 2 ((n : ℝ) + 1)).toFinset

omit [BoundarylessManifold I M] in

lemma mem_eigenIdxFinset (n : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    i ∈ eigenIdxFinset (I := I) (M := M) g n ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < (n : ℝ) + 1 := by
  unfold eigenIdxFinset
  rw [Set.Finite.mem_toFinset]
  rfl

omit [BoundarylessManifold I M] in

lemma eigenIdxFinset_mono : Monotone (eigenIdxFinset (I := I) (M := M) g) := by
  intro m n hmn i hi
  rw [mem_eigenIdxFinset] at hi ⊢
  have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  linarith

omit [BoundarylessManifold I M] in

lemma exists_mem_eigenIdxFinset
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    ∃ n : ℕ, i ∈ eigenIdxFinset (I := I) (M := M) g n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 + TensorEigenIdx.lambda (I := I) (M := M) i)
  refine ⟨n, ?_⟩
  rw [mem_eigenIdxFinset]
  linarith

omit [BoundarylessManifold I M] in

lemma tendsto_eigenIdxFinset_atTop :
    Tendsto (eigenIdxFinset (I := I) (M := M) g) atTop atTop :=
  tendsto_atTop_finset_of_monotone (eigenIdxFinset_mono (I := I) (M := M) g)
    (exists_mem_eigenIdxFinset (I := I) (M := M) g)

def spectralPartialSum (u : TensorL2 0 2 g) (n : ℕ) : SmoothCcTensor g 0 2 :=
  finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n)
    (fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i)

omit [BoundarylessManifold I M] in
theorem spectralPartialSum_toL2_tendsto (u : TensorL2 0 2 g) :
    Tendsto (fun n => (spectralPartialSum (I := I) (M := M) g u n : TensorL2 0 2 g))
      atTop (𝓝 u) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) with hb_def
  have hsum : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
  have hpartial : Tendsto
      (fun s : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) =>
        ∑ i ∈ s, b.repr u i • b i) atTop (𝓝 u) := hsum
  have hcomp := hpartial.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
  refine hcomp.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [spectralPartialSum, finiteEigenCombo_toL2 (I := I) (M := M) g]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) i, ← hb_def]
  rfl

private def weightedPartial (u : TensorL2 0 2 g) (k n : ℕ) : ℝ :=
  ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2

omit [BoundarylessManifold I M] in

private lemma weightedPartial_term_nonneg (u : TensorL2 0 2 g) (k : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2 := by
  have hbase : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i
    linarith
  have hw : 0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) :=
    Real.rpow_nonneg hbase _
  positivity

open scoped Classical in

omit [BoundarylessManifold I M] in
private lemma toHs_spectralPartialSum_sub (u : TensorL2 0 2 g) (k : ℕ) {m n : ℕ}
    (hmn : n ≤ m) :
    SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u m) -
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u n) =
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (finiteEigenCombo (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n)
          (fun i => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i)) := by
  classical
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i with hc
  have hsub : finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c -
        finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c =
      finiteEigenCombo (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n) c := by
    rw [finiteEigenCombo_eq, finiteEigenCombo_eq, finiteEigenCombo_eq]
    rw [Finset.sum_sdiff_eq_sub (eigenIdxFinset_mono (I := I) (M := M) g hmn)]
  rw [show SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u m) -
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u n) =
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c -
          finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c) from ?_]
  · rw [hsub]
  · rw [SmoothCcTensor.toHs, SmoothCcTensor.toHs, SmoothCcTensor.toHs]
    rw [show (⟨finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c -
            finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c⟩ :
          SmoothCcTensorHs g 0 2 k) =
        (⟨finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c⟩ :
            SmoothCcTensorHs g 0 2 k) -
          (⟨finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c⟩ :
            SmoothCcTensorHs g 0 2 k) from
      SmoothCcTensorHs.ext (by rw [SmoothCcTensorHs.toCcTensor_sub])]
    rw [UniformSpace.Completion.coe_sub]
    rfl

omit [BoundarylessManifold I M] in

private lemma weightedPartial_le_tsum (u : TensorL2 0 2 g) (k n : ℕ)
    (v : tensorHs (I := I) (M := M) g 0 2 ((2 * k : ℕ) : ℝ))
    (hv : ∀ i, v.coeff i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) :
    weightedPartial (I := I) (M := M) g u k n ≤ ‖v‖ ^ 2 := by
  classical
  rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) v]
  unfold weightedPartial
  have hterm : ∀ i,
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) * (v.coeff i) ^ 2 := by
    intro i
    rw [hv i, tensorSobolevWeight]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  refine Summable.sum_le_tsum _ (fun i _ => ?_) v.weighted_summable
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i ((2 * k : ℕ) : ℝ)
  positivity

omit [BoundarylessManifold I M] in

private lemma weightedPartial_cauchySeq (u : TensorL2 0 2 g) (k : ℕ)
    (v : tensorHs (I := I) (M := M) g 0 2 ((2 * k : ℕ) : ℝ))
    (hv : ∀ i, v.coeff i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) :
    CauchySeq (fun n => weightedPartial (I := I) (M := M) g u k n) := by
  classical
  have hmono : Monotone (fun n => weightedPartial (I := I) (M := M) g u k n) := by
    intro m n hmn
    unfold weightedPartial
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (eigenIdxFinset_mono (I := I) (M := M) g hmn)
      (fun i _ _ => weightedPartial_term_nonneg (I := I) (M := M) g u k i)
  have hbdd : BddAbove (Set.range (fun n => weightedPartial (I := I) (M := M) g u k n)) := by
    refine ⟨‖v‖ ^ 2, ?_⟩
    rintro x ⟨n, rfl⟩
    exact weightedPartial_le_tsum (I := I) (M := M) g u k n v hv
  exact (tendsto_atTop_ciSup hmono hbdd).cauchySeq

open scoped Classical in

omit [BoundarylessManifold I M] in
private lemma finiteEigenComboHs_sdiff_normSq (u : TensorL2 0 2 g) (k : ℕ) {m n : ℕ}
    (hmn : n ≤ m) :
    ‖finiteEigenComboHs (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n)
        (fun i => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i)
        ((2 * k : ℕ) : ℝ)‖ ^ 2 =
      weightedPartial (I := I) (M := M) g u k m -
        weightedPartial (I := I) (M := M) g u k n := by
  classical
  rw [finiteEigenCombo_spectral_normSq (I := I) (M := M) g]
  unfold weightedPartial
  rw [Finset.sum_sdiff_eq_sub (eigenIdxFinset_mono (I := I) (M := M) g hmn)]

open scoped Classical in

omit [BoundarylessManifold I M] in
private lemma dist_toHs_spectralPartialSum_le (u : TensorL2 0 2 g) (k : ℕ)
    {C : ℝ} (hC :
      ∀ (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
        (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
        (tensorPouSobolevHsNorm (I := I) (M := M) g k
            (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
          (C * (k + 1)) *
            ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖)
    {m n : ℕ} (hmn : n ≤ m) :
    dist (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
          (spectralPartialSum (I := I) (M := M) g u m))
        (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
          (spectralPartialSum (I := I) (M := M) g u n)) ≤
      (C * (k + 1)) * Real.sqrt
        (weightedPartial (I := I) (M := M) g u k m -
          weightedPartial (I := I) (M := M) g u k n) := by
  classical
  rw [dist_eq_norm, toHs_spectralPartialSum_sub (I := I) (M := M) g u k hmn,
    tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g k]
  set F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
    eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n with hF
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i with hc
  refine le_trans (hC F c) ?_
  rw [show ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ =
        Real.sqrt (weightedPartial (I := I) (M := M) g u k m -
          weightedPartial (I := I) (M := M) g u k n) from ?_]
  rw [← finiteEigenComboHs_sdiff_normSq (I := I) (M := M) g u k hmn, hF, hc]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem spectralPartialSum_toHs_cauchy (u : TensorL2 0 2 g)
    (hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v = u)
    (k : ℕ) :
    CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
      (spectralPartialSum (I := I) (M := M) g u n)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := eigenSpan_pouHs_le_spectral (I := I) (M := M) g k
  obtain ⟨v, hv_eq⟩ := hu ((2 * k : ℕ) : ℝ) (by positivity)
  have hv_coeff : ∀ i, v.coeff i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i := by
    intro i
    have := tensorHsToL2_tensorL2Coeff (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      (show (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) by positivity) v i
    rw [hv_eq] at this
    exact this.symm
  have hwcauchy := weightedPartial_cauchySeq (I := I) (M := M) g u k v hv_coeff
  set Ck : ℝ := C * (k + 1) with hCk
  have hCk_pos : 0 < Ck + 1 := by positivity
  rw [Metric.cauchySeq_iff'] at hwcauchy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hwcauchy ((ε / (Ck + 1)) ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound := dist_toHs_spectralPartialSum_le (I := I) (M := M) g u k hC hn
  have hwlt : weightedPartial (I := I) (M := M) g u k n -
      weightedPartial (I := I) (M := M) g u k N < (ε / (Ck + 1)) ^ 2 := by
    have := hN n hn
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hwnn : 0 ≤ weightedPartial (I := I) (M := M) g u k n -
      weightedPartial (I := I) (M := M) g u k N := by
    have hmono : weightedPartial (I := I) (M := M) g u k N ≤
        weightedPartial (I := I) (M := M) g u k n := by
      unfold weightedPartial
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (eigenIdxFinset_mono (I := I) (M := M) g hn)
        (fun i _ _ => weightedPartial_term_nonneg (I := I) (M := M) g u k i)
    linarith
  calc dist (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (spectralPartialSum (I := I) (M := M) g u n))
          (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (spectralPartialSum (I := I) (M := M) g u N))
      ≤ Ck * Real.sqrt
          (weightedPartial (I := I) (M := M) g u k n -
            weightedPartial (I := I) (M := M) g u k N) := hbound
    _ < ε := by
        have hsqrt : Real.sqrt
            (weightedPartial (I := I) (M := M) g u k n -
              weightedPartial (I := I) (M := M) g u k N) < ε / (Ck + 1) := by
          rw [show ε / (Ck + 1) = Real.sqrt ((ε / (Ck + 1)) ^ 2) from
            (Real.sqrt_sq (by positivity)).symm]
          exact Real.sqrt_lt_sqrt hwnn hwlt
        have hCk_nn : 0 ≤ Ck := by positivity
        calc Ck * Real.sqrt
              (weightedPartial (I := I) (M := M) g u k n -
                weightedPartial (I := I) (M := M) g u k N)
            ≤ Ck * (ε / (Ck + 1)) := by
                apply mul_le_mul_of_nonneg_left (le_of_lt hsqrt) hCk_nn
          _ < ε := by
                rw [mul_div_assoc']
                rw [div_lt_iff₀ hCk_pos]
                nlinarith [hε, hCk_nn]

theorem spectralSmoothRealizesAsSmooth_holds :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g 0 2 := by
  classical
  intro u hu
  have hcauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
        (spectralPartialSum (I := I) (M := M) g u n)) :=
    fun k => spectralPartialSum_toHs_cauchy (I := I) (M := M) g u hu (2 * k)
  obtain ⟨T, hT⟩ :=
    smoothCcTensor_limit_of_allOrders_toHs_cauchy (I := I) (M := M) g 0 2 u
      (fun n => spectralPartialSum (I := I) (M := M) g u n) hcauchy
      (spectralPartialSum_toL2_tendsto (I := I) (M := M) g u)
  exact ⟨T, hT⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
