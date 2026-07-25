import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner








namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open Tensor0SBundle

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
private theorem grad_jet_norm
    (g : SmoothRiemannianMetric I M) (s j : ℕ) (T : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 (s + 1) j
        (covGrad (I := I) (M := M) g 0 s T)‖ =
      ‖iteratedCovGrad (I := I) g 0 s (j + 1) T‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j
          (covGrad (I := I) (M := M) g 0 s T)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 s (j + 1) T‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g
        (iteratedCovGrad (I := I) g 0 (s + 1) j
          (covGrad (I := I) (M := M) g 0 s T)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g (iteratedCovGrad (I := I) g 0 s (j + 1) T),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g ((s + 1) + j)
        (iteratedCovGrad (I := I) g 0 (s + 1) j
          (covGrad (I := I) (M := M) g 0 s T)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g (s + (j + 1))
        (iteratedCovGrad (I := I) g 0 s (j + 1) T)]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_covGrad_comm_rs
      (I := I) (M := M) g 0 s j T x
  nlinarith [norm_nonneg
    (iteratedCovGrad (I := I) g 0 (s + 1) j
      (covGrad (I := I) (M := M) g 0 s T)),
    norm_nonneg (iteratedCovGrad (I := I) g 0 s (j + 1) T)]



theorem hsC0_fiber_sq
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
        C ^ 2 * ‖ccTensorToHs (I := I) (M := M) g s
          ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖ ^ 2 := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 s
  obtain ⟨Chs, hChs, hhs⟩ := hsJet_le
    (I := I) (M := M) g s (Module.finrank ℝ E / 2 + 1)
  refine ⟨Cpt * Chs, mul_nonneg hCpt hChs, ?_⟩
  intro T x
  have hsq :
      ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤
        Chs * ‖ccTensorToHs (I := I) (M := M) g s
          ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖ := by
    simpa [Nat.add_assoc] using hhs T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 := hpt T x
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (Chs * ‖ccTensorToHs (I := I) (M := M) g s
            ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = (Cpt * Chs) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g s
            ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖ ^ 2 := by
      ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in


theorem scalar0_fiber_sq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 0) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 0 x (T.toSection x) =
      TensorRSField.scalar0 T.toSection x ^ 2 := by
  let A := TensorRSField.rs0 (n := (∞ : WithTop ℕ∞)) T.toSection
  have hTx : Tensor0SSpace.toRS0 (A x) = T.toSection x := by
    rw [← Tensor0SField.toRS0_eq (n := (∞ : WithTop ℕ∞)) A x]
    have hfield : A.toTensorRSField (∞ : WithTop ℕ∞) = T.toSection := by
      dsimp only [A]
      exact TensorRSField.toRS0_rs0
        (n := (∞ : WithTop ℕ∞)) T.toSection
    exact DFunLike.congr_fun hfield x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise, ← hTx,
    inner_toRS0_zero (I := I) (M := M) g x]
  have hscalar : tensor0SSpace_evalScalar x (A x) =
      TensorRSField.scalar0 T.toSection x := by
    rw [Tensor0SSpace.evalScalar_apply]
    rfl
  rw [hscalar, pow_two]



theorem scalar0_abs_le_hs
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g 0 0) (x : M),
      |TensorRSField.scalar0 T.toSection x| ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 0
          ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖ := by
  obtain ⟨C, hC, hbound⟩ := hsC0_fiber_sq (I := I) (M := M) g 0
  refine ⟨C, hC, ?_⟩
  intro T x
  have hsq :
      TensorRSField.scalar0 T.toSection x ^ 2 ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g 0
          ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖) ^ 2 := by
    rw [← scalar0_fiber_sq (I := I) (M := M) g T x]
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 0 x (T.toSection x)
          ≤ C ^ 2 * ‖ccTensorToHs (I := I) (M := M) g 0
              ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖ ^ 2 := hbound T x
      _ = (C * ‖ccTensorToHs (I := I) (M := M) g 0
              ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T‖) ^ 2 := by
        ring
  exact abs_le_of_sq_le_sq hsq (mul_nonneg hC (norm_nonneg _))



theorem hs2_fiber_sq
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
        C ^ 2 * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 s
  obtain ⟨Chs, hChs, hhs⟩ := hsJet_le (I := I) (M := M) g s 2
  refine ⟨Cpt * Chs, mul_nonneg hCpt hChs, ?_⟩
  intro T x
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpt' := hpt T x
  rw [hrange] at hpt'
  have hsq :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤
        Chs * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ := by
    simpa using hhs T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 := hpt'
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (Chs * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = (Cpt * Chs) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
      ring



theorem hs2_low2
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 s,
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖) ^ 2 := by
  obtain ⟨C, hC, hjet⟩ := hsJet_le (I := I) (M := M) g s 2
  refine ⟨C, hC, ?_⟩
  intro T
  have hsum : ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ := by
    simpa using hjet T
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)).trans
    (pow_le_pow_left₀
      (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)



theorem hs3_grad_low2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 s,
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s T).toSection x) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) T‖) ^ 2) ∧
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) j
            (covGrad (I := I) (M := M) g 0 s T)‖ ^ 2) ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 (s + 1)
  obtain ⟨Chs, hChs, hhs⟩ := hsJet_le (I := I) (M := M) g s 3
  let C : ℝ := Cpt * Chs + Chs + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) T‖
  let V : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s T
  have hN : 0 ≤ N := norm_nonneg _
  have hCptChs : Cpt * Chs ≤ C := by
    dsimp [C]
    nlinarith
  have hChsC : Chs ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hCpt hChs]
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hlin :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤ Chs * N := by
    simpa [N] using hhs T
  have hshift :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) j V‖ ^ 2 ≤
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 := by
    dsimp [V]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [grad_jet_norm (I := I) (M := M) g s 0 T,
      grad_jet_norm (I := I) (M := M) g s 1 T,
      grad_jet_norm (I := I) (M := M) g s 2 T]
    nlinarith [sq_nonneg
      ‖iteratedCovGrad (I := I) g 0 s 0 T‖]
  have hsqsum :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hlin_sq :
      (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 ≤
        (Chs * N) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hlin 2
  have hVjet :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) j V‖ ^ 2 ≤
        (C * N) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 := hshift.trans hsqsum
      _ ≤ (Chs * N) ^ 2 := hlin_sq
      _ ≤ (C * N) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hChs hN)
          (mul_le_mul_of_nonneg_right hChsC hN) 2
  constructor
  · intro x
    have hpt' := hpt V x
    rw [hrange] at hpt'
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          (V.toSection x)
          ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 (s + 1) j V‖ ^ 2 := hpt'
      _ ≤ Cpt ^ 2 * (Chs * N) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (hshift.trans (hsqsum.trans hlin_sq)) (sq_nonneg Cpt)
      _ = (Cpt * Chs * N) ^ 2 := by ring
      _ ≤ (C * N) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCpt hChs) hN)
          (mul_le_mul_of_nonneg_right hCptChs hN) 2
  · exact hVjet

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in


theorem hs2_op_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : SmoothCcTensor g 0 2,
      metricCauchySchwarzBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g T)
        (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) := by
  classical
  obtain ⟨C0, hC0, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g 2
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro T
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  have hN : 0 ≤ N := norm_nonneg _
  have hC : 0 ≤ C0 + 1 := by linarith
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
        ((C0 + 1) * N) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
          ≤ C0 ^ 2 * N ^ 2 := hpt T x
      _ ≤ (C0 + 1) ^ 2 * N ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg N)
      _ = ((C0 + 1) * N) ^ 2 := by ring
  intro x v w
  letI instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  letI instNormed : ∀ b : M,
      NormedAddCommGroup (Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    fun b =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) b
  have hnorm : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤
      (C0 + 1) * N := by
    rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 2 x (T.toSection x),
      ← riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g 0 2 x (T.toSection x)]
    calc
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x))
          ≤ Real.sqrt (((C0 + 1) * N) ^ 2) := Real.sqrt_le_sqrt (hpt' x)
      _ = (C0 + 1) * N := Real.sqrt_sq (mul_nonneg hC hN)
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt
    (I := I) (M := M) g T x
  have hsv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  have hvw : |smoothCcTensorBilinForm (I := I) g T x v w| ≤
      ((C0 + 1) * N) * Real.sqrt (g.inner x v v) *
        Real.sqrt (g.inner x w w) := by
    exact (hcs v w).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm hsv) hsw)
  have hwv : |smoothCcTensorBilinForm (I := I) g T x w v| ≤
      ((C0 + 1) * N) * Real.sqrt (g.inner x w w) *
        Real.sqrt (g.inner x v v) := by
    exact (hcs w v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm hsw) hsv)
  rw [ccTensorBilinSymm_apply]
  calc
    |(1 / 2 : ℝ) *
        (smoothCcTensorBilinForm (I := I) g T x v w + smoothCcTensorBilinForm (I := I) g T x w v)|
        ≤ (1 / 2 : ℝ) *
          (|smoothCcTensorBilinForm (I := I) g T x v w| +
            |smoothCcTensorBilinForm (I := I) g T x w v|) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (((C0 + 1) * N) * Real.sqrt (g.inner x v v) *
              Real.sqrt (g.inner x w w) +
            ((C0 + 1) * N) * Real.sqrt (g.inner x w w) *
              Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left (add_le_add hvw hwv) (by norm_num)
    _ = (C0 + 1) * N * Real.sqrt (g.inner x v v) *
          Real.sqrt (g.inner x w w) := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
