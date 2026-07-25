import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldIdentity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldMonomialRefoldL2JetWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldRicciFoldWeightKernel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldSharpGradKoszulResidualSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldResidualFieldBallUniform

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


private lemma bdWindowOneThree_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {B : ℝ}
    (hB1 : b 1 ≤ B) :
    Combinatorics.boundedFactorGridWindow b 1 3 ≤ 1 + B + B ^ 2 := by
  classical
  have hB0 : 0 ≤ B := le_trans (hb 1) hB1
  have hgrid0 : Combinatorics.boundedFactorGrid b 1 0 = 1 :=
    Combinatorics.boundedFactorGrid_zero b 1
  have hgrid1 : Combinatorics.boundedFactorGrid b 1 1 = b 1 := by
    rw [Combinatorics.boundedFactorGrid]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [show Finset.Nat.antidiagonalTuple 0 1 = ∅ from
      Finset.Nat.antidiagonalTuple_zero_succ 0]
    rw [show Finset.Nat.antidiagonalTuple 1 1 = {![1]} from
      Finset.Nat.antidiagonalTuple_one 1]
    rw [Finset.filter_empty, Finset.sum_empty]
    rw [Finset.filter_singleton]
    rw [if_pos (by decide : ∀ m : Fin 1, (![1] : Fin 1 → ℕ) m ≤ 1)]
    rw [Finset.sum_singleton]
    rw [Fin.prod_univ_one]
    norm_num
  have hgrid2 : Combinatorics.boundedFactorGrid b 1 2 = b 1 * b 1 := by
    rw [Combinatorics.boundedFactorGrid]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [show Finset.Nat.antidiagonalTuple 0 2 = ∅ from
      Finset.Nat.antidiagonalTuple_zero_succ 1]
    rw [show Finset.Nat.antidiagonalTuple 1 2 = {![2]} from
      Finset.Nat.antidiagonalTuple_one 2]
    rw [Finset.filter_empty, Finset.sum_empty]
    rw [Finset.filter_singleton]
    rw [if_neg (by decide : ¬ ∀ m : Fin 1, (![2] : Fin 1 → ℕ) m ≤ 1)]
    rw [Finset.sum_empty]
    have h22 : (Finset.Nat.antidiagonalTuple 2 2).filter
        (fun e : Fin 2 → ℕ => ∀ m, e m ≤ 1) = {![1, 1]} := by
      decide
    rw [h22, Finset.sum_singleton, Fin.prod_univ_two]
    change (0 : ℝ) + 0 + b (![1, 1] 0) * b (![1, 1] 1) = b 1 * b 1
    norm_num
  rw [Combinatorics.boundedFactorGridWindow, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hgrid0, hgrid1, hgrid2]
  nlinarith [hb 1, hB1, hB0, sq_nonneg (b 1 - B)]


theorem exists_ricciArmOrder0AACommCoeffField_realizedFam_fiberNormSq_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window (I := I) (M := M) g₀ hδ₁_lt
  obtain ⟨Csob, hCsob_nn, hcap1⟩ :=
    exists_sobolevConst_riemannianFiberNormSq_covGrad_T_le_sq (I := I) (M := M) g₀ a ha_super
  refine ⟨C 0 * (1 + (Csob * R) ^ 2 + ((Csob * R) ^ 2) ^ 2),
    mul_nonneg (hC_nn 0) (by positivity), ?_⟩
  intro T δ hδ_le hδ hδZ hball s hs x
  by_cases hM : Nonempty M
  swap
  · exact ((not_nonempty_iff.mp hM).false x).elim
  obtain ⟨x₀⟩ := hM
  have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
  have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  obtain ⟨hs0, hs1⟩ := hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have h0 := hpt (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le' hδ0 hδP 0 x
  rw [iteratedCovGrad_zero] at h0
  have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
  have hs2 : s * s ≤ 1 := by nlinarith
  have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤ (Csob * R) ^ 2 := by
    rw [hcP, iteratedCovGrad_smul_real]
    rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) =
        s • ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + 1) x]
    have hT1 := hcap1 T hR hball x
    nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x), hT1, hss, hs2, sq_nonneg s]
  have hwin := bdWindowOneThree_le
    (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x))
    (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)
    hb1
  exact le_trans h0 (mul_le_mul_of_nonneg_left hwin (hC_nn 0))


theorem exists_ricciArmOrder0AACommCoeffField_realizedFam_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window (I := I) (M := M) g₀ hδ₁_lt
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders (I := I) (M := M) g₀ a
      ha_super hR
  refine ⟨fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i), ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    obtain ⟨hs0, hs1⟩ := hs
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
    have hs2 : s * s ≤ 1 := by nlinarith
    have hptx : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
      intro x
      refine le_trans (hpt (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le' hδ0 hδP i x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hC_nn i)
      rw [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGridWindow]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Combinatorics.boundedFactorGrid, Combinatorics.boundedFactorGrid]
      refine Finset.sum_le_sum fun n _ => ?_
      refine Finset.sum_le_sum fun e _ => ?_
      refine Finset.prod_le_prod
        (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _)
        (fun m _ => ?_)
      rw [hcP, iteratedCovGrad_smul_real]
      rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) =
          s • ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) from by
        rw [SmoothCcTensor.toSection_smul]
        rfl]
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + e m) x]
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x), hss, hs2]
    obtain ⟨hWint, hWbound⟩ := hKflat T hball i
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)))
      (fun x => C i * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))
      (hWint.const_mul (C i)) hptx
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    refine le_trans (mul_le_mul_of_nonneg_left hWbound (hC_nn i)) (le_of_eq ?_)
    ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s))‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
    nlinarith [hwin_nn, hK_nn]

private lemma bdBoundedFactorGridWindow_mono_of_le (b b' : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbb : ∀ j, b j ≤ b' j) (K w : ℕ) :
    Combinatorics.boundedFactorGridWindow b K w ≤
      Combinatorics.boundedFactorGridWindow b' K w := by
  rw [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGridWindow]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Combinatorics.boundedFactorGrid, Combinatorics.boundedFactorGrid]
  refine Finset.sum_le_sum fun n _ => ?_
  refine Finset.sum_le_sum fun e _ => ?_
  exact Finset.prod_le_prod (fun m _ => hb (e m)) (fun m _ => hbb (e m))


theorem exists_ricciArmOrder0BgRCommCoeffField_realizedFam_backgroundDifference_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BgRCommCoeffFieldDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₁_lt
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders (I := I) (M := M) g₀ a
      ha_super hR
  refine ⟨fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i), ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    obtain ⟨hs0, hs1⟩ := hs
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have hPT : ∀ (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) := by
      intro l x
      rw [hcP, iteratedCovGrad_smul_real]
      rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) =
          s • ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) from by
        rw [SmoothCcTensor.toSection_smul]
        rfl]
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l) x]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)]
    have hptx : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s)
                - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
      intro x
      have h1 := hpt (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le' hδ0 hδP i x
      refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (hC_nn i))
      exact bdBoundedFactorGridWindow_mono_of_le _ _
        (fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _)
        (fun j => hPT j x) (i + 1) (i + 3)
    obtain ⟨hWint, hWbound⟩ := hKflat T hball i
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀))
      (fun x => C i * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))
      (hWint.const_mul (C i)) hptx
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    refine le_trans (mul_le_mul_of_nonneg_left hWbound (hC_nn i)) (le_of_eq (by ring))
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
    nlinarith [hwin_nn, hK_nn]

private lemma bdTupleWindow_le_boundedWindow (b : ℕ → ℝ) (_hb : ∀ j, 0 ≤ b j)
    {K W : ℕ} (hW : W ≤ K + 1) :
    Combinatorics.antidiagonalTupleGridWindow b W ≤
      Combinatorics.boundedFactorGridWindow b K W := by
  rw [Combinatorics.antidiagonalTupleGridWindow, Combinatorics.boundedFactorGridWindow]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  exact le_of_eq (Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega))

private lemma bdSingleCell_le_boundedGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {K q : ℕ} (hq : 1 ≤ q) (hqK : q ≤ K) :
    b q ≤ Combinatorics.boundedFactorGrid b K q := by
  have h := Combinatorics.single_factor_mul_boundedFactorGrid_le b hb (K := K) 0 q hq hqK
  rw [Combinatorics.boundedFactorGrid_zero, mul_one, zero_add] at h
  exact h

private lemma bdPairCell_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {K W q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₁K : q₁ ≤ K) (hq₂ : 1 ≤ q₂) (hq₂K : q₂ ≤ K)
    (hW : q₁ + q₂ < W) :
    b q₁ * b q₂ ≤ Combinatorics.boundedFactorGridWindow b K W := by
  have h2 : b q₂ ≤ Combinatorics.boundedFactorGrid b K q₂ :=
    bdSingleCell_le_boundedGrid b hb hq₂ hq₂K
  have h1 : b q₁ * Combinatorics.boundedFactorGrid b K q₂ ≤
      Combinatorics.boundedFactorGrid b K (q₂ + q₁) :=
    Combinatorics.single_factor_mul_boundedFactorGrid_le b hb q₂ q₁ hq₁ hq₁K
  have hle : b q₁ * b q₂ ≤ Combinatorics.boundedFactorGrid b K (q₂ + q₁) :=
    le_trans (mul_le_mul_of_nonneg_left h2 (hb q₁)) h1
  refine le_trans hle ?_
  exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)

private lemma sharpGradKoszulRaw_gridWindow (g₀ : SmoothRiemannianMetric I M) :
    ∃ CZ : ℕ → ℝ, (∀ w, 0 ≤ CZ w) ∧
      ∀ (τ : Equiv.Perm (Fin 6)) (T : SmoothCcTensor g₀ 0 2) (w K : ℕ), w + 1 ≤ K →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 6 w
              (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                    (koszulCovGradRaw (I := I) (M := M) g₀ T))
                  (koszulCovecCc (I := I) g₀ T)))).toSection x) ≤
          CZ w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) K (w + 3) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun w => diagonalGridGrowthFactor (E := E) w *
      (((w : ℝ) + 1) * (((w : ℝ) + 1) * (100 * fr ^ 3))),
    fun w => mul_nonneg (appCcGdiag_nonneg (E := E) w)
      (mul_nonneg (by positivity) (mul_nonneg (by positivity) (by positivity))), ?_⟩
  intro τ T w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W3 : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 3) with hW3_def
  have hW3_nn : 0 ≤ W3 := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 3)
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 6 w
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
        (koszulCovecCc (I := I) g₀ T)))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 6 w
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
        (koszulCovecCc (I := I) g₀ T))).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
      g₀ 0 6 τ
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
        (koszulCovecCc (I := I) g₀ T))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
        (koszulCovecCc (I := I) g₀ T)))
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) w x
  rw [hperm]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ w 0 3 6
    (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
    (koszulCovecCc (I := I) g₀ T) x) ?_
  have hΦ : ∀ w₁ : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₁) x
        ((iteratedCovGrad (I := I) g₀ 3 6 w₁
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))).toSection x) ≤
      fr * (fr * (fr * (10 * b (w₁ + 1)))) := by
    intro w₁
    have h3 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 5
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (koszulCovGradRaw (I := I) (M := M) g₀ T)) w₁ x
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (koszulCovGradRaw (I := I) (M := M) g₀ T)) w₁ x
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
      (koszulCovGradRaw (I := I) (M := M) g₀ T) w₁ x
    have h0 := riemannianFiberNormSq_iteratedCovGrad_bdKRaw_le (I := I) (M := M) g₀ T w₁ x
    refine le_trans h3 ?_
    refine mul_le_mul_of_nonneg_left (le_trans h2 ?_) hfr_nn
    refine mul_le_mul_of_nonneg_left (le_trans h1 ?_) hfr_nn
    exact mul_le_mul_of_nonneg_left h0 hfr_nn
  have hK : ∀ w₂ : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₂) x
        ((iteratedCovGrad (I := I) g₀ 0 3 w₂ (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * b (w₂ + 1) :=
    fun w₂ => bdRfns_iCG_koszulCovecCc_le (I := I) (M := M) g₀ T w₂ x
  have hcell : ∀ w₁ ∈ Finset.range (w + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₁) x
          ((iteratedCovGrad (I := I) g₀ 3 6 w₁
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))).toSection x) *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₂) x
            ((iteratedCovGrad (I := I) g₀ 0 3 w₂ (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      (((w : ℝ) + 1) * (100 * fr ^ 3)) * W3 := by
    intro w₁ hw₁
    rw [Finset.mem_range] at hw₁
    have hsum2 : ∑ w₂ ∈ Finset.range (w + 1 - w₁),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 3 w₂ (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
        ∑ w₂ ∈ Finset.range (w + 1 - w₁), 10 * b (w₂ + 1) :=
      Finset.sum_le_sum fun w₂ _ => hK w₂
    have hΦnn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₁) x
        ((iteratedCovGrad (I := I) g₀ 3 6 w₁
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (6 + w₁) x _
    have hsum2nn : (0 : ℝ) ≤ ∑ w₂ ∈ Finset.range (w + 1 - w₁), 10 * b (w₂ + 1) :=
      Finset.sum_nonneg fun w₂ _ => mul_nonneg (by norm_num) (hb (w₂ + 1))
    refine le_trans (mul_le_mul (hΦ w₁) hsum2
      (Finset.sum_nonneg fun w₂ _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + w₂) x _)
      (mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg hfr_nn
        (mul_nonneg (by norm_num) (hb (w₁ + 1))))))) ?_
    rw [Finset.mul_sum]
    have hterm : ∀ w₂ ∈ Finset.range (w + 1 - w₁),
        fr * (fr * (fr * (10 * b (w₁ + 1)))) * (10 * b (w₂ + 1)) ≤
        (100 * fr ^ 3) * W3 := by
      intro w₂ hw₂
      rw [Finset.mem_range] at hw₂
      have hpair : b (w₁ + 1) * b (w₂ + 1) ≤ W3 := by
        rw [hW3_def]
        exact bdPairCell_le_boundedWindow b hb (by omega) (by omega) (by omega) (by omega)
          (by omega)
      calc fr * (fr * (fr * (10 * b (w₁ + 1)))) * (10 * b (w₂ + 1))
          = (100 * fr ^ 3) * (b (w₁ + 1) * b (w₂ + 1)) := by ring
        _ ≤ (100 * fr ^ 3) * W3 :=
            mul_le_mul_of_nonneg_left hpair (by positivity)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    have hcard : ((w + 1 - w₁ : ℕ) : ℝ) ≤ (w : ℝ) + 1 := by
      have : (w + 1 - w₁ : ℕ) ≤ w + 1 := by omega
      exact_mod_cast this
    have hWnn : (0 : ℝ) ≤ (100 * fr ^ 3) * W3 := by positivity
    calc ((w + 1 - w₁ : ℕ) : ℝ) * ((100 * fr ^ 3) * W3)
        ≤ ((w : ℝ) + 1) * ((100 * fr ^ 3) * W3) :=
          mul_le_mul_of_nonneg_right hcard hWnn
      _ = (((w : ℝ) + 1) * (100 * fr ^ 3)) * W3 := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) w)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have h1 : ((w + 1 : ℕ) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
  rw [h1]
  exact le_of_eq (by ring)

private lemma sharpGradKoszulMvWeight_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CW : ℕ → ℝ, (∀ l, 0 ≤ CW l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (τ : Equiv.Perm (Fin 6))
        (P T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hboundP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (x : M)
        (_hPT : ∀ l' : ℕ,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x))
        (l K : ℕ), l + 1 ≤ K →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ τ T T)).toSection x) ≤
          CW l * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) K (l + 3) := by
  classical
  obtain ⟨C4, hC4_nn, hC4⟩ := bdPureDT_tgrid (I := I) (M := M) g₀ 4 hδ₀
  obtain ⟨CZ, hCZ_nn, hCZ⟩ := sharpGradKoszulRaw_gridWindow (I := I) (M := M) g₀
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l *
      ∑ u ∈ Finset.range (l + 1), C4 u *
        ∑ w ∈ Finset.range (l + 1 - u),
          CZ w * Combinatorics.windowPairCellCount (u + 1) (w + 3),
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun u _ => mul_nonneg (hC4_nn u)
        (Finset.sum_nonneg fun w _ => mul_nonneg (hCZ_nn w)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ τ P T htie δ hδ_le hδ0 hboundP x hPT l K hlK
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set bP : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hbP_def
  have hbP : ∀ l', 0 ≤ bP l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W3L : ℝ := Combinatorics.boundedFactorGridWindow b K (l + 3) with hW3L_def
  have hW3L_nn : 0 ≤ W3L := Combinatorics.boundedFactorGridWindow_nonneg b hb K (l + 3)
  rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ τ T T =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))) from rfl]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 0 6 4
    (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))) x) ?_
  have hcell : ∀ u ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)).toSection x) *
        ∑ w ∈ Finset.range (l + 1 - u),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 6 w
              (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T)))).toSection x) ≤
      (C4 u * ∑ w ∈ Finset.range (l + 1 - u),
        CZ w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W3L := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hDT : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) x
        ((iteratedCovGrad (I := I) g₀ 6 4 u
          (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
        C4 u * Combinatorics.boundedFactorGridWindow b K (u + 1) := by
      refine le_trans (hC4 g₁ P htie hδ_le hδ0 hboundP u x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hC4_nn u)
      refine le_trans (bdGridWindow_mono_of_le bP b hbP (fun j => hPT j) (u + 1)) ?_
      exact bdTupleWindow_le_boundedWindow b hb (by omega)
    have hZw : ∀ w ∈ Finset.range (l + 1 - u),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T)))).toSection x) ≤
        CZ w * Combinatorics.boundedFactorGridWindow b K (w + 3) := by
      intro w hw
      rw [Finset.mem_range] at hw
      exact hCZ τ T w K (by omega) x
    have hsum2 : ∑ w ∈ Finset.range (l + 1 - u),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T)))).toSection x) ≤
        ∑ w ∈ Finset.range (l + 1 - u),
          CZ w * Combinatorics.boundedFactorGridWindow b K (w + 3) :=
      Finset.sum_le_sum hZw
    refine le_trans (mul_le_mul hDT hsum2
      (Finset.sum_nonneg fun w _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w) x _)
      (mul_nonneg (hC4_nn u)
        (Combinatorics.boundedFactorGridWindow_nonneg b hb K (u + 1)))) ?_
    rw [Finset.mul_sum]
    have hgoal : ∀ w ∈ Finset.range (l + 1 - u),
        C4 u * Combinatorics.boundedFactorGridWindow b K (u + 1) *
          (CZ w * Combinatorics.boundedFactorGridWindow b K (w + 3)) ≤
        C4 u * (CZ w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W3L := by
      intro w hw
      rw [Finset.mem_range] at hw
      have hmul := Combinatorics.boundedFactorGridWindow_mul_le b hb K (u + 1) (w + 3)
        (by omega) (by omega)
      have hmono := Combinatorics.boundedFactorGridWindow_mono b hb
        (le_refl K) (show u + 1 + (w + 3) - 1 ≤ l + 3 by omega)
      calc C4 u * Combinatorics.boundedFactorGridWindow b K (u + 1) *
            (CZ w * Combinatorics.boundedFactorGridWindow b K (w + 3))
          = (C4 u * CZ w) *
              (Combinatorics.boundedFactorGridWindow b K (u + 1) *
                Combinatorics.boundedFactorGridWindow b K (w + 3)) := by ring
        _ ≤ (C4 u * CZ w) *
              (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                Combinatorics.boundedFactorGridWindow b K (u + 1 + (w + 3) - 1)) := by
            refine mul_le_mul_of_nonneg_left hmul ?_
            exact mul_nonneg (hC4_nn u) (hCZ_nn w)
        _ ≤ (C4 u * CZ w) *
              (Combinatorics.windowPairCellCount (u + 1) (w + 3) * W3L) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC4_nn u) (hCZ_nn w))
            refine mul_le_mul_of_nonneg_left hmono ?_
            exact Combinatorics.windowPairCellCount_nonneg _ _
        _ = C4 u * (CZ w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W3L := by
            ring
    refine le_trans (Finset.sum_le_sum hgoal) (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  have hrw : ∑ u ∈ Finset.range (l + 1),
      (C4 u * ∑ w ∈ Finset.range (l + 1 - u),
        CZ w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W3L =
      (∑ u ∈ Finset.range (l + 1),
        C4 u * ∑ w ∈ Finset.range (l + 1 - u),
          CZ w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W3L := by
    rw [Finset.sum_mul]
  rw [hrw]
  exact le_of_eq (by ring)

private lemma sharpGradKoszulComposite_pointwise_boundedWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hboundP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        (∀ l' : ℕ,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
                (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW, hCW_nn, hCW⟩ := sharpGradKoszulMvWeight_gridWindow (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CP i' *
        ∑ l ∈ Finset.range (i + 1 - i'),
          (fr ^ 2 * (16 * CW l)) * Combinatorics.windowPairCellCount (i' + 1) (l + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCP_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (hCW_nn l)))
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P T htie δ hδ_le hδ0 hboundP i x hPT
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set bP : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hbP_def
  have hbP : ∀ l', 0 ≤ bP l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set WT : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWT_def
  have hWT_nn : 0 ≤ WT :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))) x) ?_
  have hXiJet : ∀ l : ℕ, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))))).toSection x) ≤
      (fr ^ 2 * (16 * CW l)) * Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3) := by
    intro l hl
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
        g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))) l x
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)) l x
    have hsub := bdRfns_iCG_sub_le (I := I) (M := M) g₀ 0 4 l
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T)
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T) x
    have hadd12 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 l
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T) (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) x
    have hadd34 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 l
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T) (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T) x
    have hW1 := hCW g₁ bdSGKTau1 P T htie hδ_le hδ0 hboundP x hPT l (i + 1) (by omega)
    have hW2 := hCW g₁ bdSGKTau2 P T htie hδ_le hδ0 hboundP x hPT l (i + 1) (by omega)
    have hW3 := hCW g₁ bdSGKTau3 P T htie hδ_le hδ0 hboundP x hPT l (i + 1) (by omega)
    have hW4 := hCW g₁ bdSGKTau4 P T htie hδ_le hδ0 hboundP x hPT l (i + 1) (by omega)
    have hXi4 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))).toSection x) ≤
        (16 * CW l) * Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3) := by
      have hWnn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3) :=
        Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (l + 3)
      nlinarith [hsub, hadd12, hadd34, hW1, hW2, hW3, hW4, hWnn, hCW_nn l,
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T)).toSection x),
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)).toSection x),
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T)).toSection x),
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T)).toSection x),
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T)).toSection x),
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)).toSection x)]
    refine le_trans h2 ?_
    have hstep : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))).toSection x) ≤
        fr * ((16 * CW l) * Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3)) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hXi4 hfr_nn)
    refine le_trans (mul_le_mul_of_nonneg_left hstep hfr_nn) (le_of_eq (by ring))
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))))).toSection x) ≤
      (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr ^ 2 * (16 * CW l)) * Combinatorics.windowPairCellCount (i' + 1) (l + 3)) * WT := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hPTO : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CP i' * Combinatorics.boundedFactorGridWindow b (i + 1) (i' + 1) := by
      refine le_trans (hCP g₁ P htie hδ_le hδ0 hboundP i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCP_nn i')
      refine le_trans (bdGridWindow_mono_of_le bP b hbP (fun j => hPT j) (i' + 1)) ?_
      exact bdTupleWindow_le_boundedWindow b hb (by omega)
    have hsum2 : ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T + sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))))).toSection x) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (fr ^ 2 * (16 * CW l)) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hXiJet l (by omega)
    refine le_trans (mul_le_mul hPTO hsum2
      (Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
      (mul_nonneg (hCP_nn i')
        (Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i' + 1)))) ?_
    rw [Finset.mul_sum]
    have hgoal : ∀ l ∈ Finset.range (i + 1 - i'),
        CP i' * Combinatorics.boundedFactorGridWindow b (i + 1) (i' + 1) *
          ((fr ^ 2 * (16 * CW l)) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3)) ≤
        CP i' * ((fr ^ 2 * (16 * CW l)) *
          Combinatorics.windowPairCellCount (i' + 1) (l + 3)) * WT := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hmul := Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
        (i' + 1) (l + 3) (by omega) (by omega)
      have hmono := Combinatorics.boundedFactorGridWindow_mono b hb
        (le_refl (i + 1)) (show i' + 1 + (l + 3) - 1 ≤ i + 3 by omega)
      have hcnn : (0 : ℝ) ≤ CP i' * (fr ^ 2 * (16 * CW l)) :=
        mul_nonneg (hCP_nn i')
          (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (hCW_nn l)))
      calc CP i' * Combinatorics.boundedFactorGridWindow b (i + 1) (i' + 1) *
            ((fr ^ 2 * (16 * CW l)) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3))
          = (CP i' * (fr ^ 2 * (16 * CW l))) *
              (Combinatorics.boundedFactorGridWindow b (i + 1) (i' + 1) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (l + 3)) := by ring
        _ ≤ (CP i' * (fr ^ 2 * (16 * CW l))) *
              (Combinatorics.windowPairCellCount (i' + 1) (l + 3) *
                Combinatorics.boundedFactorGridWindow b (i + 1)
                  (i' + 1 + (l + 3) - 1)) :=
            mul_le_mul_of_nonneg_left hmul hcnn
        _ ≤ (CP i' * (fr ^ 2 * (16 * CW l))) *
              (Combinatorics.windowPairCellCount (i' + 1) (l + 3) * WT) := by
            refine mul_le_mul_of_nonneg_left ?_ hcnn
            refine mul_le_mul_of_nonneg_left hmono ?_
            exact Combinatorics.windowPairCellCount_nonneg _ _
        _ = CP i' * ((fr ^ 2 * (16 * CW l)) *
              Combinatorics.windowPairCellCount (i' + 1) (l + 3)) * WT := by ring
    refine le_trans (Finset.sum_le_sum hgoal) (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  have hrw : ∑ i' ∈ Finset.range (i + 1),
      (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr ^ 2 * (16 * CW l)) * Combinatorics.windowPairCellCount (i' + 1) (l + 3)) * WT =
      (∑ i' ∈ Finset.range (i + 1),
        CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
          (fr ^ 2 * (16 * CW l)) *
            Combinatorics.windowPairCellCount (i' + 1) (l + 3)) * WT := by
    rw [Finset.sum_mul]
  rw [hrw]
  exact le_of_eq (by ring)


theorem exists_ricciArmSharpGradKoszulResidualField_realizedFam_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ :=
    sharpGradKoszulComposite_pointwise_boundedWindow (I := I) (M := M) g₀ hδ₁_lt
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders (I := I) (M := M) g₀ a
      ha_super hR
  refine ⟨fun i => 4 * (C i * Kflat i),
    fun i => mul_nonneg (by norm_num) (mul_nonneg (hC_nn i) (hKflat_nn i)), ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    obtain ⟨hs0, hs1⟩ := hs
    have htie0 : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ (s • T) y v w := by
      intro y v w
      have h0 := htie0 y v w
      rwa [show convexPerturbation (I := I) g₀ T 0 s = s • T from by
        rw [convexPerturbation, smul_zero, zero_add]] at h0
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have hfield : ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T) =
        ((2 : ℝ) * (s * s)) •
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))) := by
      rw [bdSGK_eq_refold (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (s • T) (s • T) htie]
      rw [bdSGKXi_smul (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) T s]
      rw [appCcRS_smul_right (I := I) (M := M) g₀ 2 6 2 (s * s)
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))]
      rw [smul_smul]
    rw [hfield, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, mul_pow]
    have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
    have hs2 : s * s ≤ 1 := by nlinarith
    have habs2 : |(2 : ℝ) * (s * s)| ^ 2 ≤ 4 := by
      rw [abs_mul]
      have h1 : |(2 : ℝ)| = 2 := by norm_num
      have h2 : |s * s| = s * s := abs_of_nonneg hss
      rw [h1, h2]
      nlinarith [hss, hs2]
    have hptx : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
      intro x
      refine hpt (realizedFam (I := I) g₀ T 0 hδ hδZ s) (convexPerturbation (I := I) g₀ T 0 s) T htie0 hδ_le' hδ0 hδP i x
        (fun l' => ?_)
      rw [hcP, iteratedCovGrad_smul_real]
      rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) =
          s • ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) from by
        rw [SmoothCcTensor.toSection_smul]
        rfl]
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l') x]
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x
        ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x), hs2, hss]
    obtain ⟨hWint, hWbound⟩ := hKflat T hball i
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))))
      (fun x => C i * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))
      (hWint.const_mul (C i)) hptx
    have key2 : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))))‖ ^ 2 ≤
        C i * (Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hWbound (hC_nn i)
    nlinarith [key2, habs2, hwin_nn, hC_nn i, hKflat_nn i,
      sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))))‖,
      sq_abs ((2 : ℝ) * (s * s)),
      mul_nonneg (hC_nn i) (mul_nonneg (hKflat_nn i) hwin_nn)]
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ 4 * (C i * Kflat i) :=
      mul_nonneg (by norm_num) (mul_nonneg (hC_nn i) (hKflat_nn i))
    nlinarith [hwin_nn, hK_nn]

private theorem ricciFoldWeightComposite_pointwise_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (Λ0 : ℝ) (hΛ0 : 0 ≤ Λ0) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hboundP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hPT : ∀ (l : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x))
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
                (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                      palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))))).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 2) := by
  classical
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₀
  have hK4ex : ∀ l' : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ b : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l') b
        ((iteratedCovGrad (I := I) g₀ 6 4 l'
          (cometricDoubleTraceField (I := I) g₀ 4)).toSection b) ≤ K :=
    fun l' => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ 6 (4 + l')
      (iteratedCovGrad (I := I) g₀ 6 4 l' (cometricDoubleTraceField (I := I) g₀ 4))
  choose K4 hK4_nn hK4 using hK4ex
  have hK5ex : ∀ m' : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ b : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + m') b
        ((iteratedCovGrad (I := I) g₀ 2 6 m'
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection b) ≤ K :=
    fun m' => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ 2 (6 + m')
      (iteratedCovGrad (I := I) g₀ 2 6 m'
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))
  choose K5 hK5_nn hK5 using hK5ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set C6 : ℕ → ℝ := fun m => diagonalGridGrowthFactor (E := E) m *
    ∑ m' ∈ Finset.range (m + 1),
      K5 m' * (((m + 1 - m' : ℕ) : ℝ) * (Λ0 + 1)) with hC6_def
  have hC6_nn : ∀ m, 0 ≤ C6 m := by
    intro m
    rw [hC6_def]
    exact mul_nonneg (appCcGdiag_nonneg (E := E) m)
      (Finset.sum_nonneg fun m' _ => mul_nonneg (hK5_nn m')
        (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
  set C7 : ℕ → ℝ := fun l => diagonalGridGrowthFactor (E := E) l *
    ∑ l' ∈ Finset.range (l + 1),
      K4 l' * ∑ m ∈ Finset.range (l + 1 - l'), C6 m with hC7_def
  have hC7_nn : ∀ l, 0 ≤ C7 l := by
    intro l
    rw [hC7_def]
    exact mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun l' _ => mul_nonneg (hK4_nn l')
        (Finset.sum_nonneg fun m _ => hC6_nn m))
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
      CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * (4 * C7 l))) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCP_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg (by norm_num) (hC7_nn l))))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P T htie δ hδ_le hδ0 hboundP hPT hT0 i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  set bP : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hbP_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hbP : ∀ l', 0 ≤ bP l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hbPb : ∀ l', bP l' ≤ b l' := fun l' => hPT l' x
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (i + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  have hTcell : ∀ n : ℕ, b n ≤ (Λ0 + 1) * Combinatorics.antidiagonalTupleGridWindow b (n + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      have h0 : b 0 ≤ Λ0 := by
        have := hT0 x
        rw [hb_def]
        simpa [iteratedCovGrad_zero] using this
      have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (0 + 1) :=
        Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by norm_num)
      nlinarith [hΛ0, hone, h0, hb 0]
    · have hsingle : b n ≤ Combinatorics.antidiagonalTupleGrid b n :=
        bdSingle_b_le_grid b hb n hn1
      have hgw : Combinatorics.antidiagonalTupleGrid b n ≤
          Combinatorics.antidiagonalTupleGridWindow b (n + 1) :=
        Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
      have hwnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (n + 1) :=
        Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (n + 1)
      nlinarith [le_trans hsingle hgw, hΛ0, hwnn]
  have hInner : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 6 m
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) ≤
        C6 m * Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
    intro m
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ m 0 2 6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T x) ?_
    have hwin_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (m + 2) :=
      Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (m + 2)
    have hcell : ∀ m' ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + m') x
            ((iteratedCovGrad (I := I) g₀ 2 6 m'
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) *
          ∑ n ∈ Finset.range (m + 1 - m'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 0 2 n T).toSection x) ≤
        (K5 m' * (((m + 1 - m' : ℕ) : ℝ) * (Λ0 + 1))) *
          Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
      intro m' hm'
      rw [Finset.mem_range] at hm'
      have hA1 := hK5 m' x
      have hA2 : (∑ n ∈ Finset.range (m + 1 - m'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 2 n T).toSection x)) ≤
          (((m + 1 - m' : ℕ) : ℝ) * (Λ0 + 1)) *
            Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
        have hstep : ∀ n ∈ Finset.range (m + 1 - m'), b n ≤
            (Λ0 + 1) * Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
          intro n hn
          rw [Finset.mem_range] at hn
          refine le_trans (hTcell n) ?_
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
        calc (∑ n ∈ Finset.range (m + 1 - m'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 0 2 n T).toSection x))
            ≤ ∑ _n ∈ Finset.range (m + 1 - m'),
                (Λ0 + 1) * Combinatorics.antidiagonalTupleGridWindow b (m + 2) :=
              Finset.sum_le_sum hstep
          _ = (((m + 1 - m' : ℕ) : ℝ) * (Λ0 + 1)) *
                Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
              ring
      have hsum_nn : (0 : ℝ) ≤ ∑ n ∈ Finset.range (m + 1 - m'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 2 n T).toSection x) :=
        Finset.sum_nonneg fun n _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + n) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + m') x
            ((iteratedCovGrad (I := I) g₀ 2 6 m'
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) *
          ∑ n ∈ Finset.range (m + 1 - m'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 0 2 n T).toSection x)
          ≤ K5 m' * ((((m + 1 - m' : ℕ) : ℝ) * (Λ0 + 1)) *
              Combinatorics.antidiagonalTupleGridWindow b (m + 2)) :=
            mul_le_mul hA1 hA2 hsum_nn (hK5_nn m')
        _ = (K5 m' * (((m + 1 - m' : ℕ) : ℝ) * (Λ0 + 1))) *
              Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
      (appCcGdiag_nonneg (E := E) m)) ?_
    rw [hC6_def, ← Finset.sum_mul, ← mul_assoc]
  have hWA : ∀ (σw : Equiv.Perm (Fin 6)) (l : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)))).toSection x) ≤
        C7 l * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
    intro σw l
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ l 0 6 4
      (cometricDoubleTraceField (I := I) g₀ 4)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)) x) ?_
    have hperm : ∀ m : ℕ,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 6 m
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 6 m
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) :=
      fun m => riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
        g₀ 0 6 σw
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) m x
    have hcell : ∀ l' ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l') x
            ((iteratedCovGrad (I := I) g₀ 6 4 l'
              (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
          ∑ m ∈ Finset.range (l + 1 - l'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 6 m
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x) ≤
        (K4 l' * ∑ m ∈ Finset.range (l + 1 - l'), C6 m) *
          Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
      intro l' hl'
      rw [Finset.mem_range] at hl'
      have hA1 := hK4 l' x
      have hA2 : (∑ m ∈ Finset.range (l + 1 - l'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 6 m
              (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x)) ≤
          (∑ m ∈ Finset.range (l + 1 - l'), C6 m) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_range] at hm
        rw [hperm m]
        refine le_trans (hInner m) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hC6_nn m)
        exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
      have hsum_nn : (0 : ℝ) ≤ ∑ m ∈ Finset.range (l + 1 - l'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 6 m
              (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x) :=
        Finset.sum_nonneg fun m _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + m) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l') x
            ((iteratedCovGrad (I := I) g₀ 6 4 l'
              (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
          ∑ m ∈ Finset.range (l + 1 - l'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 6 m
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x)
          ≤ K4 l' * ((∑ m ∈ Finset.range (l + 1 - l'), C6 m) *
              Combinatorics.antidiagonalTupleGridWindow b (l + 2)) :=
            mul_le_mul hA1 hA2 hsum_nn (hK4_nn l')
        _ = (K4 l' * ∑ m ∈ Finset.range (l + 1 - l'), C6 m) *
              Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
      (appCcGdiag_nonneg (E := E) l)) ?_
    rw [hC7_def, ← Finset.sum_mul, ← mul_assoc]
  have hXitower : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) ≤
      (fr * (fr * (4 * C7 l))) * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
    intro l
    have hperm := riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
      g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)) l x
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
        palatiniRicciFoldWeightB (I := I) (M := M) g₀ T) l x
    have hW4 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) ≤
        (4 * C7 l) * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
      rw [iteratedCovGrad_add]
      have hsplit : ((iteratedCovGrad (I := I) g₀ 0 4 l
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T) +
          iteratedCovGrad (I := I) g₀ 0 4 l
            (palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 l
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 l
              (palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x := by
        rw [SmoothCcTensor.toSection_add]
        rfl
      rw [hsplit]
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x)
      have hA' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T)).toSection x) ≤
          C7 l * Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
        hWA (Equiv.swap (1 : Fin 6) 3) l
      have hB' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) ≤
          C7 l * Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
        hWA palatiniRicciFoldWeightBPerm l
      linarith
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) := h2
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x)) :=
          mul_le_mul_of_nonneg_left h1 hfr_nn
      _ ≤ fr * (fr * ((4 * C7 l) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW4 hfr_nn) hfr_nn
      _ = (fr * (fr * (4 * C7 l))) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by ring
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                    palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) ≤
      (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * (4 * C7 l))) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CP i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) := by
      refine le_trans (hCP g₁ P htie hδ_le hδ0 hboundP i' x) ?_
      exact mul_le_mul_of_nonneg_left
        (bdGridWindow_mono_of_le bP b hbP hbPb (i' + 1)) (hCP_nn i')
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (fr * (fr * (4 * C7 l))) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
      Finset.sum_le_sum fun l _ => hXitower l
    have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
    have hA1_rhs_nn : (0 : ℝ) ≤ CP i' *
        Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      mul_nonneg (hCP_nn i')
        (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * (4 * C7 l))) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CP i' * ((fr * (fr * (4 * C7 l))) *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1 + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
          Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1) :=
      Combinatorics.antidiagonalTupleGridWindow_mul_le b hb i' (l + 1)
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1) ≤ W := by
      rw [hW_def]
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hfrC_nn : (0 : ℝ) ≤ fr * (fr * (4 * C7 l)) :=
      mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg (by norm_num) (hC7_nn l)))
    calc CP i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
          ((fr * (fr * (4 * C7 l))) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2))
        = (CP i' * (fr * (fr * (4 * C7 l)))) *
            (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l + 1 + 1)) := by
          rw [show l + 2 = l + 1 + 1 from rfl]
          ring
      _ ≤ (CP i' * (fr * (fr * (4 * C7 l)))) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCP_nn i') hfrC_nn
      _ ≤ (CP i' * (fr * (fr * (4 * C7 l)))) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) * W) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCP_nn i') hfrC_nn)
          exact mul_le_mul_of_nonneg_left hmono
            (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
      _ = (CP i' * ((fr * (fr * (4 * C7 l))) *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1))) * W := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]


theorem exists_ricciArmRicciFoldRemainderField_realizedFam_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Csob, hCsob_nn, hTcapAll⟩ :=
    exists_sobolevConst_riemannianFiberNormSq_T_le_sq (I := I) (M := M) g₀ a ha_super
  obtain ⟨C, hC_nn, hpt⟩ := ricciFoldWeightComposite_pointwise_gridWindow (I := I) (M := M)
    g₀ hδ₁_lt ((Csob * R) ^ 2) (sq_nonneg _)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    bdL2_tameEnvelope_of_gridWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 2), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k), ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    obtain ⟨hs0, hs1⟩ := hs
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have hPT : ∀ (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) := by
      intro l x
      rw [hcP, iteratedCovGrad_smul_real]
      rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) =
          s • ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) from by
        rw [SmoothCcTensor.toSection_smul]
        rfl]
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l) x]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)]
    have hfield : ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T) =
        ((-(1 / 2) : ℝ) * s) •
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))) := by
      rw [bdRicciFold_eq_refold (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)]
      rw [bdRicciFoldXi_smul (I := I) (M := M) g₀ T s]
      rw [appCcRS_smul_right (I := I) (M := M) g₀ 2 6 2 s
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))]
      rw [smul_smul]
    rw [hfield, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, mul_pow]
    have habs2 : |(-(1 / 2) : ℝ) * s| ^ 2 ≤ 1 := by
      rw [abs_mul]
      have h1 : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
      have h2 : |s| ≤ 1 := by
        rw [abs_of_nonneg hs0]
        exact hs1
      rw [h1]
      nlinarith [abs_nonneg s]
    have hmain := hKg T hball i (C i) (hC_nn i)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))))
      (fun x => hpt (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) T htie hδ_le' hδ0 hδP hPT
        (fun x' => hTcapAll T hR hball x') i x)
    nlinarith [hmain, habs2, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))))‖,
      sq_abs ((-(1 / 2) : ℝ) * s)]
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 2), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k)
    nlinarith [hwin_nn, hK_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
