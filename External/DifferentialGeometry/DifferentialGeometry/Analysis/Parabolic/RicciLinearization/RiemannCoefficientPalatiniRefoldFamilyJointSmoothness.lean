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

def riemannPalatiniRefoldC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ((1 / 2 : ℝ) •
    (curvatureActionKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (qA 0) (qA 1) (qA 2) (qA 3)
      + curvatureActionKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (qB 0) (qB 1) (qB 2) (qB 3)))


omit [BoundarylessManifold I M] in
@[simp] lemma riemannPalatiniRefoldC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB 0 = 0 := by
  rw [riemannPalatiniRefoldC2Family, zero_smul]

def IsFramePairPartner (qA qB : Fin 4 → Equiv.Perm (Fin 4)) : Prop :=
  ∀ k : Fin 4, qB k = Equiv.swap (0 : Fin 4) 1 * qA k

lemma not_isFramePairPartner_self (q : Fin 4 → Equiv.Perm (Fin 4)) :
    ¬ IsFramePairPartner q q := by
  intro h
  have h0 : Equiv.swap (0 : Fin 4) 1 = 1 := right_eq_mul.mp (h 0)
  have h1 : (Equiv.swap (0 : Fin 4) 1) 0 = (1 : Equiv.Perm (Fin 4)) 0 := by rw [h0]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h1
  exact absurd h1 (by decide)

def deTurckLieCovDerivArmField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffCovDerivBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := dLaBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem deTurckLieCovDerivArmField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffCovDerivBiContrFib (I := I) g₁ g_bg x)) := rfl

def deTurckLieEndoArmField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem deTurckLieEndoArmField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)) := rfl


omit [I.Boundaryless] in
theorem deTurckLieCoeffField_eq_covDerivArm_add_endoArm
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg
        + deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg := by
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieCoeffField_toSection, deTurckLieCovDerivArmField_toSection,
    deTurckLieEndoArmField_toSection]
  rfl

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem exists_ricciArmOrder0RiemannCoeff_realizedFam_riemannianFiberNormSq_ballUniform_sq
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
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ (max_lt hδ₀ one_pos)
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  obtain ⟨Kbg, hKbg_nn, hKbg_bd⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  set F : ℝ := (1 + (Csob * R) ^ 2) ^ 2 with hF_def
  have hF_nn : (0 : ℝ) ≤ F := by positivity
  set cnt : ℝ := ∑ k ∈ Finset.range 3, ∑ n ∈ Finset.range (k + 1),
    ((Finset.Nat.antidiagonalTuple n k).card : ℝ) with hcnt_def
  have hcnt_nn : (0 : ℝ) ≤ cnt :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun n _ => Nat.cast_nonneg _
  have hsum_nn : (0 : ℝ) ≤ 2 * (CD 0 * (cnt * F)) + 2 * Kbg := by
    have h1 : (0 : ℝ) ≤ CD 0 * (cnt * F) :=
      mul_nonneg (hCD_nn 0) (mul_nonneg hcnt_nn hF_nn)
    linarith
  refine ⟨Real.sqrt (2 * (CD 0 * (cnt * F)) + 2 * Kbg), Real.sqrt_nonneg _, ?_⟩
  intro T δ hδ_le hδ hδZ hTball s hs x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    abs_convex_smallConstant_lt_one hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : (0 : ℝ) ≤ m := le_max_right _ _
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ + |s| * δ = (1 - s) * δ + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ + s * δ ≤ m := by
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    have heq : (1 - s) * δ + s * δ = δ := by ring
    linarith
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hCD0 := hCD (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) htie (le_of_eq hm_def) hm0 hδP 0 x
  have hicg0 : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_sub (I := I) g₀ 0 2 j T T
    simp only [sub_self] at h
    exact h
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j _
    rw [hicg0 j, norm_zero]
    exact hR
  have hCsob_sum := hCsob T 0 hR hTball hZball s ⟨hs0, hs1⟩ x
  have hterm_nn : ∀ j ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x‖) := by
    intro j _
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    exact norm_nonneg _
  have hcell : ∀ j : ℕ, j < 3 →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤
        1 + (Csob * R) ^ 2 := by
    intro j hj
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    have hbridge := norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M)
      g₀ 0 (2 + j) x
      (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T 0 s))
    have hnorm_le : ‖((iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
          TensorRSSpace 0 (2 + j) I x)‖ ≤ Csob * R :=
      le_trans (Finset.single_le_sum hterm_nn (Finset.mem_range.mpr hj)) hCsob_sum
    have hsq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x) =
        ‖((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
            TensorRSSpace 0 (2 + j) I x)‖ ^ 2 := by
      rw [hbridge, Real.sq_sqrt
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _)]
    rw [hsq]
    have h1 : ‖((iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
          TensorRSSpace 0 (2 + j) I x)‖ ^ 2 ≤ (Csob * R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
    linarith
  have hprodcell : ∀ k ∈ Finset.range 3, ∀ n ∈ Finset.range (k + 1),
      ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
      (∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤ F := by
    intro k hk n hn e he
    have hk2 : k ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hn2 : n ≤ 2 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hk2
    have hsum_e : (∑ i : Fin n, e i) = k := Finset.Nat.mem_antidiagonalTuple.mp he
    have hem : ∀ m' : Fin n, e m' < 3 := by
      intro m'
      have hle : e m' ≤ k := by
        calc e m' ≤ ∑ i : Fin n, e i :=
              Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m')
          _ = k := hsum_e
      omega
    have hstep : (∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤
        ∏ _m' : Fin n, (1 + (Csob * R) ^ 2) :=
      Finset.prod_le_prod
        (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m') x _)
        (fun m' _ => hcell (e m') (hem m'))
    refine le_trans hstep ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF_def]
    exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg (Csob * R))) hn2
  have hgrid_le : (∑ k ∈ Finset.range 3, ∑ n ∈ Finset.range (k + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
        ∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
            (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤ cnt * F := by
    rw [hcnt_def, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun n hn => ?_)
    calc (∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x))
        ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, F :=
          Finset.sum_le_sum (fun e he => hprodcell k hk n hn e he)
      _ = (Finset.Nat.antidiagonalTuple n k).card • F := Finset.sum_const F
      _ = ((Finset.Nat.antidiagonalTuple n k).card : ℝ) * F := nsmul_eq_mul _ _
  have hdiff_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
      CD 0 * (cnt * F) :=
    le_trans hCD0 (mul_le_mul_of_nonneg_left hgrid_le (hCD_nn 0))
  have hbg_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤ Kbg :=
    hKbg_bd x
  have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x =
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) +
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) := by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    abel
  have hfin : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤
      2 * (CD 0 * (cnt * F)) + 2 * Kbg := by
    rw [hsplit]
    have htri := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
    linarith
  rw [Real.sq_sqrt hsum_nn]
  exact hfin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_add_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_const_smul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_smulFun_local {r s : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

private noncomputable def outerPairBilinChartα (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g α x k l * K X (chartBasisVecFiber (I := I) α k x)) •
          (ContinuousLinearMap.flip Dd (chartBasisVecFiber (I := I) α l x))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma outerPairBilinChartα_apply (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilinChartα (I := I) g α K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k l *
          (K X (chartBasisVecFiber (I := I) α k x) *
            Dd X' (chartBasisVecFiber (I := I) α l x)) := by
  rw [outerPairBilinChartα, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma double_frame_bilin_trace_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (K (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x) *
            Dd (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilinChartα (I := I) g α K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilinChartα_apply]
    have h := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply, smul_eq_mul] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
    (outerPairBilinChartα (I := I) g α K Dd) B hB
  simp only [smul_eq_mul] at hout
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilinChartα_apply]

private def toModelEvalCLM (s : ℕ) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModelEvalCLM_apply (s : ℕ) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    toModelEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

private def pairFeedScalarCLM (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (toModelEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma pairFeedScalarCLM_apply (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) (p q : TangentSpace I x) :
    pairFeedScalarCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel (𝕜 := ℝ) G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [pairFeedScalarCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, toModelEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p) (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma curvatureRefoldMonomialBiContrFib_toModel_chartα
    (g : SmoothRiemannianMetric I M) (W : Π b : M, Tensor0SSpace 2 I b)
    (σp : Equiv.Perm (Fin 4)) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (G : Tensor0SSpace 4 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (curvatureActionMonomialTrace (I := I) (M := M) g W σp x G) v =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
              ![(chartBasisVecFiber (I := I) α m x : E),
                (chartBasisVecFiber (I := I) α k x : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ) G
              (fun i => (Fin.cons ((chartBasisVecFiber (I := I) α n x : E))
                (Fin.cons ((chartBasisVecFiber (I := I) α l x : E)) v) : Fin 4 → E)
                (σp i)))) := by
  classical
  have hBf_on : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [show curvatureActionMonomialTrace (I := I) (M := M) g W σp x =
      curvatureActionMonomialFrameTrace (I := I) (M := M) W σp
        (smoothOrthoFrame (I := I) g x) x from rfl,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
          ![(smoothOrthoFrame (I := I) g x a x : E), (smoothOrthoFrame (I := I) g x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g x a x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g x b x : E)) v) : Fin 4 → E) (σp i)) =
      pairFeedScalarCLM (I := I) (M := M) 0 x (W x) ![]
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) *
        pairFeedScalarCLM (I := I) (M := M) 2 x
          (tensorRank4PermuteCLM (I := I) (M := M) x σp G) v
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) := by
    intro a b
    rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsummand a b))]
  rw [double_frame_bilin_trace_chartα (I := I) g α hxbase
    (pairFeedScalarCLM (I := I) (M := M) 0 x (W x) ![])
    (pairFeedScalarCLM (I := I) (M := M) 2 x (tensorRank4PermuteCLM (I := I) (M := M) x σp G) v)
    (fun a => smoothOrthoFrame (I := I) g x a x) hBf_on]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x m n * t) ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x k l * t) ?_
  rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma curvatureRefoldMonomialBiContrFibAppY_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯)
    (α : M) (σc : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel
        (curvatureActionMonomialTrace (I := I) (M := M)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1 (Y p.1))
        ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
          (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)])
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  classical
  have htuple : ∀ (y : M) (n l : Fin (Module.finrank ℝ E)) (j : Fin 4),
      (Fin.cons ((chartBasisVecFiber (I := I) α n y : E))
        (Fin.cons ((chartBasisVecFiber (I := I) α l y : E))
          ![(chartBasisVecFiber (I := I) α (σc 0) y : E),
            (chartBasisVecFiber (I := I) α (σc 1) y : E)]) : Fin 4 → E) j =
      ((chartBasisVecFiber (I := I) α
        ((Fin.cons n (Fin.cons l ![σc 0, σc 1]) : Fin 4 → Fin (Module.finrank ℝ E)) j)
        y : E)) := by
    intro y n l j
    fin_cases j <;> rfl
  have hYtuple : ∀ w : Fin 4 → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (𝕜 := ℝ) (Y p.1)
          (fun i => (chartBasisVecFiber (I := I) α (w i) p.1 : E)))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro w p₀ hp₀
    have hYon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SSpace 4 I z) p.1 (Y p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 4, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α (w i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α (w i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    exact TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 4
      (fun b : M => Y b) (hYon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α (w i) b) hv
  have hWpair : ∀ m k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (𝕜 := ℝ) (W p.1)
          ![(chartBasisVecFiber (I := I) α m p.1 : E),
            (chartBasisVecFiber (I := I) α k p.1 : E)])
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro m k p₀ hp₀
    have hWon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1 (W p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (hW.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 2, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α
            ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α
        ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 2
      (fun b : M => W b) (hWon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α
        ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) b) hv
    refine happly.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ m, ∑ n, chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) α p.1 m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) α p.1 k l *
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W p.1)
              ![(chartBasisVecFiber (I := I) α m p.1 : E),
                (chartBasisVecFiber (I := I) α k p.1 : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ) (Y p.1)
              (fun i => (Fin.cons ((chartBasisVecFiber (I := I) α n p.1 : E))
                (Fin.cons ((chartBasisVecFiber (I := I) α l p.1 : E))
                  ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)]) : Fin 4 → E)
                (σp i)))))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    refine contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T 0
      hδ hδZ α m n).mul ?_
    refine contMDiffOn_finset_sum (fun k _ => contMDiffOn_finset_sum (fun l _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T 0
      hδ hδZ α k l).mul ?_
    refine (hWpair m k).mul ?_
    refine (hYtuple (fun i => (Fin.cons n (Fin.cons l ![σc 0, σc 1]) :
      Fin 4 → Fin (Module.finrank ℝ E)) (σp i))).congr (fun p _ => ?_)
    congr 1
    funext i
    exact htuple p.1 n l (σp i)
  refine hcomb.congr (fun p hp => ?_)
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hp.1
  rw [curvatureRefoldMonomialBiContrFib_toModel_chartα (I := I) (M := M)
    (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp α hxbase]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma curvatureRefoldMonomialBiContrFibAppY_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) p.1
        (curvatureActionMonomialTrace (I := I) (M := M)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun s => realizedFam (I := I) g₀ T 0 hδ hδZ s with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ) with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σc : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, curvatureActionMonomialTrace (I := I) (M := M)
            (gfam p.2) W σp p.1 (Y p.1)⟩).2 σc)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σc
    have hscal := curvatureRefoldMonomialBiContrFibAppY_chartCoord_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ W hW σp Y α σc
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, curvatureActionMonomialTrace (I := I) (M := M)
            (gfam q.2) W σp q.1 (Y q.1)⟩).2 σc =
          Tensor0SSpace.toModel (curvatureActionMonomialTrace (I := I) (M := M)
              (gfam q.2) W σp q.1 (Y q.1))
            ![(chartBasisVecFiber (I := I) α (σc 0) q.1 : E),
              (chartBasisVecFiber (I := I) α (σc 1) q.1 : E)] := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1, curvatureActionMonomialTrace (I := I) (M := M)
          (gfam q.2) W σp q.1 (Y q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) (curvatureActionMonomialTrace (I := I) (M := M)
            (gfam q.2) W σp q.1 (Y q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1
        hqbase
        (curvatureActionMonomialTrace (I := I) (M := M) (gfam q.2) W σp q.1 (Y q.1))
        (fun j => (chartModelBasis E) (σc j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      change Tensor0SSpace.toModel (curvatureActionMonomialTrace (I := I) (M := M)
          (gfam q.2) W σp q.1 (Y q.1))
          (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σc j))) = _
      congr 1
      funext j
      fin_cases j <;> rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σc : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, curvatureActionMonomialTrace (I := I) (M := M)
          (gfam p.2) W σp p.1 (Y p.1)⟩).2 σc)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σc => hcoordEach σc)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, curvatureActionMonomialTrace (I := I) (M := M)
        (gfam p.2) W σp p.1 (Y p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, curvatureActionMonomialTrace (I := I) (M := M)
          (gfam p₀.2) W σp p₀.1 (Y p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

omit [BoundarylessManifold I M] in
theorem curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W hW σp).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => curvatureActionMonomialTrace (I := I) (M := M)
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun Y => curvatureRefoldMonomialBiContrFibAppY_realizedFam_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ W hW σp Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [curvatureRefoldMonomialCoeffField_toSection]
  rfl


omit [BoundarylessManifold I M] in
theorem riemannPalatiniRefoldC2Family_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB)
      (δ := δ) (δ' := δ) := by
  classical
  have hmono : ∀ σp : Equiv.Perm (Fin 4),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    fun σp => curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ
      (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp
  have hker : ∀ q : Fin 4 → Equiv.Perm (Fin 4),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((curvatureActionKernelCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
            (q 0) (q 1) (q 2) (q 3)).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro q
    have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hmono (q 0)) (hmono (q 1))
    have hsub1 := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hadd (hmono (q 2))
    have hsub2 := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hsub1 (hmono (q 3))
    have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hsub2
    refine hhalf.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    rw [curvatureActionKernelCoeffField, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContMDiffSection.coe_add, Pi.add_apply]
  have hsum := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hker qA) (hker qB)
  have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hsum
  have hfam := jointTotalSpaceRS_smulFun_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) (f := fun t => t) contDiff_id _ hhalf
  refine hfam.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [riemannPalatiniRefoldC2Family, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContMDiffSection.coe_add, Pi.add_apply]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
