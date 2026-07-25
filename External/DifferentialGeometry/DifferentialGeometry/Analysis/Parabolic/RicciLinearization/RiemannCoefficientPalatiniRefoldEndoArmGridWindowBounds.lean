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
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindowClosureAdditivity


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

lemma bdICG_succ_cometricDT_zero (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdRfns_zero_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((0 : SmoothCcTensor g₀ r s).toSection x) = 0 := by
  rw [show ((0 : SmoothCcTensor g₀ r s).toSection x) = (0 : TensorRSSpace r s I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ r s x

private theorem bdCometricCastG0_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
            ((iteratedCovGrad (I := I) g₀ 3 1 j
              (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 1) := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 3 1
    (cometricDoubleTraceField (I := I) g₀ 1)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => 2 * cfix 0 +
      2 * (diagonalGridGrowthFactor (E := E) j * (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l)),
    fun j => by
      have h1 := hcfix_nn 0
      have h2 : 0 ≤ diagonalGridGrowthFactor (E := E) j *
          (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) j) (mul_nonneg (hcfix_nn 0)
          (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hCD_nn l)))
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hW1 : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (j + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by linarith
  rw [cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) (M := M) g₀ g₁]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 3 1 j
    (cometricDoubleTraceField (I := I) g₀ 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
    x) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤ cfix 0 := by
    match j with
    | 0 => exact hcfix 0 x
    | (m + 1) =>
        rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ 1 m]
        rw [bdRfns_zero_toSection]
        exact hcfix_nn 0
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) j * (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ j 3 3 1
      (cometricDoubleTraceField (I := I) g₀ 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) = 0 := by
      intro i' _ hi'0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
      rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ 1 m]
      rw [bdRfns_zero_toSection, zero_mul]
    have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + 0) x
            ((iteratedCovGrad (I := I) g₀ 3 1 0
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - 0),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
      intro i' hi' hi'0
      exact hzero i' hi' hi'0
    rw [hsum_eq]
    have hslot : (∑ l ∈ Finset.range (j + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) ≤
        (∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
        rw [show j + 1 - 0 = j + 1 from rfl, Finset.sum_mul]
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_range] at hl
        refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x) ?_
        have h2 := hCD g₁ P htie hδ_le hδ0 hbound l x
        calc (Module.finrank ℝ E : ℝ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
            ≤ fr ^ 2 * (CD l * ∑ n ∈ Finset.range (l + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n l,
                  ∏ m : Fin n, b (e m)) := by
              rw [← hfr_def]
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (fr ^ 2 * CD l) * Combinatorics.antidiagonalTupleGrid b l := by
              rw [Combinatorics.antidiagonalTupleGrid]
              ring
          _ ≤ (fr ^ 2 * CD l) * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (by positivity) (hCD_nn l))
              exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
    have hfix0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 3 1 0
          (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤ cfix 0 := hcfix 0 x
    have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (j + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + l) x _
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hfix0 hslot hsum_nn (hcfix_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
    rw [← mul_assoc, ← mul_assoc]
    rw [mul_assoc (diagonalGridGrowthFactor (E := E) j) (cfix 0)]
  have hA' : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤
      cfix 0 * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    refine le_trans hA ?_
    nlinarith [hcfix_nn 0]
  have hB_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) j *
      (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) :=
    mul_nonneg (appCcGdiag_nonneg (E := E) j) (mul_nonneg (hcfix_nn 0)
      (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hCD_nn l)))
  nlinarith [hA', hB, hW_nn, hcfix_nn 0]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdConnDiffSection_eq_cometricRaise (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [bdInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [bdConnDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] in
lemma bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [bdConnDiffSection_eq_cometricRaise]

private theorem bdCA_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (bdCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  refine ⟨CA, hCA_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j
        (bdCA (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 3 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
            (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) := by
    rw [bdCA]
    exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)) j x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 3 j
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 3 j
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 3) 2) (connDiffLoweredCc (I := I) g₀ g₁) j x
  rw [h1, h2, bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ j x]
  refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound j x) ?_
  rw [show Combinatorics.antidiagonalTupleGridWindow b (j + 2) =
      ∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k from rfl]

private theorem bdOmega_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 1 l
              (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 1) := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ := bdCometricCastG0_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨cxi, hcxi_nn, hcxi⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 0 3
    (bdXiFix (I := I) (M := M) g₀ g_bg)
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l',
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCg_nn i')
        (Finset.sum_nonneg fun l' _ => hcxi_nn l')), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 1) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 1)
  rw [bdOmega]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 0 3 1
    (cometricDoubleTraceCastG0 (I := I) g₀ g₁)
    (bdXiFix (I := I) (M := M) g₀ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 1 i'
            (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x) ≤
      (Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l') *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
        ((iteratedCovGrad (I := I) g₀ 3 1 i'
          (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
        Cg i' * Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
      refine le_trans (hCg g₁ P htie hδ_le hδ0 hbound i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCg_nn i')
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (l + 1 - i'), cxi l' :=
      Finset.sum_le_sum fun l' _ => hcxi l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x) *
          ∑ l' ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 3 l'
                (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x)
        ≤ (Cg i' * Combinatorics.antidiagonalTupleGridWindow b (l + 1)) *
            ∑ l' ∈ Finset.range (l + 1 - i'), cxi l' :=
          mul_le_mul hA1 hA2 hsum_nn (mul_nonneg (hCg_nn i') hW_nn)
      _ = (Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l') *
            Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

private theorem bdAlphaA_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨Cω, hCω_nn, hCω⟩ := bdOmega_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => Cω (i + 1), fun i => hCω_nn (i + 1), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  rw [bdAlphaA]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) i x]
  rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x]
  exact hCω g₁ P htie hδ_le hδ0 hbound (i + 1) x

private theorem bdAlphaB_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := bdCA_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cω, hCω_nn, hCω⟩ := bdOmega_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l',
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCA_nn i')
        (Finset.sum_nonneg fun l' _ => mul_nonneg (hCω_nn l')
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  rw [bdAlphaB]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 0 1 2
    (bdCA (I := I) (M := M) g₀ g₁)
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 1 2 i'
            (bdCA (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l' ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 1 l'
              (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      (CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l') *
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i'
          (bdCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) :=
      hCA g₁ P htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l' ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 1 l'
            (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (i + 1 - i'),
          Cω l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 1) :=
      Finset.sum_le_sum fun l' _ => hCω g₁ P htie hδ_le hδ0 hbound l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 1 l'
            (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (1 + l') x _
    have hA1_rhs_nn : (0 : ℝ) ≤ CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) :=
      mul_nonneg (hCA_nn i') (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 2))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l') *
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) =
        ∑ l' ∈ Finset.range (i + 1 - i'),
          (CA i' * (Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l')) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l' hl' => ?_
    rw [Finset.mem_range] at hl'
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
        Combinatorics.antidiagonalTupleGridWindow b (l' + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
          Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1) := by
      have h := Combinatorics.antidiagonalTupleGridWindow_mul_le b hb (i' + 1) l'
      rw [show i' + 1 + 1 = i' + 2 from rfl] at h
      exact h
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1) ≤
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
      Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    calc CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
          (Cω l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 1))
        = (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
            Combinatorics.antidiagonalTupleGridWindow b (l' + 1)) := by ring
      _ ≤ (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
            Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCA_nn i') (hCω_nn l')
      _ ≤ (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (hCA_nn i') (hCω_nn l'))
          refine mul_le_mul_of_nonneg_left hmono ?_
          exact Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _
      _ = (CA i' * (Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l')) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

private theorem bdWEndoInsertDiff_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CAa, hCAa_nn, hCAa⟩ := bdAlphaA_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CAb, hCAb_nn, hCAb⟩ := bdAlphaB_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => 2 * CAa i + 2 * CAb i,
    fun i => by have h1 := hCAa_nn i; have h2 := hCAb_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  rw [bdWEndoInsert_sub_eq_cometricRaise (I := I) (M := M) g₀ g₁ g_bg]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) i x]
  rw [bdAlpha]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 2 i
    (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)
    (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have h1 := hCAa g₁ P htie hδ_le hδ0 hbound i x
  have h2 := hCAb g₁ P htie hδ_le hδ0 hbound i x
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  nlinarith [h1, h2, hW_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i
        (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i
        (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem bdDLb_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D
      = deTurckLieDLbFib (I := I) g₁ g_bg x D from rfl]
  rw [deTurckLieDLbFib_toModel (I := I) g₁ g_bg x D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x) D from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x) D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorRS_domDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)) from by
    rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
    ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (deTurckLieWEndo (I := I) g₁ g_bg x
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k))
      = Function.update m 1 (deTurckLieWEndo (I := I) g₁ g_bg x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdSlotInsertEndoCc_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s A - endoSlotZeroCcTensor (I := I) (M := M) g₀ s B =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A - B) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by rw [ContMDiffSection.coe_sub]; rfl]
  rw [slotInsertEndoFib_sub_left]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdReindexSwap_sub (g₀ : SmoothRiemannianMetric I M)
    (X Y : SmoothCcTensor g₀ 2 2) :
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1) -
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1) =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) (X - Y))
        (Equiv.swap (0 : Fin 2) 1) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1) -
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1)).toSection x) =
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1)).toSection x -
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  have hpt : ∀ (Z : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Z)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Z.toSection x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))))
        (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) := by
    intro Z
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Z)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              Z).toSection x) D from rfl]
    rw [reindexCoeffFibGen_apply]
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          Z).toSection x) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorRS_domDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            (Z.toSection x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show Tensor0SSpace.toModel
      (((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
          (Equiv.swap (0 : Fin 2) 1)).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m from by
    rw [show (((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
          (Equiv.swap (0 : Fin 2) 1)).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) -
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) from rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]]
  rw [hpt X, hpt Y, hpt (X - Y)]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (X - Y).toSection x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from X.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) -
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Y.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) from by
    rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

private def bdWEndoSecDiff (g₁ g_bg g₀' : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg -
    deTurckLieWEndoSection (I := I) (M := M) g₁ g₀'

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem bdDLbDiff_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [bdDLb_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg,
    bdDLb_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g₀]
  rw [show (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1))
      - (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        - endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀))
      + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)
        - reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)) from by abel]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rw [bdReindexSwap_sub (I := I) (M := M) g₀
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀))]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdSlotInsertZero_bdWEndoSecDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀) =
      deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀ := by
  rw [deTurckLieWEndoInsert, deTurckLieWEndoInsert]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 0
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rfl

theorem bdEndoArmDiff_pointwise_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CW, hCW_nn, hCW⟩ := bdWEndoInsertDiff_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 2 * (fr * CW i) + 2 * (fr * CW i),
    fun i => by have h := mul_nonneg hfr_nn (hCW_nn i); linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  have hbase : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x) ≤
      CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    rw [bdSlotInsertZero_bdWEndoSecDiff (I := I) (M := M) g₀ g₁ g_bg]
    exact hCW g₁ P htie hδ_le hδ0 hbound i x
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x) ≤
      fr * CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
      (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀) i x
    rw [pow_one] at h
    refine le_trans h ?_
    rw [← hfr_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left hbase hfr_nn
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
          (Equiv.swap (0 : Fin 2) 1))).toSection x) ≤
      fr * CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    have heq := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)) i x
    rw [heq]
    exact hA
  rw [bdDLbDiff_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 2 2 i _ _ x) ?_
  nlinarith [hA, hB,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
          (Equiv.swap (0 : Fin 2) 1))).toSection x)]

theorem bdL2_tameEnvelope_of_gridWindow (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kg : ℕ → ℝ, (∀ k, 0 ≤ Kg k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ) (C : ℝ), 0 ≤ C → ∀ (V : SmoothCcTensor g₀ 2 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i V).toSection x) ≤
          C * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2)) →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i V‖ ^ 2 ≤
          (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kg, hKg_nn, ?_⟩
  intro P hPball i C hC V hpt
  have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V).toSection x) ≤
        C * ∑ k ∈ Finset.range (i + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
    intro x
    refine le_trans (hpt x) (le_of_eq ?_)
    congr 1
  have hF_int : MeasureTheory.Integrable
      (fun x => C * ∑ k ∈ Finset.range (i + 2),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum _
      (fun k hk => (hKg P hPball k).1)).const_mul C
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i V)
    (fun x => C * ∑ k ∈ Finset.range (i + 2),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
    hF_int hpt'
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
  have hsum_le : ∑ k ∈ Finset.range (i + 2),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (i + 2), Kg k) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hKg P hPball k).2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
    have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hk
      omega
    linarith
  calc C * ∑ k ∈ Finset.range (i + 2),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      ≤ C * ((∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_le hC
    _ = (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
