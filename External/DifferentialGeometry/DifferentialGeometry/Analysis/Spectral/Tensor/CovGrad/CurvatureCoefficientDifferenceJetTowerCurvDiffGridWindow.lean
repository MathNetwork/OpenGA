import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
def ricciEndomorphismField (g : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricEndoRaisedFib (I := I) g x
  contMDiff_toFun := ricEndoRaisedFib_contMDiff (I := I) g

set_option backward.isDefEq.respectTransparency false in
def ricEndoBackgroundDifferenceField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ricciEndomorphismField (I := I) (M := M) g₁ - ricciEndomorphismField (I := I) (M := M) g₀

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma ricEndoBackgroundDifferenceField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x =
      ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x := by
  rw [ricEndoBackgroundDifferenceField]
  rw [show ((ricciEndomorphismField (I := I) (M := M) g₁ -
        ricciEndomorphismField (I := I) (M := M) g₀) x) =
      ricciEndomorphismField (I := I) (M := M) g₁ x -
        ricciEndomorphismField (I := I) (M := M) g₀ x from by
    rw [ContMDiffSection.coe_sub]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma curvCoeffSlot_zero_backgroundDifference_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0 =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x) =
      (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0).toSection x -
        (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ 0 x D from rfl]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₀ 0 x D from rfl]
  rw [ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) D from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma curvCoeffSlot_one_backgroundDifference_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1 =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x) =
      (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1).toSection x -
        (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ 1 x D from rfl]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₀ 1 x D from rfl]
  rw [ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
        (Equiv.swap (0 : Fin 2) 1)).toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) D
      from rfl]
  rw [reindexCoeffFibGen_apply]
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotInsertEndoCc_toSection,
    slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        Function.update (fun i : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
          ((ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x)
            (m ((Equiv.swap (0 : Fin 2) 1) 0))) ((Equiv.swap (0 : Fin 2) 1) i)) =
      Function.update m 1
        ((ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) (m 1)) from by
    funext j
    fin_cases j <;>
      simp [Function.update]]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciArmOrder0CurvCoeff_backgroundDifference_decomp
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) +
        reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
          (Equiv.swap (0 : Fin 2) 1) := by
  rw [← curvCoeffSlot_one_backgroundDifference_eq (I := I) (M := M) g₀ g₁,
    ← curvCoeffSlot_zero_backgroundDifference_eq (I := I) (M := M) g₀ g₁,
    ricciArmOrder0CurvCoeff, ricciArmOrder0CurvCoeff]
  abel

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem curvDiffGrid_productTerm_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max R (max C 1))) ^ (7 * i) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max R (max C 1)) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_trans (le_max_right R _) (le_max_right Λ _))
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hR_le : R ≤ Mbar := le_trans (le_max_left R _) (le_max_right Λ _)
  have hC_le : C ≤ Mbar :=
    le_trans (le_trans (le_max_left C 1) (le_max_right R _)) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e2 : R ^ 2 ≤ Mbar ^ 2 := pow_le_pow_left₀ hR hR_le 2
          have e3 : Mbar ^ (2 * i) * Mbar ^ 2 ≤ Mbar ^ (7 * i) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hMbar1 (by omega)
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 := e4
            _ ≤ Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hexp2_nn : 0 ≤ 2 * (e m : ℝ) / i := by positivity
      have hexp2_le : 2 * (e m : ℝ) / i ≤ 2 := by
        rw [mul_div_assoc]; nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hRpow : R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 : ℕ) := by
        calc R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 * (e m : ℝ) / i) :=
              Real.rpow_le_rpow hR hR_le hexp2_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp2_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
          Mbar ^ (5 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        have h2 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
            Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) :=
          mul_le_mul h1 hRpow (Real.rpow_nonneg hR _) (by positivity)
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)
            ≤ Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) := h2
          _ = Mbar ^ (5 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) := by
        apply mul_nonneg (mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)) (Real.rpow_nonneg hR _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM5_one : (1 : ℝ) ≤ Mbar ^ (5 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hM5_one hidiv
        _ = (Mbar ^ (5 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
        _ = Mbar ^ (5 * i) := by rw [← pow_mul]
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * Mbar ^ (5 * i) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * Mbar ^ (5 * i) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) := e4
            _ = Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5

theorem curvDiffGrid_integral_ballUniform_window
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a + 2 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K i := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max R (max (Cgn k) 1))) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_trans (le_max_right R _) (le_max_right Lam _)))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  · intro P hPball i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      refine ⟨?_, ?_⟩
      · rw [hgrid0]; exact MeasureTheory.integrable_const 1
      · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, ← hvol]
        exact le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R := hPball i (by omega)
      have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
        intro x
        have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
            _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
          have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
          have hsl := Finset.single_le_sum
            (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
            (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
          simpa using hsl
        have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
          refine le_trans (hCemb P x) ?_
          rw [hLam2]
          calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
        exact le_trans hsingle hchain
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hGNP : ∀ j : ℕ, 0 < j → j < i →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
            Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)) := by
        intro j hj0 hji
        have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
        have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
          rw [hCgn]; simp only [dif_pos hi1]
        rw [hchoose] at hb
        refine le_trans hb ?_
        have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
            (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
          (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hNi (by positivity))
          (mul_nonneg (hCgn_nn i) (Real.rpow_nonneg hLam_nn _))
      have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
          MeasureTheory.Integrable (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Gfun i := by
        intro n hn e he
        have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
        have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hres := curvDiffGrid_productTerm_integral_le (I := I) (M := M) g₀ P hR i hi1 hLam_nn hΛsup
          hNi (hCgn_nn i) hGNP n hn_le e hsum_e
        simpa only [hGfun] using hres
      have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.integrable_finset_sum
        intro n hn
        apply MeasureTheory.integrable_finset_sum
        intro e he
        exact (hPT n hn e he).1
      refine ⟨hgrid_int, ?_⟩
      rw [MeasureTheory.integral_finset_sum _
        (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
      have hinner : ∀ n ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        intro n hn
        exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact (hPT n hn e he).2
      have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i =
          (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) * Gfun i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hle1 ?_
      rw [heq2]
      exact le_add_of_nonneg_right hvol_nn

def tGridCount (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ)

lemma tGridCount_nonneg (j : ℕ) : 0 ≤ tGridCount j :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

lemma prodTerm_le_antidiagonalTupleGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (k n : ℕ) (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    (∏ m : Fin n, b (e m)) ≤ Combinatorics.antidiagonalTupleGrid b k := by
  rw [Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k, ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

lemma antidiagonalTupleGrid_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j k : ℕ) :
    Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k ≤
      (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
  classical
  have hpair : ∀ n ∈ Finset.range (j + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n j,
      ∀ n' ∈ Finset.range (k + 1), ∀ e' ∈ Finset.Nat.antidiagonalTuple n' k,
      (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) ≤
        Combinatorics.antidiagonalTupleGrid b (j + k) := by
    intro n hn e he n' hn' e' he'
    have happend : (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) =
        ∏ m : Fin (n + n'), b (Fin.append e e' m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e e' ∈ Finset.Nat.antidiagonalTuple (n + n') (j + k) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at he he' ⊢
      rw [Fin.sum_univ_add]
      have h1 : (∑ m : Fin n, Fin.append e e' (Fin.castAdd n' m)) = j := by
        rw [← he]
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
      have h2 : (∑ m : Fin n', Fin.append e e' (Fin.natAdd n m)) = k := by
        rw [← he']
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
      rw [h1, h2]
    have hnn' : n + n' < j + k + 1 := by
      rw [Finset.mem_range] at hn hn'
      omega
    exact prodTerm_le_antidiagonalTupleGrid b hb (j + k) (n + n') hnn' _ hmem
  calc Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k
      = ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ((∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Combinatorics.antidiagonalTupleGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun e he => ?_))
        calc (∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                ((∏ m : Fin n, b (e m)) * ∏ m : Fin n', b (e' m)) := by
              rw [Combinatorics.antidiagonalTupleGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                Combinatorics.antidiagonalTupleGrid b (j + k) := by
              refine Finset.sum_le_sum (fun n' hn' => Finset.sum_le_sum (fun e' he' => ?_))
              exact hpair n hn e he n' hn' e' he'
          _ = tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k) := by
              rw [tGridCount, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun n' _ => by
                rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ) *
          (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
        rw [show (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) =
            tGridCount j * (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) from by
          ring]
        rw [show tGridCount j = ∑ n ∈ Finset.range (j + 1),
            ((Finset.Nat.antidiagonalTuple n j).card : ℝ) from rfl]
        rw [Finset.sum_mul]

def tWindow (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k

lemma tWindow_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) : 0 ≤ tWindow b i :=
  Finset.sum_nonneg (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

lemma antidiagonalTupleGrid_le_tWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {k i : ℕ} (hk : k < i + 3) :
    Combinatorics.antidiagonalTupleGrid b k ≤ tWindow b i :=
  Finset.single_le_sum (fun k' _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr hk)

lemma tWindow_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {i i' : ℕ} (h : i ≤ i') :
    tWindow b i ≤ tWindow b i' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (show i + 3 ≤ i' + 3 by omega)) ?_
  intro k _ _
  exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k

lemma one_le_tWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) : 1 ≤ tWindow b i := by
  rw [← Combinatorics.antidiagonalTupleGrid_zero b]
  exact antidiagonalTupleGrid_le_tWindow b hb (by omega)

def tWindowMulConst (j l : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 3), tGridCount k * tGridCount l

lemma tWindowMulConst_nonneg (j l : ℕ) : 0 ≤ tWindowMulConst j l :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (tGridCount_nonneg k) (tGridCount_nonneg l))

lemma tWindow_mul_antidiagonalTupleGrid_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j l : ℕ) :
    tWindow b j * Combinatorics.antidiagonalTupleGrid b l ≤
      tWindowMulConst j l * tWindow b (j + l) := by
  calc tWindow b j * Combinatorics.antidiagonalTupleGrid b l
      = ∑ k ∈ Finset.range (j + 3),
          Combinatorics.antidiagonalTupleGrid b k * Combinatorics.antidiagonalTupleGrid b l := by
        rw [tWindow, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (j + 3), (tGridCount k * tGridCount l) * tWindow b (j + l) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k l) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (tGridCount_nonneg k) (tGridCount_nonneg l))
        refine antidiagonalTupleGrid_le_tWindow b hb ?_
        rw [Finset.mem_range] at hk
        omega
    _ = tWindowMulConst j l * tWindow b (j + l) := by
        rw [tWindowMulConst, ← Finset.sum_mul]

section NormedGridIdentities

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tWindow_eq_tripleSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (i : ℕ) :
    tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma antidiagonalTupleGrid_eq_doubleSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (l : ℕ) :
    Combinatorics.antidiagonalTupleGrid
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l =
      ∑ n ∈ Finset.range (l + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n l,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGrad_fiberNormSq_bound (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i S).toSection x) ≤ c i := by
  have h : ∀ i : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i S).toSection x) ≤ c := fun i =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + i)
      (iteratedCovGrad (I := I) g₀ r s i S)
  choose c hc0 hcb using h
  exact ⟨c, hc0, hcb⟩

end NormedGridIdentities

end Connection
end Integral
end DifferentialGeometry
end
