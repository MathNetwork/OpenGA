import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
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

section MixedSharpRicci

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (ricciTensor (I := I) g₁ x v).toLinearMap +
              (ricciTensor (I := I) g₁ x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) g₁ x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricMixedSharpEndoFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v =
      metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap := by
  rw [ricMixedSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricMixedSharpEndoFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) g₁ b)) :=
      ricciTensor_contMDiff (I := I) g₁
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) g₁ b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (Y x))
  rw [ricMixedSharpEndoFib_apply]

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x
  contMDiff_toFun := ricMixedSharpEndoFib_contMDiff (I := I) (M := M) g₀ g₁

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma ricMixedSharpEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricMixedSharpEndoField (I := I) (M := M) g₀ g₁ x =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ricEndoRaisedFib (I := I) g₁ x v =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
        metricComparisonDiffEndo (I := I) g₀ g₁ x
          (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) := by
  rw [gInvDiffRaisedEndo_apply]
  have hcollapse : ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
      (inverseMetricSharpFib (I := I) g₁ x
          (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) -
        ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) =
      inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) := by
    abel
  rw [hcollapse]
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x
    (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)]
  have hβ : (g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap =
      (ricciTensor (I := I) g₁ x v).toLinearMap := by
    ext w
    rw [show ((g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap) w =
        g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) w from rfl]
    rw [ricMixedSharpEndoFib_apply]
    exact inner_metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap w
  rw [hβ, ricEndoRaisedFib_apply]
  exact (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_eq_connectionMetricSharp
    (I := I) g₁ x (ricciTensor (I := I) g₁ x v).toLinearMap).symm

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)) +
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)) +
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection) x) =
      ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x) +
      (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x from by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
    rfl]
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoRaisedFib (I := I) g₀ x) A from rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
          (metricComparisonDiffEndo (I := I) g₀ g₁ x) A) from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval]
  rw [Function.update_self, Function.update_idem]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]
  rw [ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised (I := I) (M := M) g₀ g₁ x (m 0)]
  rw [ContinuousMultilinearMap.map_update_add]
  ring

end MixedSharpRicci

section RiemannLoweredDifference

section NormedRiemannLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

set_option backward.isDefEq.respectTransparency false

def riemannLoweredCovec (gm gc : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hR : Continuous (fun m : Fin 4 → TangentSpace I x =>
            riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) :=
          (((riemannOp (LeviCivita (I := I) gc) x).continuous.comp
            (continuous_apply 0)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((gm.inner x).continuous.comp hR).clm_apply (continuous_apply 1) }
    : Tensor0SSpace 4 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma riemannLoweredCovec_apply (gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    riemannLoweredCovec (I := I) gm gc x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannLoweredScalar_global (gm gc : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) gc) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) gc) hY hp hq
  have hcongr : (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => gm.inner x (riemannSec (LeviCivita (I := I) gc) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) gc) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) gm
    ⟨fun b => riemannSec (LeviCivita (I := I) gc) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannLoweredScalar_contMDiffAt (gm gc : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (V0 x) (V2 x) (V3 x)) (V1 x)) x₀ := by
  have hglob := riemannLoweredScalar_global (I := I) (M := M) gm gc
    (Y := fun b => V0 b) (W := fun b => V1 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V0.contMDiff V1.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannLoweredCovec_section_contMDiff (gm gc : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (riemannLoweredCovec (I := I) gm gc x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (riemannLoweredCovec (I := I) gm gc x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y (σ 0) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 1) x)) x₀ :=
    riemannLoweredScalar_contMDiffAt (I := I) gm gc (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change gm.inner x (riemannOp (LeviCivita (I := I) gc) x
      (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 2))) (e₁.symmL ℝ x (b (σ 3))))
      (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

def riemannLoweredField (gm gc : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => riemannLoweredCovec (I := I) gm gc x,
    riemannLoweredCovec_section_contMDiff (I := I) gm gc⟩

def riemannLoweredCc (g₀ gm gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (riemannLoweredField (I := I) gm gc)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma riemannLoweredCc_unitModel (g₀ gm gc : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x =
      Tensor0SSpace.toModel (riemannLoweredCovec (I := I) gm gc x) := by
  rw [unitModel]
  rw [show (riemannLoweredCc (I := I) (M := M) g₀ gm gc).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (riemannLoweredField (I := I) gm gc x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma riemannLoweredCc_unitModel_apply (g₀ gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := by
  rw [riemannLoweredCc_unitModel]
  rfl

def riemannLoweredBackgroundDifference (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma riemannLoweredBackgroundDifference_unitModel_apply
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1) -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3)) (m 1) := by
  have hsub : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m -
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x m := by
    simp only [riemannLoweredBackgroundDifference, unitModel]
    rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x) =
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x -
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hsub, riemannLoweredCc_unitModel_apply, riemannLoweredCc_unitModel_apply]

end NormedRiemannLowering

section NormedSharpFlatSplitting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private instance tensor0SModelNormedSpaceCC {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interiorProduct_toModel_eval_pal (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_om_single_eq_cotangentToDual (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g0_inner_inverseMetricSharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToDual_eq_inner_sharp (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (ww : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om ww =
      g₀.inner x ww (inverseMetricSharpFib (I := I) g₀ x om) := by
  rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₀ x om ww]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x ww = ww from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma sharpFlatEndoCc_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma fullRaisedEndoField_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotInsertEndoCc_add_endo (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma endoCovariantDerivative_fullRaised_id_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply]
    rw [show metricComparisonEndo (I := I) g₀ g₀ y (Y y) = Y y from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x
      ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v) =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_slotInsert_fullRaised_id_eq_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact covGrad_slotInsert_fullRaised_id_eq_zero (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

end NormedSharpFlatSplitting

section NormedRaisedKoszulPointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_smul_pt (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rfns_smul_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rfns_neg_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := rfns_smul_pt (I := I) (M := M) g r s x (-1 : ℝ) v
  rw [neg_one_smul] at h
  rw [h]; norm_num

omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iteratedCovGrad_symmS_pointwise (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := by
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [htoSec]
  have hRB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := hswap
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [rfns_smul_pt, rfns_smul_pt]; ring
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by
        rw [hRB]; ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_koszulCovecCc_pointwise (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    rw [show symmSCovGrad3 (I := I) g₀ T =
        covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T) from rfl]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
      (ccTensor02Symm (I := I) g₀ T) x
    rw [hcomm]
    exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i + 1) x
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hkos, iteratedCovGrad_smul_pt, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, rfns_smul_pt]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    rfns_neg_pt (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iteratedCovGrad_raisedKoszul_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) (M := M) g₀ g₁ T htie]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) (M := M) g₀ T i x]
  exact rfns_iteratedCovGrad_koszulCovecCc_pointwise (I := I) (M := M) g₀ T i x

end NormedRaisedKoszulPointwise

section NormedConnectionDifferenceGrid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ S : ℕ → ℝ, (∀ l, 0 ≤ S l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S l * Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * CD l + 2 * cid,
    fun l => by have := hCD_nn l; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b l :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hsplit : sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo (I := I) (M := M) g₀ 0]
  have hsec : (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x := by
    rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      CD l * Combinatorics.antidiagonalTupleGrid b l :=
    hCD g₁ T htie hδ_le hδ0 hbound l x
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cid * Combinatorics.antidiagonalTupleGrid b l := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one]
        exact hcid x
    | (m + 1) =>
        rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ m]
        rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (m + 1))).toSection x) =
            (0 : TensorRSSpace 1 (1 + (m + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 1 (1 + (m + 1)) x]
        exact mul_nonneg hcid_nn
          (Combinatorics.antidiagonalTupleGrid_nonneg b hb (m + 1))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x)
      ≤ 2 * (CD l * Combinatorics.antidiagonalTupleGrid b l) +
          2 * (cid * Combinatorics.antidiagonalTupleGrid b l) := by
        have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        linarith
    _ = (2 * CD l + 2 * cid) * Combinatorics.antidiagonalTupleGrid b l := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_order_congr_ts (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

theorem rfns_iteratedCovGrad_connDiffSection_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
              (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) ∧
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
                (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc j * ∑ k ∈ Finset.range j,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j - k)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (j - k) T).toSection x) *
              Combinatorics.antidiagonalTupleGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (k + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ :=
    exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid (I := I) (M := M) g₀ hδ₀
  refine ⟨10 * S 0, mul_nonneg (by norm_num) (hS_nn 0), ?_⟩
  refine ⟨fun j => (j : ℝ) * diagonalGridGrowthFactor (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l),
    fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (appCcGdiag_nonneg (E := E) j))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun l _ => hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  constructor
  · rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁)).toSection x)
      ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    have hK := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie j x
    have hF : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ S 0 := by
      have h0 := hS g₁ T htie hδ_le hδ0 hbound 0 x
      rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h0
      exact h0
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x)) * S 0 :=
          mul_le_mul hK hF
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _)
            (mul_nonneg (by norm_num)
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (j + 1)) x _))
      _ = (10 * S 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) := by ring
  · have hid : iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) =
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
            (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁) +
          ∑ k ∈ Finset.range j,
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
              (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
      rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
      rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2
        (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
      rw [Finset.sum_range_succ' (fun k =>
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
          (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
      have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
          (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
            (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁) :=
        congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
          (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
            (raisedKoszul (I := I) g₀ g₁) j)
      rw [hf0]
      exact add_comm _ _
    have hsub : iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) =
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
      rw [hid]
      exact add_sub_cancel_left _ _
    rw [hsub]
    rw [SmoothCcTensor.toSection_sum_apply]
    refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1 (2 + j) x
      (Finset.range j) (fun k =>
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ?_
    rw [Finset.card_range]
    have hstep : (∑ k ∈ Finset.range j,
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
              (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ≤
        ∑ k ∈ Finset.range j,
          diagonalGridGrowthFactor (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j - k)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (j - k) T).toSection x) *
              Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk_lt : k < j := Finset.mem_range.mp hk
      rw [appCcRS_toSection (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
        (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + (k + 1))
        (2 + j) x
        ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
          (k + 1)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ?_
      have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + j) x
          ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
            (k + 1)).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j * (10 * b (j - k)) := by
        have hE3 := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 1 2
          (raisedKoszul (I := I) g₀ g₁) j (k + 1) 0 (by omega : k + 1 ≤ j) x
        rw [rfns_iteratedCovGrad_order_congr_ts (I := I) (M := M) g₀ 1 2
          (show (j - (k + 1)) + 0 = j - (k + 1) from by omega)
          (raisedKoszul (I := I) g₀ g₁) x] at hE3
        refine le_trans hE3 (mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j))
        have hK := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie
          (j - (k + 1)) x
        rw [rfns_iteratedCovGrad_order_congr_ts (I := I) (M := M) g₀ 0 2
          (show (j - (k + 1)) + 1 = j - k from by omega) T x] at hK
        exact hK
      have hF : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S (k + 1) * Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        hS g₁ T htie hδ_le hδ0 hbound (k + 1) x
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
      have hSk_le : S (k + 1) ≤ ∑ l ∈ Finset.range (j + 1), S l :=
        Finset.single_le_sum (f := S) (fun l _ => hS_nn l)
          (Finset.mem_range.mpr (by omega : k + 1 < j + 1))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + j) x
              ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
                (k + 1)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
          ≤ (diagonalGridGrowthFactor (E := E) j * (10 * b (j - k))) *
              (S (k + 1) * Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
            refine mul_le_mul hPsi hF
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + (k + 1)) x _) ?_
            have h10 : (0 : ℝ) ≤ 10 * b (j - k) := by
              have := hb (j - k); linarith
            exact mul_nonneg (appCcGdiag_nonneg (E := E) j) h10
        _ ≤ (diagonalGridGrowthFactor (E := E) j * (10 * b (j - k))) *
              ((∑ l ∈ Finset.range (j + 1), S l) *
                Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hSk_le hgrid_nn) ?_
            have h10 : (0 : ℝ) ≤ 10 * b (j - k) := by
              have := hb (j - k); linarith
            exact mul_nonneg (appCcGdiag_nonneg (E := E) j) h10
        _ = diagonalGridGrowthFactor (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l) *
              (b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg j)) (le_of_eq ?_)
    rw [← Finset.mul_sum]
    ring

def connDiffArmFieldPt (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff)⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffArmFieldPt_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x = PDE.DeTurck.connDiff (I := I) g₁ g₀ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma connDiffSection_eq_armSlotEndoCc_zero (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 0
          (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)).toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 0 x (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      connDiffPairing (I := I) g₁ g₀ x om from rfl]
  change connDiffPairing (I := I) g₁ g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma armSlotEndoCc_one_eq_reindex_slotExtend (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 1 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
          (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) =
        bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 3 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRS_domDomCongr (finRotate 3).symm
          ((slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
        (fun i => w ((finRotate 3).symm i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (finRotate 3).symm
      ((slotExtend (I := I) (M := M) g₀ 1 2
        (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
      (fun i => w ((finRotate 3).symm i)) =
      Tensor0SSpace.toModel
        (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
        (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')) from rfl]
    rw [show (fun i => w ((finRotate 3).symm i)) =
        Fin.cons (w ((finRotate 3).symm 0))
          (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')))
      (v0 := w ((finRotate 3).symm 0))
      (vs := Matrix.vecTail (fun i => w ((finRotate 3).symm i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 0 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i)))]
    rw [slotInsertEndoFib_apply_eval]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [Function.update_self]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w ((finRotate 3).symm 0))
          (fun _ : Fin 1 => (show E from
            Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D') (v0 := w ((finRotate 3).symm 0))
      (vs := fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w ((finRotate 3).symm 0))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hτ0, hτ1, hτ2]
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show (Function.update (Matrix.vecTail w) 0
            (Arm x (w 0) (Matrix.vecTail w 0)) (0 : Fin 2)) =
          Arm x (w 0) (Matrix.vecTail w 0) from Function.update_self _ _ _]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j2 => j2.elim0) j
      rw [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

lemma rfns_iteratedCovGrad_armSlotPass_connDiffArm_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) j x]
  rw [armSlotEndoCc_one_eq_reindex_slotExtend (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)) j x) ?_
  rw [← connDiffSection_eq_armSlotEndoCc_zero (I := I) (M := M) g₀ g₁]

theorem exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CA : ℕ → ℝ, (∀ j, 0 ≤ CA j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          CA j * ∑ k ∈ Finset.range (j + 2),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) k := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j *
      ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l,
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => hS_nn l)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set G : ℝ := ∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k with hG_def
  clear_value G
  have hG_nn : 0 ≤ G := by
    rw [hG_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hcell : ∀ i ∈ Finset.range (j + 1), ∀ l ∈ Finset.range (j + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (10 * S l) * G := by
    intro i hi l hl
    have h1 := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie i x
    have h2 := hS g₁ T htie hδ_le hδ0 hbound l x
    have h1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    have h2_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
    have hb_le_grid : b (i + 1) * Combinatorics.antidiagonalTupleGrid b l ≤
        Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) :=
      Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb l (i + 1) (by omega)
    have hgrid_le_G : Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) ≤ G := by
      rw [hG_def]
      refine Finset.single_le_sum
        (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
        (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k) ?_
      rw [Finset.mem_range] at hi hl ⊢
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
        ≤ (10 * b (i + 1)) * (S l * Combinatorics.antidiagonalTupleGrid b l) := by
          refine mul_le_mul ?_ h2 h2_nn (by
            have := hb (i + 1); linarith)
          exact h1
      _ = (10 * S l) * (b (i + 1) * Combinatorics.antidiagonalTupleGrid b l) := by ring
      _ ≤ (10 * S l) * Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) := by
          refine mul_le_mul_of_nonneg_left hb_le_grid ?_
          have := hS_nn l; linarith
      _ ≤ (10 * S l) * G := by
          refine mul_le_mul_of_nonneg_left hgrid_le_G ?_
          have := hS_nn l; linarith
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (I := I) (M := M) g₀ g₁ j x) ?_
  have hsum : (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
      (∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    calc (∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (j + 1 - i), (10 * S l) * G :=
          Finset.sum_le_sum fun l hl => hcell i hi l hl
      _ = (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
          rw [Finset.mul_sum, Finset.sum_mul]
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ((∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G) :=
        mul_le_mul_of_nonneg_left hsum (appCcGdiag_nonneg (E := E) j)
    _ = (diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
        ring

end NormedConnectionDifferenceGrid

section NormedRiemannLoweredGrid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def quadraticConnDiffCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
    (connDiffSection (I := I) g₁ g₀)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma quadraticConnDiffCc_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0)) := by
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
          (connDiffSection (I := I) g₁ g₀)).toSection x) om) from rfl]
  rw [toModel_appCcRS_armSlotEndoPassZeroCc_eval (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) (connDiffSection (I := I) g₁ g₀) x om w]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      connDiffPairing (I := I) g₁ g₀ x om from rfl]
  have hchg : Tensor0SSpace.toModel (connDiffPairing (I := I) g₁ g₀ x om)
      (fun j : Fin 2 => if j = 0 then
        connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (w 1) (w 2) else w 0) =
      connDiffPairing (I := I) g₁ g₀ x om
        (fun j : Fin 2 => if j = 0 then
          connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (w 1) (w 2) else w 0) := rfl
  rw [hchg]
  rw [show (fun j : Fin 2 => if j = 0 then
        connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (w 1) (w 2) else w 0) =
      (Fin.cons (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2))
        (fun _ : Fin 1 => w 0) : Fin 2 → TangentSpace I x) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [if_pos rfl]
      rfl
    · intro i
      rw [if_neg (Fin.succ_ne_zero i)]
      rfl]
  rw [connDiffPairing_apply]
  rw [cotangentToDual_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def covectorExtensionSection (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  ⟨fun b : M => g0FlatCLM (I := I) g₀ b
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b),
   by
     have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
         (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
           (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b)) :=
       smoothExtensionTangent_contMDiff (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)
     exact ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) hU⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma covectorExtensionSection_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    covectorExtensionSection (I := I) (M := M) g₀ x om x = om := by
  change g0FlatCLM (I := I) g₀ x
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) x) = om
  rw [smoothExtensionTangent_eq (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)]
  exact g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannLoweredBackgroundDifference_palatini_repr
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
        rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  set X0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (v 0) with hX0_def
  set X1 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (v 1) with hX1_def
  set X2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (v 2) with hX2_def
  have hX0x : X0 x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hX1x : X1 x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  have hX2x : X2 x = v 2 := smoothExtensionTangent_eq (I := I) x (v 2)
  set omSec : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
    covectorExtensionSection (I := I) (M := M) g₀ x om with homSec_def
  have homx : omSec x = om := covectorExtensionSection_self (I := I) (M := M) g₀ x om
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hpair : ∀ ww : TangentSpace I x,
      g₀.inner x ww u = cotangentToDual (I := I) (x := x) om ww := by
    intro ww
    rw [hu_def]
    rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
    rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₀ x om ww]
    rw [show metricComparisonEndo (I := I) g₀ g₀ x ww = ww from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  have hDQ : ∀ (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om)
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      cotangentToDual (I := I) (x := x) om
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) +
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) (X x)) := by
    intro X Y Z
    have hsplit : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
          quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) om) +
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om) := by
      rw [SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    have hbridge : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) om)
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
        cotangentToDual (I := I) (x := x) om
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) := by
      rw [← homx]
      rw [connDiffSection_covGrad_eq_covDerivConnDiff (I := I) (M := M) g₁ g₀ omSec X Y Z x]
      rw [cotangentToDual_apply]
    rw [hbridge]
    rw [quadraticConnDiffCc_toModel (I := I) (M := M) g₀ g₁ x om
      (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))]
    rfl
  have htor : (LeviCivita (I := I) g₀).torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g₀
  have hpal := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    (X := fun b => X0 b) (Y := fun b => X1 b) (Z := fun b => X2 b)
    X0.contMDiff X1.contMDiff X2.contMDiff htor x
  have hop1 : riemannOp (LeviCivita (I := I) g₁) x (v 0) (v 1) (v 2) =
      riemannSec (LeviCivita (I := I) g₁) (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := by
    rw [← hX0x, ← hX1x, ← hX2x]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁)
      X0.contMDiff X1.contMDiff X2.contMDiff
  have hop0 : riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) (v 2) =
      riemannSec (LeviCivita (I := I) g₀) (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := by
    rw [← hX0x, ← hX1x, ← hX2x]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      X0.contMDiff X1.contMDiff X2.contMDiff
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) om) v =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (v 1) (v 2)) u -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) (v 2)) u := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          cometricRaiseSlot0Fib g₀ 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
              (unitTensor (I := I) (M := M) x))) om) from rfl]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
        (unitTensor (I := I) (M := M) x)) om]
    rw [interiorProduct_toModel_eval_pal (I := I) (M := M) 3 x
      (inverseMetricSharpFib (I := I) g₀ x om) _ v]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) x from rfl]
    rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i : Fin 4 =>
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
          (fun k => (show E from v k)) : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) i)) =
      (![v 0, (show E from u), v 1, v 2] : Fin 4 → E) from by
      funext i
      fin_cases i <;> rfl]
    rw [riemannLoweredBackgroundDifference_unitModel_apply (I := I) (M := M) g₀ g₁ x
      (![v 0, (show E from u), v 1, v 2] : Fin 4 → TangentSpace I x)]
    rfl
  rw [hLHS]
  have hRHSsub : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) -
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) from by
      rw [SmoothCcTensor.toSection_sub]
      rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hRHSsub]
  have hterm : ∀ (σ : Equiv.Perm (Fin 3)) (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ((fun i => v (σ i)) : Fin 3 → E) = Fin.cons (X x) (Fin.cons (Y x) ![Z x]) →
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v =
      cotangentToDual (I := I) (x := x) om
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) +
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) (X x)) := by
    intro σ X Y Z htup
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr σ
            ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x)) om) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
        quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [htup]
    exact hDQ X Y Z
  have htup1 : ((fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) : Fin 3 → E) =
      Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show ((Equiv.swap (1 : Fin 3) 2) 0) = (0 : Fin 3) from by decide]
      rw [show (Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) : Fin 3 → E) 0 = X0 x from rfl]
      rw [hX0x]
    · intro j
      refine Fin.cases ?_ ?_ j
      · rw [show (Fin.succ (0 : Fin 2)) = (1 : Fin 3) from rfl]
        rw [show ((Equiv.swap (1 : Fin 3) 2) 1) = (2 : Fin 3) from by decide]
        rw [show (Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) : Fin 3 → E) 1 = X2 x from rfl]
        rw [hX2x]
      · intro j2
        refine Fin.cases ?_ (fun j3 => j3.elim0) j2
        rw [show (Fin.succ (Fin.succ (0 : Fin 1))) = (2 : Fin 3) from rfl]
        rw [show ((Equiv.swap (1 : Fin 3) 2) 2) = (1 : Fin 3) from by decide]
        rw [show (Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) : Fin 3 → E) 2 = X1 x from rfl]
        rw [hX1x]
  have htup2 : ((fun i => v ((finRotate 3) i)) : Fin 3 → E) =
      Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show ((finRotate 3) 0) = (1 : Fin 3) from by decide]
      rw [show (Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) : Fin 3 → E) 0 = X1 x from rfl]
      rw [hX1x]
    · intro j
      refine Fin.cases ?_ ?_ j
      · rw [show (Fin.succ (0 : Fin 2)) = (1 : Fin 3) from rfl]
        rw [show ((finRotate 3) 1) = (2 : Fin 3) from by decide]
        rw [show (Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) : Fin 3 → E) 1 = X2 x from rfl]
        rw [hX2x]
      · intro j2
        refine Fin.cases ?_ (fun j3 => j3.elim0) j2
        rw [show (Fin.succ (Fin.succ (0 : Fin 1))) = (2 : Fin 3) from rfl]
        rw [show ((finRotate 3) 2) = (0 : Fin 3) from by decide]
        rw [show (Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) : Fin 3 → E) 2 = X0 x from rfl]
        rw [hX0x]
  rw [hterm (Equiv.swap (1 : Fin 3) 2) X0 X2 X1 htup1]
  rw [hterm (finRotate 3) X1 X2 X0 htup2]
  rw [hop1, hop0]
  rw [hpal]
  rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
  rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
  rw [map_sub (g₀.inner x), ContinuousLinearMap.sub_apply]
  rw [map_sub (g₀.inner x), ContinuousLinearMap.sub_apply]
  simp only [hpair]
  have hc1 : covDerivConnDiff (I := I) g₀ g₁
      (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := rfl
  have hc2 : covDerivConnDiff (I := I) g₀ g₁
      (fun b => X1 b) (fun b => X0 b) (fun b => X2 b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => X1 b) (fun b => X0 b) (fun b => X2 b) x := rfl
  have hq1 : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (X2 x) (X1 x)) (X0 x) =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (fun b => X1 b) (fun b => X2 b) x) ((fun b => X0 b) x) := rfl
  have hq2 : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (X2 x) (X0 x)) (X1 x) =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (fun b => X0 b) (fun b => X2 b) x) ((fun b => X1 b) x) := rfl
  rw [← hc1, ← hc2, ← hq1, ← hq2]
  ring

def gridSumPairCount (m1 m2 : ℕ) : ℝ :=
  ∑ k1 ∈ Finset.range m1, ∑ k2 ∈ Finset.range m2, tGridCount k1 * tGridCount k2

lemma gridSumPairCount_nonneg (m1 m2 : ℕ) : 0 ≤ gridSumPairCount m1 m2 :=
  Finset.sum_nonneg fun k1 _ => Finset.sum_nonneg fun k2 _ =>
    mul_nonneg (tGridCount_nonneg k1) (tGridCount_nonneg k2)

lemma gridSum_mul_gridSum_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    (∑ k ∈ Finset.range m1, Combinatorics.antidiagonalTupleGrid b k) *
      (∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k) ≤
    gridSumPairCount m1 m2 * ∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k := by
  classical
  have hG_nn : ∀ k, 0 ≤ Combinatorics.antidiagonalTupleGrid b k :=
    fun k => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hS3_nn : 0 ≤ ∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k :=
    Finset.sum_nonneg fun k _ => hG_nn k
  rw [Finset.sum_mul]
  rw [gridSumPairCount, Finset.sum_mul]
  refine Finset.sum_le_sum fun k1 hk1 => ?_
  calc Combinatorics.antidiagonalTupleGrid b k1 *
        ∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k2 ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k1 *
          Combinatorics.antidiagonalTupleGrid b k2 := by rw [Finset.mul_sum]
    _ ≤ ∑ k2 ∈ Finset.range m2, (tGridCount k1 * tGridCount k2) *
          (∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k) := by
        refine Finset.sum_le_sum fun k2 hk2 => ?_
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k1 k2) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (tGridCount_nonneg k1) (tGridCount_nonneg k2))
        refine Finset.single_le_sum (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
          (fun k _ => hG_nn k) ?_
        rw [Finset.mem_range] at hk1 hk2 ⊢
        omega
    _ = (∑ k2 ∈ Finset.range m2, tGridCount k1 * tGridCount k2) *
          (∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Finset.sum_mul]

set_option backward.isDefEq.respectTransparency false in
private def perturbationSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x
        (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g₀ T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma perturbationSharpEndoFib_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : TangentSpace I x) :
    perturbationSharpEndoFib (I := I) (M := M) g₀ T x v =
      metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
  rw [perturbationSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_perturbationSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (perturbationSharpEndoFib (I := I) (M := M) g₀ T x v) w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [perturbationSharpEndoFib_apply]
  exact inner_metricSharp (I := I) g₀ x
    (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem perturbationSharpEndoFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (perturbationSharpEndoFib (I := I) (M := M) g₀ T x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => perturbationSharpEndoFib (I := I) (M := M) g₀ T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g₀ T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g₀ T b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (Y x))
  rw [perturbationSharpEndoFib_apply]

def perturbationSharpEndoField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => perturbationSharpEndoFib (I := I) (M := M) g₀ T x
  contMDiff_toFun := perturbationSharpEndoFib_contMDiff (I := I) (M := M) g₀ T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin_pt (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
private lemma slotInsert_perturbationSharp_eq_raise_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (perturbationSharpEndoField (I := I) (M := M) g₀ T) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (w 0)
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (perturbationSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x om
      (Function.update w 0 (perturbationSharpEndoField (I := I) (M := M) g₀ T x (w 0)))]
    rw [Function.update_self]
    rw [show (perturbationSharpEndoField (I := I) (M := M) g₀ T x) =
        perturbationSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
    rw [cotangentToDual_eq_inner_sharp (I := I) (M := M) g₀ x om
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (w 0))]
    rw [inner_perturbationSharpEndoFib]
  rw [hLHS]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_pal (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g₀ x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (ccTensor02Symm (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(w 0 : E), (show E from inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x
    (w 0) (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannG1LoweringDifference_slotInsert_repr (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  have hLHS : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
        riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m =
      ccTensorBilinSymm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1) := by
    have hsub : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m =
        unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) x m -
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m := by
      rw [unitModel, unitModel, unitModel]
      rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x) =
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁).toSection x -
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
        ContinuousMultilinearMap.sub_apply]
    rw [hsub]
    rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g₁ x m]
    rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x m]
    rw [htie x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1)]
    ring
  rw [hLHS]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
        (perturbationSharpEndoField (I := I) (M := M) g₀ T))
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have happ : unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
          (perturbationSharpEndoField (I := I) (M := M) g₀ T))
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) x
      (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) =
      unitModel (I := I) (M := M) g₀ 4
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) x
        (Function.update (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            ((fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) 0))) := by
    rw [unitModel, unitModel]
    rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
          (perturbationSharpEndoField (I := I) (M := M) g₀ T))
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
        (unitTensor (I := I) (M := M) x) =
      slotInsertEndoFib (I := I) (M := M) 4 0 x
        (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
      rw [appCcRS_toSection]
      rfl]
    rw [slotInsertEndoFib_apply_eval]
  rw [happ]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 4 =>
      (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
        (perturbationSharpEndoField (I := I) (M := M) g₀ T x
          ((fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0)))
        ((Equiv.swap (0 : Fin 4) 1) i)) =
      (![(m 0 : E),
        (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
        (m 2 : E), (m 3 : E)] : Fin 4 → E) from by
    funext i
    fin_cases i
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 0) = m 0
      rw [show ((Equiv.swap (0 : Fin 4) 1) 0) = (1 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 1) = (0 : Fin 4) from by decide]
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 1) =
        (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1))
      rw [show ((Equiv.swap (0 : Fin 4) 1) 1) = (0 : Fin 4) from by decide]
      rw [Function.update_self]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 0) = (1 : Fin 4) from by decide]
      rfl
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 2) = m 2
      rw [show ((Equiv.swap (0 : Fin 4) 1) 2) = (2 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 2) = (2 : Fin 4) from by decide]
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 3) = m 3
      rw [show ((Equiv.swap (0 : Fin 4) 1) 3) = (3 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 3) = (3 : Fin 4) from by decide]]
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 0 = m 0 from rfl]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 1 =
    perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1) from rfl]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 2 = m 2 from rfl]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 3 = m 3 from rfl]
  rw [g₀.symm x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3))
    (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1))]
  rw [inner_perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)
    (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3))]
  rw [ccTensorBilinSymm_symm (I := I) g₀ T x (m 1)
    (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3))]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_eq_sum_componentSq_of_horth_pt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J) ^ 2 := by
  classical
  haveI : Nonempty (Fin n) := by
    rw [hn]
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hrank]; exact hn
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin n, bse i = e i := by
    intro i; rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ r s x S e bse hn hbse horth

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_zero_toModel_pt
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g₀ 0 s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 0 → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x))
        (fun k => (show E from e (L k))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (coframeS (I := I) (M := M) g₀ x 0 e K) (fun k => e (L k)) from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g₀ x e K]
  rfl

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rfns_symmS_zero_le_of_ball (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 2 x
    ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) e hnE horth]
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ 2 x
        (ccTensor02Symm (I := I) (M := M) g₀ T) e K J]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun k => (show E from e (J k))) =
          unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

lemma rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) := by
  refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (perturbationSharpEndoField (I := I) (M := M) g₀ T) j x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [slotInsert_perturbationSharp_eq_raise_symmS (I := I) (M := M) g₀ T]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (ccTensor02Symm (I := I) (M := M) g₀ T)) j x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) (ccTensor02Symm (I := I) (M := M) g₀ T) j x]

theorem rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  set AA : ℕ → ℕ → ℝ := fun i i' => ∑ l ∈ Finset.range (i + 1 - i'),
    CA i' * CA l * gridSumPairCount (i' + 2) (l + 2) with hAA_def
  have hAA_nn : ∀ i i', 0 ≤ AA i i' := by
    intro i i'
    rw [hAA_def]
    exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hCA_nn i') (hCA_nn l)) (gridSumPairCount_nonneg _ _)
  clear_value AA
  refine ⟨fun i => 8 * CA (i + 1) + 8 * (diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i'),
    fun i => by
      have h1 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i' :=
        Finset.sum_nonneg fun i' _ => mul_nonneg (Nat.cast_nonneg _) (hAA_nn i i')
      have h2 := appCcGdiag_nonneg (E := E) i
      have h4 := hCA_nn (i + 1)
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgoal_eq : (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n, b (e m)) =
      ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
  rw [hgoal_eq]
  set WW : ℝ := ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k
    with hWW_def
  have hWW_nn : 0 ≤ WW := by
    rw [hWW_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hgsum_le_WW : ∀ m : ℕ, m ≤ i + 3 →
      (∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k) ≤ WW := by
    intro m hm
    rw [hWW_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm) ?_
    intro k _ _
    exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  clear_value WW
  have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)))).toSection x) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) i x]
  rw [hstep1]
  rw [riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁]
  set DQ : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hDQ_def
  have hrs_eq : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ DQ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i DQ).toSection x) := by
    intro σ
    exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ DQ
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ DQ)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hsubsec : (iteratedCovGrad (I := I) g₀ 1 3 i
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ -
        rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection x +
      (- (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg,
      SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection +
        (- iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection) x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection x +
      (- iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsubsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
  rw [rfns_neg_pt (I := I) (M := M) g₀ 1 (3 + i) x]
  rw [hrs_eq (Equiv.swap (1 : Fin 3) 2), hrs_eq (finRotate 3)]
  have hDQsec : (iteratedCovGrad (I := I) g₀ 1 3 i DQ).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x := by
    rw [hDQ_def, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  have hD_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      CA (i + 1) * WW := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (i + 1) x) ?_
    exact mul_le_mul_of_nonneg_left (hgsum_le_WW (i + 3) (le_refl _)) (hCA_nn (i + 1))
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 2 3 i'
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * AA i i') * WW := by
    intro i' hi'
    have hi'le : i' ≤ i := by
      rw [Finset.mem_range] at hi'; omega
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
        ((iteratedCovGrad (I := I) g₀ 2 3 i'
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connDiffArm_le
        (I := I) (M := M) g₀ g₁ i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact hCA g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k :=
      Finset.sum_le_sum fun l _ => hCA g₁ T htie hδ_le hδ0 hbound l x
    have hprod_nn1 : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _
    have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hgsA_nn : 0 ≤ CA i' * ∑ k ∈ Finset.range (i' + 2),
        Combinatorics.antidiagonalTupleGrid b k :=
      mul_nonneg (hCA_nn i') (Finset.sum_nonneg fun k _ =>
        Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
    have hpairsum : ∀ l ∈ Finset.range (i + 1 - i'),
        (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
          (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k) ≤
        (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by
      intro l hl
      have hl_le : l ≤ i - i' := by
        rw [Finset.mem_range] at hl; omega
      have hgs := gridSum_mul_gridSum_le b hb (i' + 2) (l + 2) (i + 3) (by omega)
      calc (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
            (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k)
          = (CA i' * CA l) *
              ((∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
                (∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k)) := by
            ring
        _ ≤ (CA i' * CA l) * (gridSumPairCount (i' + 2) (l + 2) *
              (∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn i') (hCA_nn l))
            exact hgs
        _ ≤ (CA i' * CA l) * (gridSumPairCount (i' + 2) (l + 2) * WW) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn i') (hCA_nn l))
            refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
            exact hgsum_le_WW (i + 3) (le_refl _)
        _ = (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by ring
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 2 3 i'
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x)
        ≤ ((Module.finrank ℝ E : ℝ) *
            (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k)) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k :=
          mul_le_mul hA1 hA2 hprod_nn1 (mul_nonneg hfr_nn hgsA_nn)
      _ = (Module.finrank ℝ E : ℝ) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
              (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k) := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpairsum) hfr_nn
      _ = ((Module.finrank ℝ E : ℝ) * AA i i') * WW := by
          have hAAval : AA i i' = ∑ l ∈ Finset.range (i + 1 - i'),
              CA i' * CA l * gridSumPairCount (i' + 2) (l + 2) := by rw [hAA_def]
          rw [hAAval, ← Finset.sum_mul]
          ring
  have hQ_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW := by
    rw [show quadraticConnDiffCc (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
          (connDiffSection (I := I) g₁ g₀) from rfl]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 1 2 3
      (armSlotEndoPassZeroCc (I := I) (M := M) g₀
        (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
      (connDiffSection (I := I) g₁ g₀) x) ?_
    calc diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
                ((iteratedCovGrad (I := I) g₀ 2 3 i'
                  (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l
                    (connDiffSection (I := I) g₁ g₀)).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), ((Module.finrank ℝ E : ℝ) * AA i i') * WW :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = (diagonalGridGrowthFactor (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW := by
          rw [← Finset.sum_mul]
          ring
  rw [hDQsec]
  have hsum_le := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x
    ((iteratedCovGrad (I := I) g₀ 1 3 i
      (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x)
    ((iteratedCovGrad (I := I) g₀ 1 3 i
      (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x)
  have hDQfull : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
      2 * (CA (i + 1) * WW) +
        2 * ((diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW) := by
    refine le_trans hsum_le ?_
    linarith [hD_le, hQ_le]
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 i
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 i
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x)
      ≤ 2 * (2 * (CA (i + 1) * WW) +
          2 * ((diagonalGridGrowthFactor (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW)) +
        2 * (2 * (CA (i + 1) * WW) +
          2 * ((diagonalGridGrowthFactor (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW)) := by
        linarith [hDQfull]
    _ = (8 * CA (i + 1) + 8 * (diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i')) * WW := by
        ring

end NormedRiemannLoweredGrid

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma linearMap_trace_eq_orthoFrame_inner_sum (g₀ : SmoothRiemannianMetric I M)
    (x : M) (G : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) G =
      ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (G (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₀ x i x with hB_def
  have horth : ∀ i j, g₀.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g₀.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g₀.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (v : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr v j = g₀.inner x v (B j) := by
    intro v j
    conv_rhs => rw [← bB.sum_repr v]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    have hsimp : ∀ i, g₀.inner x (bB.repr v i • bB i) (B j) =
        bB.repr v i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hbB_coe i, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℝ bB G]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply, hrepr (G (bB i)) i, hbB_coe i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interiorProduct_toModel_eval_lc (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_om_eval_lc (x : M) (om : Tensor0SSpace 1 I x) (V : TangentSpace I x) :
    Tensor0SSpace.toModel om (fun _ : Fin 1 => (V : E)) =
      cotangentToDual (I := I) om V := by
  rw [cotangentToDual_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
theorem slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricciEndomorphismField (I := I) (M := M) g₀) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  set W2 : SmoothCcTensor g₀ 0 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) with hW2_def
  have hW2unitModel : ∀ (x : M) (mm : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2 W2 x mm =
        ricciTensor (I := I) g₁ x (mm 0) (mm 1) - ricciTensor (I := I) g₀ x (mm 0) (mm 1) := by
    intro x mm
    have hsec : (W2.toSection x) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            cometricDoubleTraceFib (I := I) g₀ 2 x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x) := by
      rw [hW2_def, appCcRS_toSection, cometricDoubleTraceField_toSection]
    rw [unitModel]
    rw [show (W2.toSection x) (unitTensor (I := I) (M := M) x) =
        cometricDoubleTraceFib (I := I) g₀ 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
            (unitTensor (I := I) (M := M) x)) from by rw [hsec]; rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [modelDoubleTrace_apply]
    have hT : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x := rfl
    rw [hT]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x)
      (fun j => (mm j : E))]
    have hker : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (fun j => (mm j : E)))) =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x) -
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
              (smoothOrthoFrame (I := I) g₀ x i x) := by
      intro i
      rw [riemannLoweredBackgroundDifference_unitModel_apply]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hker i), Finset.sum_sub_distrib]
    have htr1 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₁ x (mm 0) (mm 1) := by
      rw [ricciTensor_apply (I := I) g₁ x (mm 0) (mm 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₁ x (mm 0) (mm 1))]
      rfl
    have htr0 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₀ x (mm 0) (mm 1) := by
      rw [ricciTensor_apply (I := I) g₀ x (mm 0) (mm 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₀ x (mm 0) (mm 1))]
      rfl
    rw [htr1, htr0]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x (ricEndoRaisedFib (I := I) g₀ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hupd : ∀ V : TangentSpace I x,
      (Function.update m 0 (show E from V)) = fun _ : Fin 1 => (V : E) := by
    intro V
    funext j
    fin_cases j
    simp [Function.update]
  have hsharp_pair : ∀ α : TangentSpace I x →ₗ[ℝ] ℝ,
      cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) = α u := by
    intro α
    rw [show cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) =
        cotangentToDualLinear (I := I) (x := x) om (metricSharp (I := I) g₀ x α) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om (metricSharp (I := I) g₀ x α), ← hu_def]
    exact inner_metricSharp_right (I := I) g₀ x α u
  have hLmix : Tensor0SSpace.toModel om
      (Function.update m 0 (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (m 0))) =
      (ricciTensor (I := I) g₁ x (m 0)).toLinearMap u := by
    rw [show (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (m 0)) =
        (show E from metricSharp (I := I) g₀ x
          (ricciTensor (I := I) g₁ x (m 0)).toLinearMap) from
      ricMixedSharpEndoFib_apply (I := I) (M := M) g₀ g₁ x (m 0)]
    rw [hupd, toModel_om_eval_lc, hsharp_pair]
  have hLraised : Tensor0SSpace.toModel om
      (Function.update m 0 (ricEndoRaisedFib (I := I) g₀ x (m 0))) =
      (ricciTensor (I := I) g₀ x (m 0)).toLinearMap u := by
    rw [show (ricEndoRaisedFib (I := I) g₀ x (m 0)) =
        (show E from metricSharp (I := I) g₀ x
          (ricciTensor (I := I) g₀ x (m 0)).toLinearMap) from
      ricEndoRaisedFib_apply (I := I) g₀ x (m 0)]
    rw [hupd, toModel_om_eval_lc, hsharp_pair]
  rw [hLmix, hLraised]
  rw [cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
            (unitTensor (I := I) (M := M) x))) om) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) from
    cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_lc (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om) _ m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
          (fun k : Fin 1 => (show E from m k)) : Fin 2 → TangentSpace I x)
          ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(m 0 : TangentSpace I x), u] : Fin 2 → TangentSpace I x) from by
    funext i
    fin_cases i <;>
      simp [hu_def]]
  rw [hW2unitModel x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

end RiemannLoweredDifference

end Connection
end Integral
end DifferentialGeometry
end
