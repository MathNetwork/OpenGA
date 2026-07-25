import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamLinearizedChristoffel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldTameEnvelope
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcArmReadoutCovDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcChartCurvatureJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcArmCoeffJetEnvelopeBallUniform
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcCorrectionFieldConstruction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_linearizedRicciOrder1DivCoeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨_, _, _, hident, _, _⟩ :=
    (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
  refine ⟨linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ',
    linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ',
    linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ',
    linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ',
    linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ',
    linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ',
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
      (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ')
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ') x
  · intro x
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2
      (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ')
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ') x
  · intro x
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ')
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ') x
  · intro s hs x v
    exact hident hTsymm hT'symm s hs x v hδ_lt hδ'_lt

theorem linearizedRicci_lichnerowicz_arm1_identity (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v :=
  exists_linearizedRicciOrder1DivCoeff (I := I) g₀ T T' hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'

theorem exists_linearizedRicci_threeArm_coeffFields
    (g₀ _g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  exact linearizedRicci_lichnerowicz_arm1_identity (I := I) g₀ T T'
    hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'


theorem exists_ricciArmOrder1Coeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1) -
            ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1) =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid⟩ :=
    exists_linearizedRicci_threeArm_coeffFields (I := I) (M := M) g₀ g_bg T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set R₀ : SmoothCcTensor g₀ 2 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 with hR₀
  set R₁ : SmoothCcTensor g₀ 3 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 with hR₁
  set R₂ : SmoothCcTensor g₀ 4 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 with hR₂
  refine ⟨R₀, R₁, R₂, fun x v => ?_⟩
  set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
  set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
  set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
  have hRic :=
    ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
  rw [hRic]
  have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v := by
    rw [MeasureTheory.ae_iff]
    have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
    refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
    rw [Set.mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hsmem, hsneq⟩ := hs
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
    exact hsneq (by rw [hid s hsIoo x v, unitModel_add2_apply, unitModel_add2_apply])

  rw [intervalIntegral.integral_congr_ae hintegrand]
  have hI0 : IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v)
      MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable (I := I) g₀ 2 Φ₀ W₀ hSI hc0 x v
  have hI1 : IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v)
      MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable (I := I) g₀ 3 Φ₁ W₁ hSI hc1 x v
  have hI2 : IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v)
      MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable (I := I) g₀ 4 Φ₂ W₂ hSI hc2 x v
  rw [intervalIntegral.integral_add (hI0.add hI1) hI2,
    intervalIntegral.integral_add hI0 hI1]
  have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Φ₀ W₀
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
  have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Φ₁ W₁
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
  have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Φ₂ W₂
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
  rw [← hR₀] at he0
  rw [← hR₁] at he1
  rw [← hR₂] at he2
  rw [← he0, ← he1, ← he2, unitModel_add2_apply, unitModel_add2_apply]


theorem ricciTensor_realize_sub_eq_threeArm_appCc
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ricciTensor (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1)
            - (-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₀, R₁, R₂, hR⟩ :=
    exists_ricciArmOrder1Coeff (I := I) (M := M) g₀ g_bg T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨(-2 : ℝ) • R₀, (-2 : ℝ) • R₁, (-2 : ℝ) • R₂, fun x v => ?_⟩
  set A₀ : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  rw [appCc_smul_left_local, appCc_smul_left_local, appCc_smul_left_local, ← hA₀, ← hA₁, ← hA₂]
  have hsmulsum : (-2 : ℝ) • A₀ + (-2 : ℝ) • A₁ + (-2 : ℝ) • A₂ =
      (-2 : ℝ) • (A₀ + A₁ + A₂) := by
    rw [smul_add, smul_add]
  rw [hsmulsum]
  rw [unitModel_smul_local, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have htoinfty : ∀ (g : SmoothRiemannianMetric I M),
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x (v 0) (v 1) =
        ricciTensor (I := I) g x (v 0) (v 1) := fun g => rfl
  rw [htoinfty, htoinfty, hA₀, hA₁, hA₂, ← hR x v]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
