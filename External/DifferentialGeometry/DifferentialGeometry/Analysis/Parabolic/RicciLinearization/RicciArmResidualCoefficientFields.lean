import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsMetricPerturbation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsConnDiffCommutator
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsSharpGradientKoszul
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsRicciFold
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsBackgroundDifferenceRefold
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsFrameKernelContraction

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

set_option maxHeartbeats 3200000

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma foldMetricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem foldPerturbation_eq_metricDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    P = metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ := by
  have hsymm : ccTensor02Symm (I := I) (M := M) g₀ P = P :=
    foldSymmS_eq_self (I := I) (M := M) g₀ P hPsymm
  have hmd : metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
      ccTensor02Symm (I := I) (M := M) g₀ P := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [show metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
        metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀
        from rfl]
    rw [unitModel_sub_loc (I := I) (M := M) g₀ 2
      (metricCcTensor (I := I) (M := M) g₀ g₁) (metricCcTensor (I := I) (M := M) g₀ g₀) x]
    rw [ContinuousMultilinearMap.sub_apply]
    rw [foldMetricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      foldMetricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
    rw [show unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x m =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x ![m 0, m 1] from by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x (m 0) (m 1)]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rw [htie x (m 0) (m 1)]
    ring
  rw [hmd, hsymm]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem foldCcTensor22_ext_of_appCc (g₀ : SmoothRiemannianMetric I M)
    (C D : SmoothCcTensor g₀ 2 2)
    (h : ∀ W : SmoothCcTensor g₀ 0 2,
      operatorFieldApply (I := I) (M := M) g₀ 2 2 C W = operatorFieldApply (I := I) (M := M) g₀ 2 2 D W) : C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  set V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u))
    with hV_def
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW₀_def
  have h1 : (operatorFieldApply (I := I) (M := M) g₀ 2 2 C W₀).toSection x =
      (operatorFieldApply (I := I) (M := M) g₀ 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
          (unitTensor (I := I) (M := M) x)) := by
    have h1' := congrArg (fun (T : TensorRSSpace 0 2 I x) =>
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T)
        (unitTensor (I := I) (M := M) x)) h1
    exact h1'
  have hWval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (unitTensor (I := I) (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW, hV_def]
    change ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
          (1 : ℝ)) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hWval] at h2
  exact h2


private theorem foldHalfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) =
      ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
        + backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁
        + refoldKernelContractionField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := foldPerturbation_eq_metricDifference (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine foldCcTensor22_ext_of_appCc (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [appCc_smul_left (I := I) (M := M) g₀ 2 2, foldAppCc_sub_left (I := I) (M := M) g₀ 2 2]
  rw [hprim]
  rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
          - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
      - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
          (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)) =
      backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁ from rfl]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
    (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
      + backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
    (refoldKernelContractionField (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
    (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) W]
  rw [appCc_refoldKernelContractionField (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]


theorem linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_eq_residualFieldSum
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    ccInputSlotSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)) =
      ccInputSlotSymm (I := I) (M := M) g₀
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (refoldKernelContractionField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) := by
  rw [foldHalfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (I := I) (M := M) g₀ g₁ P htie hPsymm]
  rw [ccInputSymm_add (I := I) (M := M) g₀, ccInputSymm_add (I := I) (M := M) g₀,
    ccInputSymm_add (I := I) (M := M) g₀]
  abel


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricCcTensor_apply (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x v w =
      g.inner x v w := by
  have hround : ccTensorMultilinear (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x =
      metricCcTensorFib (I := I) g x := by
    unfold ccTensorMultilinear metricCcTensor
    rw [MixedSection.toMultilinearSection_fromMultilinearSection]
    rfl
  rw [ccTensorBilin_apply]
  unfold ccTensorModel
  rw [hround]
  rfl


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
