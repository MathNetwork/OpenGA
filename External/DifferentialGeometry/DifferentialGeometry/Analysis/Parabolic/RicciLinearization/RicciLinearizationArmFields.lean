import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections


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

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def linearizedRicciThreeArmHjoint (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ} : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
    (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 ((Φ p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))

end NormedSpaceModel

section NormedArmFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def linearizedRicciArm0BaseCoeff (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
    - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

noncomputable def linearizedRicciArm1Fib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      raisedKoszulFib (I := I) g₀ g₁ x).comp
    (cometricDoubleTraceFib (I := I) g₁ 1 x)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem linearizedRicciArm1Fib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) :
    linearizedRicciArm1Fib (I := I) g₀ g₁ x D =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          raisedKoszulFib (I := I) g₀ g₁ x)
        (cometricDoubleTraceFib (I := I) g₁ 1 x D) := by
  rw [linearizedRicciArm1Fib, ContinuousLinearMap.comp_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem linearizedRicciArm1Fib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (linearizedRicciArm1Fib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => linearizedRicciArm1Fib (I := I) g₀ g₁ x)
  intro Y
  have hdt : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) Y.contMDiff
  have hkos : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            raisedKoszulFib (I := I) g₀ g₁ x)
          (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (raisedKoszulFib_contMDiff (I := I) g₀ g₁) hdt
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [linearizedRicciArm1Fib, ContinuousLinearMap.comp_apply]

noncomputable def ricciArmOrder1KoszulCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from linearizedRicciArm1Fib (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciArm1Fib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem ricciArmOrder1KoszulCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from linearizedRicciArm1Fib (I := I) g₀ g₁ x) := rfl

def linearizedRicciArm1BaseCoeff (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

def traceHessianSlotPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3

noncomputable def domDomCongrFib (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          traceHessianSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrFib_apply (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFib (I := I) x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFib]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def traceHessianFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFib (I := I) x)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem traceHessianFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (traceHessianFib (I := I) g₁ x D) =
      modelDoubleTrace (E := E) 2 (cometricLmodel (I := I) g₁ x)
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, cometricDoubleTraceFib_toModel,
    domDomCongrFib_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongr_section_contMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
          Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem traceHessianFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (traceHessianFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => traceHessianFib (I := I) g₁ x)
  intro Y
  have hYρ := domDomCongr_section_contMDiff (I := I) traceHessianSlotPerm (fun x => Y x) Y.contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, domDomCongrFib_apply]
  rfl

noncomputable def traceHessianCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
      contMDiff_toFun := traceHessianFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem traceHessianCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) := rfl

def linearizedRicciArm2FieldLichnerowicz (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
    - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_eq_ccTensorBilin_local (g₀ : SmoothRiemannianMetric I M)
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem cometricLmodel_covectorOfCLM_inner (g₁ : SmoothRiemannianMetric I M) (y : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I y) :
    g₁.inner y (cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) u = φ (u : E) := by
  have h1 : cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      inverseMetricSharpFib (I := I) g₁ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
      (fun _ : Fin 1 => (u : E)) = φ (u : E)
  rw [Tensor0SBundle.model_covectorOfCLM_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem traceHessianCoeff_apply_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (traceHessianCoeff (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
                W.toSection x) (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [traceHessianCoeff_toSection, traceHessianFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]

omit [NeZero (Module.finrank ℝ E)] in
theorem cDualBasis_trace_basis_indep
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), F (B.cDualBasis k) (B k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        F ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k) := by
  have hcoordB : ∀ k : Fin (Module.finrank ℝ E),
      B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
      (congrFun (Module.Basis.coe_dualBasis B) k)
  have hcoordFin : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
      (congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k)
  rw [show (∑ k : Fin (Module.finrank ℝ E), F (B.cDualBasis k) (B k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (LinearMap.toContinuousLinearMap (B.coord k)) (B k) from
      Finset.sum_congr rfl (fun k _ => by rw [hcoordB k])]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            F ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k))
            ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => by rw [hcoordFin k])]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  have h_cov : ∀ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
          LinearMap.toContinuousLinearMap (B.coord i)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
          LinearMap.toContinuousLinearMap (B.coord i)) z
          = ∑ i : Fin (Module.finrank ℝ E), b.coord j (B i) * B.coord i z := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin (Module.finrank ℝ E), B.coord i z • B i) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j z := by
              rw [show (∑ i : Fin (Module.finrank ℝ E), B.coord i z • B i) = z from
                B.sum_repr z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        F (LinearMap.toContinuousLinearMap (B.coord i)) (B i))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (b.coord j (B i)) •
              F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F (LinearMap.toContinuousLinearMap (B.coord i)) (B i)
                = F (LinearMap.toContinuousLinearMap (B.coord i))
                    (∑ j : Fin (Module.finrank ℝ E), b.coord j (B i) • b j) := by
                  rw [show (∑ j : Fin (Module.finrank ℝ E), b.coord j (B i) • b j) = B i from
                    b.sum_repr (B i)]
            _ = ∑ j : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
                    F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            (b.coord j (B i)) •
              F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin (Module.finrank ℝ E), F
            (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
              LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin (Module.finrank ℝ E),
            F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

end NormedArmFields

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
