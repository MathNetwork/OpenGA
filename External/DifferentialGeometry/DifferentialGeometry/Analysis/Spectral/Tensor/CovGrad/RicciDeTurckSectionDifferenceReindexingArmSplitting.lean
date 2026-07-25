import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceKoszulSecondCovGrad
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferencePrincipalEndomorphismTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceSymmetrizedReindexedCoeff


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

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

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_symmS_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) := by
  rw [ccTensor02Symm, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (c • Φ) W =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]


omit [NeZero (Module.finrank ℝ E)] in
theorem symmAbsorbedPrincipalCoeff_appCc_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (R₂ : SmoothCcTensor g₀ 4 2) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2, ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂'
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
        unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  classical

  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) S 2
  refine ⟨(1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ', fun x v => ?_⟩

  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [ccTensor02Symm, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (operatorFieldApply (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R₂ σ')
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huRein

  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        ((1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ')
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]

  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeff_appCc_eq (I := I) (M := M) g₀ R₂ σ'
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [hLHS, hRHS]

end InnerProductSpaceModel

section NormedSpaceReindexingModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def reindexCoeffFibGen (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x) :
    Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).toContinuousLinearMap))


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem reindexCoeffFibGen_apply (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x)
    (D : Tensor0SBundle.Tensor0SSpace r I x) :
    reindexCoeffFibGen (I := I) r s σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFibGen, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoeffFibGen_contMDiff (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
    (φ := fun x => reindexCoeffFibGen (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x))
  intro Y
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x t)
    (reindexCoeffFibGen_apply (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x) (Y x)).symm

noncomputable def reindexCoeffGen (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace r s I x from
          reindexCoeffFibGen (I := I) r s σ' x
            (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFibGen_contMDiff (I := I) (M := M) g₀ r s R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem reindexCoeffGen_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    (reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace r s I x from
        reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoeffGen_appCc_eq (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (R : SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r))
    (W W' : SmoothCcTensor g₀ 0 r)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ r W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ r W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ r 2 (reindexCoeffGen (I := I) (M := M) g₀ r 2 R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ r 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection]
  rw [reindexCoeffFibGen_apply (I := I) r 2 σ' x
    (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]
  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ r W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ r W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ r W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

end NormedSpaceReindexingModel

section NormedSpaceTensorCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connDiff_endpoint_cocycle (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have e₁ := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := fun y => σ y) hσ v
  have e₂ := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun y => σ y) hσ v
  have e₃ := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := fun y => σ y) hσ v
  rw [hσx] at e₁ e₂ e₃
  rw [e₁, e₂, e₃]
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appCc_smul_left_normed (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (c • Φ) W =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

noncomputable def symmAbsorbedCoeff (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i))) : SmoothCcTensor g₀ (2 + i) 2 :=
  (1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ'


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem symmAbsorbedCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (S : SmoothCcTensor g₀ 0 2) (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i)))
    (hσ' : ∀ x : M, unitModel (I := I) (M := M) g₀ (2 + i)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S)) x =
      ContinuousMultilinearMap.domDomCongr σ'
        (unitModel (I := I) (M := M) g₀ (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i S) x))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2 (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ')
          (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2 R
          (iteratedCovGrad (I := I) g₀ 0 2 i (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  classical
  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 i (ccTensor02Symm (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [ccTensor02Symm, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]
  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2 R (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2
      (reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
      (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huRein
  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2
        ((1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
        (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left_normed, appCc_smul_left_normed, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]
  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeffGen_appCc_eq (I := I) (M := M) g₀ (2 + i) R σ'
        (iteratedCovGrad (I := I) g₀ 0 2 i S)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i (ccTensor02Symm (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [symmAbsorbedCoeff, hLHS, hRHS]

end NormedSpaceTensorCoefficients

section InnerProductSpaceTensorCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem inverseMetricSharpFib_sub_inner_g1
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      cotangentToDualLinear (I := I) (x := x) α w
        - g₁.inner x (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [map_sub, ContinuousLinearMap.sub_apply,
      inverseMetricSharpFib_inner (I := I) g₁ x α w]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
theorem inverseMetricSharpFib_sub_inner_g1_realize
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (x : M) (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      - ccTensorBilinSymm (I := I) g₀ (T - T') x
          (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [inverseMetricSharpFib_sub_inner_g1 (I := I) g₁ g₁' x α w]
  rw [← inverseMetricSharpFib_inner (I := I) g₁' x α w]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁' x α with hu
  rw [hg₁' x u w, hg₁ x u w]
  have hbsub : ∀ (a c : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x a c =
        smoothCcTensorBilinForm (I := I) g₀ T x a c - smoothCcTensorBilinForm (I := I) g₀ T' x a c := by
    intro a c
    rw [show T - T' = T + (-1 : ℝ) • T' from by rw [neg_one_smul]; abel,
      ccTensorBilin_add (I := I) (M := M) g₀ T ((-1 : ℝ) • T') x a c,
      ccTensorBilin_smul (I := I) (M := M) g₀ (-1 : ℝ) T' x a c]
    ring
  have hsub : ccTensorBilinSymm (I := I) g₀ (T - T') x u w =
      ccTensorBilinSymm (I := I) g₀ T x u w - ccTensorBilinSymm (I := I) g₀ T' x u w := by
    rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
      hbsub u w, hbsub w u]
    ring
  rw [hsub]; ring


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cotangentCov_leviCivita_diff_endpoint
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₁')).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v) := by
  have h1 := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ v w
  have h1' := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁' hθ v w

  have hcocycle : PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v := by
    classical
    set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
    have hY := smoothExtensionTangent_mdiff (I := I) x w x
    have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
    have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
    have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
    rw [hYx] at e1 e2 e3
    rw [e1, e2, e3]; abel
  rw [hcocycle, map_sub]
  linarith [h1, h1']


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem oArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
        - inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
          - inverseMetricSharpFib (I := I) g₁' x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)))
        + inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
              - dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) := by
  rw [map_sub]
  abel


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem oArm_leg_eq_connDiff (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
        - dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁')).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir) =
      dualToCotangent (I := I)
        (-((cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₁' x).flip dir)).toLinearMap) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁' Z Y x
  rw [← dualToCotangent_subC]
  congr 1
  ext w
  have hbridge := cotangentCov_leviCivita_diff_endpoint (I := I) (M := M) g₀ g₁ g₁' hθ dir w
  rw [LinearMap.sub_apply]
  simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_coe]
  exact hbridge


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connDiff_bilinear_diff_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (a a' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x a dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x a' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (a - a') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x a' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x a' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem quadArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (q q' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x q dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x q' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q - q') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x q' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x q' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel


omit [NeZero (Module.finrank ℝ E)] in
theorem combinedLowerArm_extension_free
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2,
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                          ((chartModelBasis E) i)))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
          ) + (
        (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x (v 0),
                                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))) i)
            - (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                                smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x (v 0) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
          ) + (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i))
        + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
              (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')
              (⟨smoothExtensionTangent (I := I) x (v 0),
                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
              (⟨smoothExtensionTangent (I := I) x (v 1),
                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x
            - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')
                (⟨smoothExtensionTangent (I := I) x (v 0),
                  smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                (⟨smoothExtensionTangent (I := I) x (v 1),
                  smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x)) =
        ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1)
          - unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂'
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₂', hR₂'⟩ := symmAbsorbedPrincipalCoeff_appCc_eq (I := I) (M := M) g₀ (T - T')
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
  refine ⟨R₂', fun x v => ?_⟩
  set Zv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0), smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
    with hZv
  set Yw : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1), smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩
    with hYw
  have hZvx : Zv x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYwx : Yw x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  have hcons : (![v 0, v 1] : Fin 2 → TangentSpace I x) = v := by
    funext k; fin_cases k <;> rfl

  have htel : ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i) := by
    have h₁ := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x (v 0) (v 1)
    have h₁' := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁' x (v 0) (v 1)
    rw [show ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
        (ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1))
          - (ricciTensor (I := I) g₁' x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1)) from by
      ring]
    rw [h₁, h₁']

  have hgradX : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁'
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁'
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ Yw Zv x)
  have hgradZ : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁' (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁' Zv Yw
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ x)

  have hregroup :
      ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x (v 0),
                          smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                      ((chartModelBasis E) i)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
        ) + (
      (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i))
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
        ) := by
    rw [htel]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [← Finsupp.sub_apply, ← Finsupp.add_apply, ← map_sub, ← map_add]
    refine congrArg (fun t => (chartModelBasis E).repr t i) ?_
    rw [hgradX i, hgradZ i]
    simp only [hZv, hYw, ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]
    abel

  have hPX := palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' hg₁ hg₁' Zv Yw x
  have hPZ := palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' Zv Yw x
  have hR₂'v := hR₂' x v
  rw [hZvx, hYwx, hcons] at hPX hPZ
  have huXZ : unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v
      - unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v =
        unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v := by
    rw [show ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁ =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          + (-1 : ℝ) • ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁ from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring

  have hP :
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)) =
        unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂'
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
          + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T') Zv Yw x
              - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                  (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T') Zv Yw x) := by
    rw [hPX, hPZ, hR₂'v]
    linarith [huXZ]
  rw [hregroup]
  simp only [← hZv, ← hYw]
  linarith [hP]


def lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((g₁'.inner x (v + v')).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = (g₁'.inner x v).toLinearMap + (g₁'.inner x v').toLinearMap := by
          ext w; simp [map_add]
        rw [h, dualToCotangent_addC]
      map_smul' := fun c v => by
        have h : ((g₁'.inner x (c • v)).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = c • (g₁'.inner x v).toLinearMap := by
          ext w; simp [map_smul]
        rw [h, dualToCotangent_smulC]; rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma lowerFlatCLM_apply (g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    lowerFlatCLM (I := I) g₁' x v =
      dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap := by
  rw [lowerFlatCLM, LinearMap.coe_toContinuousLinearMap']; rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma cotangentToDual_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) (lowerFlatCLM (I := I) g₁' x v) w = g₁'.inner x v w := by
  rw [lowerFlatCLM_apply, cotangentToDual_dualToCotangent]; rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma inverseMetricSharpFib_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v) = v := by
  have hkey : (g₁'.inner x (inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v)) :
        TangentSpace I x →L[ℝ] ℝ) = g₁'.inner x v := by
    ext w
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_lowerFlatCLM]

  have hinj : Function.Injective
      (fun u : TangentSpace I x => (g₁'.inner x u : TangentSpace I x →L[ℝ] ℝ)) := by
    intro a b hab
    have hval : ∀ w, g₁'.inner x a w = g₁'.inner x b w := fun w => by
      have := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ w) hab
      simpa using this
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := g₁'.pos x (a - b) hsub
    have hzero : g₁'.inner x (a - b) (a - b) = 0 := by
      have hsymm₁ : g₁'.inner x (a - b) (a - b)
          = g₁'.inner x (a - b) a - g₁'.inner x (a - b) b := by rw [← map_sub]
      rw [hsymm₁, g₁'.symm x (a - b) a, g₁'.symm x (a - b) b]
      have e1 : g₁'.inner x a (a - b) = g₁'.inner x b (a - b) := hval (a - b)
      rw [e1]; ring
    exact absurd hzero (ne_of_gt hpos)
  exact hinj hkey


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁'.inner x v).toLinearMap := by
  rw [inverseMetricSharpFib_apply, lowerFlatCLM_apply]
  rw [show cotangentToDualLinear (I := I)
        (dualToCotangent (I := I) (g₁'.inner x v).toLinearMap)
        = (g₁'.inner x v).toLinearMap from by
    rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]]

def combinedLowerRaisedEndo0 (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (lowerFlatCLM (I := I) g₁' x)
    - ContinuousLinearMap.id ℝ (TangentSpace I x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma combinedLowerRaisedEndo0_apply (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) - v := by
  rw [combinedLowerRaisedEndo0, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma combinedLowerRaisedEndo0_self (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁' g₁' x v = 0 := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM, sub_self]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma combinedLowerRaisedEndo0_eq_metricSharp_flatDiff
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp]
  have hv : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁.inner x v).toLinearMap = v := by
    rw [← inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp (I := I) g₁ g₁ x v]
    exact inverseMetricSharpFib_lowerFlatCLM (I := I) g₁ x v
  have hsharp_sub : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁'.inner x v).toLinearMap
        - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁.inner x v).toLinearMap := by
    rw [DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_sub]
  rw [hsharp_sub, hv]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem metricFlat_chartComponent_contMDiffOn_local (g : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (g.inner b (Y b)).toLinearMap
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h_total : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g.inner b (Y b)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) γ).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g.contMDiff.contMDiffOn Y.contMDiff.contMDiffOn
      (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn (I := I) γ j)
  have hbase_eq :
      (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I) γ
  rw [hbase_eq] at h_total
  intro b hb
  have hpb := h_total b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem metricFlatDiff_chartComponent_contMDiffOn_local (g₁ g₁' : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap)
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h0 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁' Y γ j
  have h1 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁ Y γ j
  refine (h0.sub h1).congr ?_
  intro b hb
  rw [LinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem combinedLowerRaisedEndo0_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ b
          ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap))) := by
    apply DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlatDiff_chartComponent_contMDiffOn_local (I := I) g₁ g₁' Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [combinedLowerRaisedEndo0_eq_metricSharp_flatDiff (I := I) g₁ g₁' x (Y x)]

set_option backward.isDefEq.respectTransparency false in

def lowerSlotInsert0Fib (x : M) (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))
      map_add' := fun A A' => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_add]
        ext m
        simp
      map_smul' := fun c A => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_smul,
          RingHom.id_apply]
        ext m
        simp }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma lowerSlotInsert0Fib_apply_eval (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) m =
      Tensor0SSpace.toModel A (Function.update m 0 (Λ (m 0))) := by
  rw [lowerSlotInsert0Fib, LinearMap.coe_toContinuousLinearMap']
  change (Tensor0SSpace.toModel ((Tensor0SSpace.ofModel
      ((Tensor0SSpace.toModel A).compContinuousLinearMap
        (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))) :
      Tensor0SSpace 2 I x)) m = _
  rw [Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin 2 =>
      (if i = 0 then Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m 0 (Λ (m 0)) := by
    funext i
    by_cases h : i = 0
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne h]; rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma lowerSlotInsert0Fib_curry (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) :
    lowerSlotInsert0Fib (I := I) (M := M) x Λ A =
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ) := by
  have hcurry : Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) =
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ := by
    apply ContinuousLinearMap.ext
    intro v0
    apply Tensor0SSpace.toModel_injective (I := I)
    ext vt
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M),
      lowerSlotInsert0Fib_apply_eval, ContinuousLinearMap.comp_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)]
    congr 1
    rw [Fin.cons_zero, Fin.update_cons_zero]
  rw [← hcurry, ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in

def combinedLowerCoeff0Fib (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lowerSlotInsert0Fib (I := I) (M := M) x (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma combinedLowerCoeff0Fib_apply_eval (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (combinedLowerCoeff0Fib (I := I) g₁ g₁' x A) m =
      Tensor0SSpace.toModel A
        (Function.update m 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (m 0))) := by
  rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_apply_eval]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem combinedLowerCoeff0Fib_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (Tensor0SBundle.TensorRSSpace.ofCLM (combinedLowerCoeff0Fib (I := I) g₁ g₁' x))) := by
  set φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x with hφdef
  have hφ := combinedLowerRaisedEndo0_contMDiff (I := I) g₁ g₁'
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x => combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      (combinedLowerCoeff0Fib (I := I) g₁ g₁' x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)))) := by
    funext x
    rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_curry]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x))) :=
    fun x => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (φ := fun x => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x) (φ x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (φ x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hφ Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) hG

noncomputable def combinedLowerCoeff0 (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
      contMDiff_toFun := combinedLowerCoeff0Fib_contMDiff (I := I) g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem combinedLowerCoeff0_toSection (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x) := rfl


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem combinedLowerCoeff0_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁') W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
        (Function.update v 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (v 0))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [combinedLowerCoeff0_toSection]
  rw [combinedLowerCoeff0Fib_apply_eval]
  rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connDiff_g1g1'_order_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Y x) (X x) =
      (inverseMetricSharpFib (I := I) g₁ x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x)
          - inverseMetricSharpFib (I := I) g₁' x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x))
        + inverseMetricSharpFib (I := I) g₁' x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x (Y x) (X x)]
  rw [connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x,
      connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁' X Y x]
  rw [map_sub (inverseMetricSharpFib (I := I) g₁' x)]
  abel


omit [NeZero (Module.finrank ℝ E)] in
theorem order1CocycleLeg_flat_eq_explicit
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (hbil' : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = g₁'.inner b u w - g₀.inner b u w)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    g₁'.inner x
        (inverseMetricSharpFib (I := I) g₁' x
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
            - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x)) ζ =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ (S - S')
            (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
            (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
            (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          + covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          - covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              x) := by
  classical
  set Xe : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩ with hXe
  set Ye : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩ with hYe
  set Ze : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩ with hZe
  have hXex : Xe x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hYex : Ye x = Y x := smoothExtensionTangent_eq (I := I) x (Y x)
  have hZex : Ze x = ζ := smoothExtensionTangent_eq (I := I) x ζ

  rw [inverseMetricSharpFib_inner (I := I) g₁' x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
          - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ,
      cotangentToDualLinear_apply,
      show cotangentToDual (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ =
          cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ
            - cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ from by
        rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
            ← cotangentToDualLinear_apply, map_sub, LinearMap.sub_apply]]

  rw [show ζ = Ze x from hZex.symm]
  rw [koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil X Y Ze x,
      koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁' S' hbil' X Y Ze x]

  have hcg : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      covGradEval (I := I) (M := M) g₀ S P Q R x
          - covGradEval (I := I) (M := M) g₀ S' P Q R x =
        covGradEval (I := I) (M := M) g₀ (S - S') P Q R x := by
    intro P Q R
    simp only [covGradEval]
    rw [covGrad_sub (I := I) (M := M) g₀ 0 2 S S', SmoothCcTensor.toSection_sub]
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
        Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  have hval : ∀ (W : SmoothCcTensor g₀ 0 2)
      (P₁ P₂ Q₁ Q₂ R₁ R₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      P₁ x = P₂ x → Q₁ x = Q₂ x → R₁ x = R₂ x →
        covGradEval (I := I) (M := M) g₀ W P₁ Q₁ R₁ x =
          covGradEval (I := I) (M := M) g₀ W P₂ Q₂ R₂ x := by
    intro W P₁ P₂ Q₁ Q₂ R₁ R₂ hP hQ hR
    simp only [covGradEval, hP, hQ, hR]

  have eXY := (hcg X Y Ze).trans (hval (S - S') X Xe Y Ye Ze Ze hXex.symm hYex.symm rfl)
  have eYX := (hcg Y X Ze).trans (hval (S - S') Y Ye X Xe Ze Ze hYex.symm hXex.symm rfl)
  have eZXY := (hcg Ze X Y).trans (hval (S - S') Ze Ze X Xe Y Ye rfl hXex.symm hYex.symm)
  linarith [eXY, eYX, eZXY]

noncomputable def ricciArmSubleadingCoeff (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
    - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁'
        - ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁')


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
theorem ricciArmSubleadingCoeff_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciArmSubleadingCoeff (I := I) (M := M) g₀ g₁ g₁') W) x v =
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) -
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁' x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) := by
  classical
  have hsub : ∀ (A B : SmoothCcTensor g₀ 4 2),
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (A - B) W) x v =
        unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 A W) x v -
          unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 B W) x v := by
    intro A B
    rw [show A - B = A + (-1 : ℝ) • B from by rw [neg_one_smul]; abel,
      appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply, neg_one_smul]
    rw [← sub_eq_add_neg]
  rw [ricciArmSubleadingCoeff, hsub, hsub, hsub,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v]

end InnerProductSpaceTensorCoefficients

section NormedCurvatureCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def ricciArmOrder0CurvCoeffFibSlot (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 k x (ricEndoRaisedFib (I := I) g₁ x)

noncomputable def ricciArmOrder0CurvCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 0 x +
    ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 1 x


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem ricciArmOrder0CurvCoeffFibSlot_toModel (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update v k (ricEndoRaisedFib (I := I) g₁ x (v k))) := by
  rw [ricciArmOrder0CurvCoeffFibSlot]
  exact slotInsertEndoFib_apply_eval (I := I) (M := M) 2 k x
    (ricEndoRaisedFib (I := I) g₁ x) D v


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem ricciArmOrder0CurvCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmOrder0CurvCoeffFib (I := I) g₁ x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [ricciArmOrder0CurvCoeffFib, ContinuousLinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciArmOrder0CurvCoeffFibSlot_contMDiff (g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))) := by
  exact slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 k
    (fun x : M => ricEndoRaisedFib (I := I) g₁ x)
    (ricEndoRaisedFib_contMDiff (I := I) g₁)

noncomputable def ricciArmOrder0CurvCoeffSlot (g₀ g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))
      contMDiff_toFun := ricciArmOrder0CurvCoeffFibSlot_contMDiff (I := I) g₁ k }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem ricciArmOrder0CurvCoeffSlot_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ k).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x)) := rfl

noncomputable def ricciArmOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 +
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1


omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem ricciArmOrder0CurvCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) := by
  rw [ricciArmOrder0CurvCoeff, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ricciArmOrder0CurvCoeffSlot_toSection, ricciArmOrder0CurvCoeffSlot_toSection]
  rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) =
      ricciArmOrder0CurvCoeffFib (I := I) g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeffFib_toModel]
  rfl

end NormedCurvatureCoeff

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
