import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.BareTensorProductCovariantLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldContractionBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChartLeviCivitaParallelCLM
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Geometry.Metric.MetricBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem zeroTensor_eq_smul_unitTensor (x : M)
    (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • unitTensor (I := I) (M := M) x := by
  classical
  have hunit : Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor0s_clm_ext_unit {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitTensor (I := I) (M := M) x) = ψ (unitTensor (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unitTensor (I := I) (M := M) x D, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in

omit [T2Space M] [SigmaCompactSpace M] in
theorem smoothCcTensor_ext_of_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ}
    {S S' : SmoothCcTensor g 0 s}
    (h : ∀ x : M, unitModel (I := I) (M := M) g s S x = unitModel (I := I) (M := M) g s S' x) :
    S = S' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    have := h x
    simpa [unitModel] using this
  exact tensor0s_clm_ext_unit (I := I) (M := M) hval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in

private theorem unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  classical
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

end NormedSpaceModel

section NormedSpacePermutation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in

private theorem unitModel_castRankCc (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g 0 a) (x : M) :
    unitModel (I := I) (M := M) g b (h ▸ W) x =
      h ▸ unitModel (I := I) (M := M) g a W x := by
  subst h
  rfl

end NormedSpacePermutation

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrField_contMDiff (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ
              (unitModel (I := I) (M := M) g s S x)) :
            Tensor0SSpace s I x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  classical
  have hSfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g s S x))) := by
    simpa only [Tensor0SSpace.ofModel_toModel, unitModel] using
      (contMDiff_unitEvalSection (I := I) (M := M) g s S)
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (unitModel (I := I) (M := M) g s S x)) :
          Tensor0SSpace s I x))).mpr ?_
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g s S x) :
      Tensor0SSpace s I x))).mp hSfield
  intro τ x₀
  refine (hS (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr σ
      (unitModel (I := I) (M := M) g s S x))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

noncomputable def domDomCongrField (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S x)),
    domDomCongrField_contMDiff (I := I) g σ S⟩

noncomputable def domDomCongrSection (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (domDomCongrField (I := I) g σ S)
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrSection_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (domDomCongrSection (I := I) g σ S) x =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S x) := by
  rw [unitModel]
  rw [show (domDomCongrSection (I := I) g σ S).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (domDomCongrField (I := I) g σ S x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S x))) = _
  rw [Tensor0SSpace.toModel_ofModel]

end NormedSpaceModel

section NormedSpacePermutationNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGrad_unitModel_domDomCongrSection (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M, unitModel (I := I) (M := M) g (s + i)
          (iteratedCovGrad (I := I) (M := M) g 0 s i (domDomCongrSection (I := I) g σ S)) x =
        ContinuousMultilinearMap.domDomCongr σ'
          (unitModel (I := I) (M := M) g (s + i)
            (iteratedCovGrad (I := I) (M := M) g 0 s i S) x) :=
  exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M) g s σ S
    (domDomCongrSection (I := I) g σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g σ S y) i

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (S : SmoothCcTensor g 0 s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i (domDomCongrSection (I := I) g σ S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr (I := I) (M := M) g s σ S
    (domDomCongrSection (I := I) g σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g σ S y) i x

end NormedSpacePermutationNorm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
