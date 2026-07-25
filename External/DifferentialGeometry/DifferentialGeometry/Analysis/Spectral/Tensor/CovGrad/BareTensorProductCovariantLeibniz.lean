import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Tensor.Multilinear.ModelProductContinuousBilinear
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitModelProdField_contMDiff (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        ((Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
              (unitModel (I := I) (M := M) g p S x)
              (unitModel (I := I) (M := M) g q T x)) :
            Tensor0SSpace (p + q) I x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (p + q)
  classical
  have hSfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x
        (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g p S x))) := by
    simpa only [Tensor0SSpace.ofModel_toModel, unitModel] using
      (contMDiff_unitEvalSection (I := I) (M := M) g p S)
  have hTfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SSpace q I z) x
        (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g q T x))) := by
    simpa only [Tensor0SSpace.ofModel_toModel, unitModel] using
      (contMDiff_unitEvalSection (I := I) (M := M) g q T)
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (unitModel (I := I) (M := M) g q T x)) :
          Tensor0SSpace (p + q) I x))).mpr ?_
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g p S x) :
      Tensor0SSpace p I x))).mp hSfield
  have hT := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g q T x) :
      Tensor0SSpace q I x))).mp hTfield
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := ∞)
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hS (τ ∘ Fin.castAdd q) x₀)).clm_apply
        (hT (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
      (unitModel (I := I) (M := M) g p S x) (unitModel (I := I) (M := M) g q T x))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

noncomputable def unitModelProdField (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ (p + q) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (p + q)
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SSpace.ofModel
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (unitModel (I := I) (M := M) g p S x) (unitModel (I := I) (M := M) g q T x)),
    unitModelProdField_contMDiff (I := I) g S T⟩

noncomputable def unitModelProdSection (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) :
    SmoothCcTensor g 0 (p + q) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (unitModelProdField (I := I) g S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitModelProdSection_unitModel (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M) :
    unitModel (I := I) (M := M) g (p + q) (unitModelProdSection (I := I) g S T) x =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (unitModel (I := I) (M := M) g p S x) (unitModel (I := I) (M := M) g q T x) := by
  rw [unitModel]
  rw [show (unitModelProdSection (I := I) g S T).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (unitModelProdField (I := I) g S T x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x) (unitModel (I := I) (M := M) g q T x))) = _
  rw [Tensor0SSpace.toModel_ofModel]

private def prodUnitEval (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) :
    Π b : M, Tensor0SSpace (p + q) I b :=
  fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (p + q) I b from
    (unitModelProdSection (I := I) g S T).toSection b) (unitTensor (I := I) (M := M) b)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma prodUnitEval_toModel (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (b : M) :
    Tensor0SSpace.toModel (prodUnitEval (I := I) g S T b) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (unitModel (I := I) (M := M) g p S b) (unitModel (I := I) (M := M) g q T b) := by
  have := unitModelProdSection_unitModel (I := I) g S T b
  rw [unitModel] at this
  exact this

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma prodUnitEval_eq_ofModel (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (b : M) :
    prodUnitEval (I := I) g S T b =
      Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S b) (unitModel (I := I) (M := M) g q T b)) := by
  rw [← prodUnitEval_toModel (I := I) g S T b, Tensor0SSpace.ofModel_toModel]

private def factorUnitEval (g : SmoothRiemannianMetric I M) {p : ℕ}
    (S : SmoothCcTensor g 0 p) : Π b : M, Tensor0SSpace p I b :=
  fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace p I b from S.toSection b)
    (unitTensor (I := I) (M := M) b)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma factorUnitEval_toModel (g : SmoothRiemannianMetric I M) {p : ℕ}
    (S : SmoothCcTensor g 0 p) (b : M) :
    Tensor0SSpace.toModel (factorUnitEval (I := I) g S b) =
      unitModel (I := I) (M := M) g p S b := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma modelProduct_compContinuousLinearMap_uniform (p q : ℕ)
    (f : Tensor0SModel p ℝ E) (h : Tensor0SModel q ℝ E) (φ : E →L[ℝ] E) :
    (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q f h).compContinuousLinearMap
        (fun _ : Fin (p + q) => φ) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (f.compContinuousLinearMap (fun _ : Fin p => φ))
        (h.compContinuousLinearMap (fun _ : Fin q => φ)) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartE_section_repr_ofModel {n : ℕ} (α : M) (f : M → Tensor0SModel n ℝ E)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    tensor0SChartE_section_repr (I := I) n α (fun y => Tensor0SSpace.ofModel (f y)) b =
      (f b).compContinuousLinearMap (fun _ : Fin n => trivFromE (I := I) α b) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensor0SChartE_section_repr_apply_tuple (I := I) (n := n) α
    (fun y => Tensor0SSpace.ofModel (f y)) hb v,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [Tensor0SSpace.ofModel, tensor0SSpace_continuousLinearEquiv_symm_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartE_section_repr_prodUnitEval (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    tensor0SChartE_section_repr (I := I) (p + q) α (prodUnitEval (I := I) g S T) b =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (tensor0SChartE_section_repr (I := I) p α (factorUnitEval (I := I) g S) b)
        (tensor0SChartE_section_repr (I := I) q α (factorUnitEval (I := I) g T) b) := by
  classical
  have hprod : (prodUnitEval (I := I) g S T) = fun y => Tensor0SSpace.ofModel
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (unitModel (I := I) (M := M) g p S y) (unitModel (I := I) (M := M) g q T y)) := by
    funext y; exact prodUnitEval_eq_ofModel (I := I) g S T y
  have hS : (factorUnitEval (I := I) g S) =
      fun y => Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g p S y) := by
    funext y; rw [← factorUnitEval_toModel (I := I) g S y, Tensor0SSpace.ofModel_toModel]
  have hT : (factorUnitEval (I := I) g T) =
      fun y => Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g q T y) := by
    funext y; rw [← factorUnitEval_toModel (I := I) g T y, Tensor0SSpace.ofModel_toModel]
  rw [hprod, hS, hT]
  rw [chartE_section_repr_ofModel (I := I) α _ hb,
    chartE_section_repr_ofModel (I := I) α _ hb,
    chartE_section_repr_ofModel (I := I) α _ hb]
  rw [modelProduct_compContinuousLinearMap_uniform (E := E) p q]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma prodUnitEval_chartPullback_eventuallyEq (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (α : M) {b : M}
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (tensor0SChartE_section_repr (I := I) (p + q) α (prodUnitEval (I := I) g S T) ∘
        (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E => Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        ((tensor0SChartE_section_repr (I := I) p α (factorUnitEval (I := I) g S) ∘
          (extChartAt I α).symm) y)
        ((tensor0SChartE_section_repr (I := I) q α (factorUnitEval (I := I) g T) ∘
          (extChartAt I α).symm) y)) := by
  classical
  set φ := extChartAt I α with hφ
  have hBase_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hb_inv : φ.symm (φ b) = b := φ.left_inv hb_src
  have hcont_symm : ContinuousAt φ.symm (φ b) :=
    continuousAt_extChartAt_symm' (I := I) (x := α) (x' := b) hb_src
  have hBase_pre : φ.symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 (φ b) := by
    have hmem : (φ.symm (φ b)) ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [hb_inv]; exact hb_base
    exact hcont_symm.preimage_mem_nhds (hBase_open.mem_nhds hmem)
  filter_upwards [hBase_pre] with y hyBase
  exact chartE_section_repr_prodUnitEval (I := I) g S T α hyBase

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fderiv_prodUnitEval_chartPullback (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (α : M) {b : M}
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hS : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) p α (factorUnitEval (I := I) g S) ∘
        (extChartAt I α).symm) (extChartAt I α b))
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) q α (factorUnitEval (I := I) g T) ∘
        (extChartAt I α).symm) (extChartAt I α b)) :
    fderiv ℝ
        (tensor0SChartE_section_repr (I := I) (p + q) α (prodUnitEval (I := I) g S T) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      (Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) p q).precompR E
          ((tensor0SChartE_section_repr (I := I) p α (factorUnitEval (I := I) g S) ∘
            (extChartAt I α).symm) (extChartAt I α b))
          (fderiv ℝ (tensor0SChartE_section_repr (I := I) q α (factorUnitEval (I := I) g T) ∘
            (extChartAt I α).symm) (extChartAt I α b))
        + (Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) p q).precompL E
          (fderiv ℝ (tensor0SChartE_section_repr (I := I) p α (factorUnitEval (I := I) g S) ∘
            (extChartAt I α).symm) (extChartAt I α b))
          ((tensor0SChartE_section_repr (I := I) q α (factorUnitEval (I := I) g T) ∘
            (extChartAt I α).symm) (extChartAt I α b)) := by
  classical
  rw [Filter.EventuallyEq.fderiv_eq
    (prodUnitEval_chartPullback_eventuallyEq (I := I) g S T α hb_src hb_base)]
  exact (Bundle.continuousMultilinearMap.hasFDerivAt_modelProduct (𝕜 := ℝ) (F := E) p q
    hS.hasFDerivAt hT.hasFDerivAt).fderiv

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_tensor0SChartFiberFromModel_self (s : ℕ) (x : M)
    (m : Tensor0SModel s ℝ E) :
    Tensor0SSpace.toModel (tensor0SChartFiberFromModel (I := I) s x x m) = m := by
  classical
  have h := DifferentialGeometry.Tensor.tensor0S_trivAt_symmL_eq_one_on_locality
    (I := I) s x (b := x) rfl (mem_chart_source H x) m
  apply ContinuousMultilinearMap.ext
  intro v
  have hcoe := congrFun (congrArg DFunLike.coe h) v
  rw [show Tensor0SSpace.toModel (tensor0SChartFiberFromModel (I := I) s x x m) =
      tensor0SSpace_continuousLinearEquiv s x (tensor0SChartFiberFromModel (I := I) s x x m)
      from rfl, tensor0SSpace_continuousLinearEquiv_apply]
  exact hcoe

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma factor_chartPullback_self (g : SmoothRiemannianMetric I M) {p : ℕ}
    (S : SmoothCcTensor g 0 p) (x : M) :
    (tensor0SChartE_section_repr (I := I) p x (factorUnitEval (I := I) g S) ∘
        (extChartAt I x).symm) (extChartAt I x x) =
      unitModel (I := I) (M := M) g p S x := by
  classical
  rw [Function.comp_apply]
  rw [show (extChartAt I x).symm (extChartAt I x x) = x from extChartAt_to_inv (I := I) x]
  rw [tensor0SChartE_section_repr]
  apply ContinuousMultilinearMap.ext
  intro v
  have h := DifferentialGeometry.Tensor.multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (I := I) p x (b := x) rfl (mem_chart_source H x)
    (show Bundle.continuousMultilinearMap ℝ p E (TangentSpace I) x from factorUnitEval (I := I) g S x)
  have hcoe := congrFun (congrArg DFunLike.coe h) v
  rw [← factorUnitEval_toModel (I := I) g S x]
  rw [show Tensor0SSpace.toModel (factorUnitEval (I := I) g S x) =
      tensor0SSpace_continuousLinearEquiv p x (factorUnitEval (I := I) g S x) from rfl,
    tensor0SSpace_continuousLinearEquiv_apply]
  exact hcoe

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_tensor0SIntrinsicChartCLM_self (s : ℕ) (x : M)
    (T : Π b : M, Tensor0SSpace s I b) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (tensor0SIntrinsicChartCLM (I := I) s x T x v) =
      fderiv ℝ (tensor0SChartE_section_repr (I := I) s x T ∘ (extChartAt I x).symm)
        (extChartAt I x x) v := by
  classical
  rw [tensor0SIntrinsicChartCLM_apply]
  rw [show trivToE (I := I) x x v = v from by
    rw [trivToE_self_eq_id (I := I) x]; rfl]
  rw [toModel_tensor0SChartFiberFromModel_self (I := I) s x]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma factorUnitEval_tensorSectionMDiffAt (g : SmoothRiemannianMetric I M) {p : ℕ}
    (S : SmoothCcTensor g 0 p) (x : M) :
    TensorSectionMDiffAt (I := I) p (factorUnitEval (I := I) g S) x := by
  classical
  have hHom : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel p ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel p ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w →L[ℝ] Tensor0SSpace p I w) z
        (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace p I z from S.toSection z)) x :=
    (S.toSection.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w) z (unitTensor (I := I) (M := M) z)) x :=
    (contMDiff_unitZeroSection (I := I) (M := M)).contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHom hv

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma prodUnitEval_tensorSectionMDiffAt (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M) :
    TensorSectionMDiffAt (I := I) (p + q) (prodUnitEval (I := I) g S T) x := by
  classical
  have hHom : MDifferentiableAt I
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (p + q) ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (p + q) ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w →L[ℝ] Tensor0SSpace (p + q) I w) z
        (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (p + q) I z from
          (unitModelProdSection (I := I) g S T).toSection z)) x :=
    ((unitModelProdSection (I := I) g S T).toSection.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w) z (unitTensor (I := I) (M := M) z)) x :=
    (contMDiff_unitZeroSection (I := I) (M := M)).contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHom hv

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_tensor0SIntrinsicChartCLM_prodUnitEval_self (g : SmoothRiemannianMetric I M)
    {p q : ℕ} (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (tensor0SIntrinsicChartCLM (I := I) (p + q) x (prodUnitEval (I := I) g S T) x v) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) p x (factorUnitEval (I := I) g S) x v))
          (unitModel (I := I) (M := M) g q T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) q x (factorUnitEval (I := I) g T) x v)) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  have hx_src : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  have hSdiff := differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt (I := I) p x
    (factorUnitEval (I := I) g S) hx_good (factorUnitEval_tensorSectionMDiffAt (I := I) g S x)
  have hTdiff := differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt (I := I) q x
    (factorUnitEval (I := I) g T) hx_good (factorUnitEval_tensorSectionMDiffAt (I := I) g T x)
  rw [toModel_tensor0SIntrinsicChartCLM_self (I := I) (p + q) x (prodUnitEval (I := I) g S T) v,
    toModel_tensor0SIntrinsicChartCLM_self (I := I) p x (factorUnitEval (I := I) g S) v,
    toModel_tensor0SIntrinsicChartCLM_self (I := I) q x (factorUnitEval (I := I) g T) v]
  rw [fderiv_prodUnitEval_chartPullback (I := I) g S T x hx_src hx_base hSdiff hTdiff]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, Bundle.continuousMultilinearMap.modelProductL_apply,
    factor_chartPullback_self (I := I) g S x, factor_chartPullback_self (I := I) g T x]
  exact add_comm _ _

private lemma fin_castAdd_ne_natAdd (p q : ℕ) (j : Fin p) (k : Fin q) :
    Fin.castAdd q j ≠ Fin.natAdd p k := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.castAdd, Fin.castLE, Fin.natAdd] at hv
  omega

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma localSlotCLM_castAdd_castAdd {b : M} (p q : ℕ) (k₀ : Fin p)
    (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) (j : Fin p) :
    localSlotCLM (I := I) (p + q) (Fin.castAdd q k₀) Φ (Fin.castAdd q j) =
      localSlotCLM (I := I) p k₀ Φ j := by
  by_cases hj : j = k₀
  · subst hj
    rw [localSlotCLM_self, localSlotCLM_self]
  · rw [localSlotCLM_other (I := I) (p + q) (Fin.castAdd q k₀) Φ
        (by intro h; exact hj (Fin.castAdd_injective p q h)),
      localSlotCLM_other (I := I) p k₀ Φ hj]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma localSlotCLM_castAdd_natAdd {b : M} (p q : ℕ) (k₀ : Fin p)
    (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) (j : Fin q) :
    localSlotCLM (I := I) (p + q) (Fin.castAdd q k₀) Φ (Fin.natAdd p j) =
      ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  rw [localSlotCLM_other (I := I) (p + q) (Fin.castAdd q k₀) Φ]
  intro h
  exact absurd h.symm (fin_castAdd_ne_natAdd p q k₀ j)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma localSlotCLM_natAdd_castAdd {b : M} (p q : ℕ) (k₀ : Fin q)
    (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) (j : Fin p) :
    localSlotCLM (I := I) (p + q) (Fin.natAdd p k₀) Φ (Fin.castAdd q j) =
      ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  rw [localSlotCLM_other (I := I) (p + q) (Fin.natAdd p k₀) Φ]
  intro h
  exact absurd h (fin_castAdd_ne_natAdd p q j k₀)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma localSlotCLM_natAdd_natAdd {b : M} (p q : ℕ) (k₀ : Fin q)
    (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) (j : Fin q) :
    localSlotCLM (I := I) (p + q) (Fin.natAdd p k₀) Φ (Fin.natAdd p j) =
      localSlotCLM (I := I) q k₀ Φ j := by
  by_cases hj : j = k₀
  · subst hj
    rw [localSlotCLM_self, localSlotCLM_self]
  · rw [localSlotCLM_other (I := I) (p + q) (Fin.natAdd p k₀) Φ
        (by intro h; exact hj (Fin.natAdd_injective q p h)),
      localSlotCLM_other (I := I) q k₀ Φ hj]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SSlotCorrection_prodUnitEval_apply (g : SmoothRiemannianMetric I M)
    {p q : ℕ} (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q)
    (X : Π b' : M, TangentSpace I b') (x : M) (k : Fin (p + q))
    (m : Fin (p + q) → TangentSpace I x) :
    Tensor0SSpace.toModel
        (chartTensor0SSlotCorrection (I := I) (p + q) g x (prodUnitEval (I := I) g S T) X x k) m =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (unitModel (I := I) (M := M) g p S x) (unitModel (I := I) (M := M) g q T x)
        (fun i => localSlotCLM (I := I) (p + q) k
          (chartLeviCivitaParallelCLM (I := I) g x x X) i (m i)) := by
  classical
  have h2 := chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (p + q) g x
    (prodUnitEval (I := I) g S T) X x k m
  calc Tensor0SSpace.toModel
        (chartTensor0SSlotCorrection (I := I) (p + q) g x (prodUnitEval (I := I) g S T) X x k) m
      = (chartTensor0SSlotCorrection (I := I) (p + q) g x (prodUnitEval (I := I) g S T) X x k :
          ContinuousMultilinearMap ℝ (fun _ : Fin (p + q) => TangentSpace I x) ℝ) m := by
        rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]; rfl
    _ = (prodUnitEval (I := I) g S T x :
          ContinuousMultilinearMap ℝ (fun _ : Fin (p + q) => TangentSpace I x) ℝ)
          (fun i => localSlotCLM (I := I) (p + q) k
            (chartLeviCivitaParallelCLM (I := I) g x x X) i (m i)) := h2
    _ = Tensor0SSpace.toModel (prodUnitEval (I := I) g S T x)
          (fun i => localSlotCLM (I := I) (p + q) k
            (chartLeviCivitaParallelCLM (I := I) g x x X) i (m i)) := by
        rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]; rfl
    _ = _ := by rw [prodUnitEval_toModel (I := I) g S T x]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SSlotCorrection_factorUnitEval_apply
    (g : SmoothRiemannianMetric I M) {p : ℕ} (S : SmoothCcTensor g 0 p)
    (X : Π b' : M, TangentSpace I b') (x : M) (k : Fin p) (m : Fin p → TangentSpace I x) :
    Tensor0SSpace.toModel
        (chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k) m =
      unitModel (I := I) (M := M) g p S x
        (fun i => localSlotCLM (I := I) p k
          (chartLeviCivitaParallelCLM (I := I) g x x X) i (m i)) := by
  classical
  have h2 := chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) p g x
    (factorUnitEval (I := I) g S) X x k m
  calc Tensor0SSpace.toModel
        (chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k) m
      = (chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k :
          ContinuousMultilinearMap ℝ (fun _ : Fin p => TangentSpace I x) ℝ) m := by
        rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]; rfl
    _ = (factorUnitEval (I := I) g S x :
          ContinuousMultilinearMap ℝ (fun _ : Fin p => TangentSpace I x) ℝ)
          (fun i => localSlotCLM (I := I) p k
            (chartLeviCivitaParallelCLM (I := I) g x x X) i (m i)) := h2
    _ = Tensor0SSpace.toModel (factorUnitEval (I := I) g S x)
          (fun i => localSlotCLM (I := I) p k
            (chartLeviCivitaParallelCLM (I := I) g x x X) i (m i)) := by
        rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]; rfl
    _ = _ := by rw [factorUnitEval_toModel (I := I) g S x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SSlotCorrection_sum_prodUnitEval (g : SmoothRiemannianMetric I M)
    {p q : ℕ} (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q)
    (X : Π b' : M, TangentSpace I b') (x : M) :
    Tensor0SSpace.toModel
        (∑ k : Fin (p + q),
          chartTensor0SSlotCorrection (I := I) (p + q) g x (prodUnitEval (I := I) g S T) X x k) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (∑ k : Fin p,
              chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k))
          (unitModel (I := I) (M := M) g q T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (∑ k : Fin q,
              chartTensor0SSlotCorrection (I := I) q g x (factorUnitEval (I := I) g T) X x k)) := by
  classical
  set Φ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    chartLeviCivitaParallelCLM (I := I) g x x X with hΦ
  apply ContinuousMultilinearMap.ext
  intro m

  rw [show Tensor0SSpace.toModel
        (∑ k : Fin (p + q),
          chartTensor0SSlotCorrection (I := I) (p + q) g x (prodUnitEval (I := I) g S T) X x k) =
      ∑ k : Fin (p + q),
        Tensor0SSpace.toModel
          (chartTensor0SSlotCorrection (I := I) (p + q) g x (prodUnitEval (I := I) g S T) X x k)
      from map_sum (tensor0SSpace_continuousLinearEquiv (p + q) x) _ _]
  rw [show Tensor0SSpace.toModel
        (∑ k : Fin p,
          chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k) =
      ∑ k : Fin p,
        Tensor0SSpace.toModel
          (chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k)
      from map_sum (tensor0SSpace_continuousLinearEquiv p x) _ _]
  rw [show Tensor0SSpace.toModel
        (∑ k : Fin q,
          chartTensor0SSlotCorrection (I := I) q g x (factorUnitEval (I := I) g T) X x k) =
      ∑ k : Fin q,
        Tensor0SSpace.toModel
          (chartTensor0SSlotCorrection (I := I) q g x (factorUnitEval (I := I) g T) X x k)
      from map_sum (tensor0SSpace_continuousLinearEquiv q x) _ _]
  rw [ContinuousMultilinearMap.add_apply]
  simp only [ContinuousMultilinearMap.sum_apply,
    toModel_chartTensor0SSlotCorrection_prodUnitEval_apply (I := I) g S T X x,
    toModel_chartTensor0SSlotCorrection_factorUnitEval_apply (I := I) g S X x,
    toModel_chartTensor0SSlotCorrection_factorUnitEval_apply (I := I) g T X x,
    Bundle.continuousMultilinearMap.modelProduct_apply, ← hΦ]
  rw [Fin.sum_univ_add, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun k₀ _ => ?_)
    have hSarg : ((fun i => localSlotCLM (I := I) (p + q) (Fin.castAdd q k₀) Φ i (m i)) ∘
          Fin.castAdd q) =
        (fun i => localSlotCLM (I := I) p k₀ Φ i (m (Fin.castAdd q i))) := by
      funext j
      rw [Function.comp_apply, localSlotCLM_castAdd_castAdd (I := I) p q k₀ Φ j]
    have hTarg : ((fun i => localSlotCLM (I := I) (p + q) (Fin.castAdd q k₀) Φ i (m i)) ∘
          Fin.natAdd p) = (fun i => m (Fin.natAdd p i)) := by
      funext j
      rw [Function.comp_apply, localSlotCLM_castAdd_natAdd (I := I) p q k₀ Φ j]
      rfl
    rw [hSarg, hTarg]
    simp only [Function.comp_def]
  · refine Finset.sum_congr rfl (fun k₀ _ => ?_)
    have hSarg : ((fun i => localSlotCLM (I := I) (p + q) (Fin.natAdd p k₀) Φ i (m i)) ∘
          Fin.castAdd q) = (fun i => m (Fin.castAdd q i)) := by
      funext j
      rw [Function.comp_apply, localSlotCLM_natAdd_castAdd (I := I) p q k₀ Φ j]
      rfl
    have hTarg : ((fun i => localSlotCLM (I := I) (p + q) (Fin.natAdd p k₀) Φ i (m i)) ∘
          Fin.natAdd p) =
        (fun i => localSlotCLM (I := I) q k₀ Φ i (m (Fin.natAdd p i))) := by
      funext j
      rw [Function.comp_apply, localSlotCLM_natAdd_natAdd (I := I) p q k₀ Φ j]
    rw [hSarg, hTarg]
    simp only [Function.comp_def]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SCovariantDerivative_eq_intrinsic_sub_slotSum
    (g : SmoothRiemannianMetric I M) {n : ℕ} (Y : Π b' : M, Tensor0SSpace n I b')
    (X : Π b' : M, TangentSpace I b') (x : M) (hY : TensorSectionMDiffAt (I := I) n Y x) :
    Tensor0SSpace.toModel
        (chartTensor0SCovariantDerivative (I := I) n g x Y X x) =
      Tensor0SSpace.toModel
          (tensor0SIntrinsicChartCLM (I := I) n x Y x (X x)) -
        Tensor0SSpace.toModel
          (∑ k : Fin n, chartTensor0SSlotCorrection (I := I) n g x Y X x k) := by
  classical
  cases n with
  | succ m =>
      rw [chartTensor0SCovariantDerivative_succ (I := I) m g x Y X x]
      exact map_sub (tensor0SSpace_continuousLinearEquiv (m + 1) x) _ _
  | zero =>
      have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
      rw [Finset.univ_eq_empty, Finset.sum_empty, Tensor0SSpace.toModel_zero, sub_zero]
      apply ContinuousMultilinearMap.ext
      intro m
      have hm : m = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact i.elim0
      subst hm
      rw [show Tensor0SSpace.toModel
              (chartTensor0SCovariantDerivative (I := I) 0 g x Y X x)
              (fun i : Fin 0 => Fin.elim0 i) =
            (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
              chartTensor0SCovariantDerivative (I := I) 0 g x Y X x)
              (fun i : Fin 0 => Fin.elim0 i) from rfl]
      rw [chartTensor0SCovariantDerivative_zero_apply (I := I) g x Y X x
        (fun i : Fin 0 => Fin.elim0 i)]
      rw [show Tensor0SSpace.toModel
              (tensor0SIntrinsicChartCLM (I := I) 0 x Y x (X x))
              (fun i : Fin 0 => Fin.elim0 i) =
            (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
              tensor0SIntrinsicChartCLM (I := I) 0 x Y x (X x))
              (fun i : Fin 0 => Fin.elim0 i) from rfl]
      rw [tensor0SIntrinsicChartCLM_zero_apply_empty_eq_mfderiv (I := I) x Y hx_good hY (X x)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SCovariantDerivative_factor_succ (g : SmoothRiemannianMetric I M)
    {s : ℕ} (S : SmoothCcTensor g 0 (s + 1)) (X : Π b' : M, TangentSpace I b') (x : M) :
    Tensor0SSpace.toModel
        (chartTensor0SCovariantDerivative (I := I) (s + 1) g x (factorUnitEval (I := I) g S) X x) =
      Tensor0SSpace.toModel
          (tensor0SIntrinsicChartCLM (I := I) (s + 1) x (factorUnitEval (I := I) g S) x (X x)) -
        Tensor0SSpace.toModel
          (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g x (factorUnitEval (I := I) g S) X x k) := by
  rw [chartTensor0SCovariantDerivative_succ (I := I) s g x (factorUnitEval (I := I) g S) X x]
  exact map_sub (tensor0SSpace_continuousLinearEquiv (s + 1) x) _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SCovariantDerivative_prodUnitEval_succ
    (g : SmoothRiemannianMetric I M) {p' q' : ℕ}
    (S : SmoothCcTensor g 0 (p' + 1)) (T : SmoothCcTensor g 0 (q' + 1))
    (X : Π b' : M, TangentSpace I b') (x : M) :
    Tensor0SSpace.toModel
        (chartTensor0SCovariantDerivative (I := I) ((p' + 1) + (q' + 1)) g x
          (prodUnitEval (I := I) g S T) X x) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (Tensor0SSpace.toModel
            (chartTensor0SCovariantDerivative (I := I) (p' + 1) g x (factorUnitEval (I := I) g S) X x))
          (unitModel (I := I) (M := M) g (q' + 1) T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (unitModel (I := I) (M := M) g (p' + 1) S x)
          (Tensor0SSpace.toModel
            (chartTensor0SCovariantDerivative (I := I) (q' + 1) g x
              (factorUnitEval (I := I) g T) X x)) := by
  classical
  rw [show chartTensor0SCovariantDerivative (I := I) ((p' + 1) + (q' + 1)) g x
        (prodUnitEval (I := I) g S T) X x =
      tensor0SIntrinsicChartCLM (I := I) ((p' + 1) + (q' + 1)) x
          (prodUnitEval (I := I) g S T) x (X x) -
        ∑ k : Fin ((p' + 1) + (q' + 1)),
          chartTensor0SSlotCorrection (I := I) ((p' + 1) + (q' + 1)) g x
            (prodUnitEval (I := I) g S T) X x k
      from rfl]
  rw [show Tensor0SSpace.toModel
        ((tensor0SIntrinsicChartCLM (I := I) ((p' + 1) + (q' + 1)) x
            (prodUnitEval (I := I) g S T) x) (X x) -
          ∑ k : Fin ((p' + 1) + (q' + 1)),
            chartTensor0SSlotCorrection (I := I) ((p' + 1) + (q' + 1)) g x
              (prodUnitEval (I := I) g S T) X x k) =
      Tensor0SSpace.toModel
          ((tensor0SIntrinsicChartCLM (I := I) ((p' + 1) + (q' + 1)) x
            (prodUnitEval (I := I) g S T) x) (X x)) -
        Tensor0SSpace.toModel
          (∑ k : Fin ((p' + 1) + (q' + 1)),
            chartTensor0SSlotCorrection (I := I) ((p' + 1) + (q' + 1)) g x
              (prodUnitEval (I := I) g S T) X x k)
      from map_sub (tensor0SSpace_continuousLinearEquiv ((p' + 1) + (q' + 1)) x) _ _]
  rw [toModel_tensor0SIntrinsicChartCLM_prodUnitEval_self (I := I) g S T x (X x)]
  rw [toModel_chartTensor0SSlotCorrection_sum_prodUnitEval (I := I) g S T X x]
  rw [toModel_chartTensor0SCovariantDerivative_factor_succ (I := I) g S X x,
    toModel_chartTensor0SCovariantDerivative_factor_succ (I := I) g T X x]

  rw [show Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
        (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) (p' + 1) x (factorUnitEval (I := I) g S) x (X x)) -
          Tensor0SSpace.toModel
            (∑ k : Fin (p' + 1),
              chartTensor0SSlotCorrection (I := I) (p' + 1) g x (factorUnitEval (I := I) g S) X x k))
        (unitModel (I := I) (M := M) g (q' + 1) T x) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) (p' + 1) x (factorUnitEval (I := I) g S) x (X x)))
          (unitModel (I := I) (M := M) g (q' + 1) T x) -
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (Tensor0SSpace.toModel
            (∑ k : Fin (p' + 1),
              chartTensor0SSlotCorrection (I := I) (p' + 1) g x (factorUnitEval (I := I) g S) X x k))
          (unitModel (I := I) (M := M) g (q' + 1) T x) from by
    rw [← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply]
    rw [map_sub, LinearMap.sub_apply]]
  rw [show Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
        (unitModel (I := I) (M := M) g (p' + 1) S x)
        (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) (q' + 1) x (factorUnitEval (I := I) g T) x (X x)) -
          Tensor0SSpace.toModel
            (∑ k : Fin (q' + 1),
              chartTensor0SSlotCorrection (I := I) (q' + 1) g x (factorUnitEval (I := I) g T) X x k)) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (unitModel (I := I) (M := M) g (p' + 1) S x)
          (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) (q' + 1) x (factorUnitEval (I := I) g T) x (X x))) -
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (unitModel (I := I) (M := M) g (p' + 1) S x)
          (Tensor0SSpace.toModel
            (∑ k : Fin (q' + 1),
              chartTensor0SSlotCorrection (I := I) (q' + 1) g x (factorUnitEval (I := I) g T) X x k))
        from by
    rw [← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply]
    rw [map_sub]]
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_chartTensor0SCovariantDerivative_prodUnitEval
    (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q)
    (X : Π b' : M, TangentSpace I b') (x : M) :
    Tensor0SSpace.toModel
        (chartTensor0SCovariantDerivative (I := I) (p + q) g x
          (prodUnitEval (I := I) g S T) X x) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (chartTensor0SCovariantDerivative (I := I) p g x (factorUnitEval (I := I) g S) X x))
          (unitModel (I := I) (M := M) g q T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (chartTensor0SCovariantDerivative (I := I) q g x
              (factorUnitEval (I := I) g T) X x)) := by
  classical
  rw [toModel_chartTensor0SCovariantDerivative_eq_intrinsic_sub_slotSum (I := I) g
    (prodUnitEval (I := I) g S T) X x (prodUnitEval_tensorSectionMDiffAt (I := I) g S T x)]
  rw [toModel_tensor0SIntrinsicChartCLM_prodUnitEval_self (I := I) g S T x (X x)]
  rw [toModel_chartTensor0SSlotCorrection_sum_prodUnitEval (I := I) g S T X x]
  rw [toModel_chartTensor0SCovariantDerivative_eq_intrinsic_sub_slotSum (I := I) g
    (factorUnitEval (I := I) g S) X x (factorUnitEval_tensorSectionMDiffAt (I := I) g S x),
    toModel_chartTensor0SCovariantDerivative_eq_intrinsic_sub_slotSum (I := I) g
    (factorUnitEval (I := I) g T) X x (factorUnitEval_tensorSectionMDiffAt (I := I) g T x)]
  rw [show Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) p x (factorUnitEval (I := I) g S) x (X x)) -
          Tensor0SSpace.toModel
            (∑ k : Fin p,
              chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k))
        (unitModel (I := I) (M := M) g q T x) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) p x (factorUnitEval (I := I) g S) x (X x)))
          (unitModel (I := I) (M := M) g q T x) -
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (∑ k : Fin p,
              chartTensor0SSlotCorrection (I := I) p g x (factorUnitEval (I := I) g S) X x k))
          (unitModel (I := I) (M := M) g q T x) from by
    rw [← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply]
    rw [map_sub, LinearMap.sub_apply]]
  rw [show Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (unitModel (I := I) (M := M) g p S x)
        (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) q x (factorUnitEval (I := I) g T) x (X x)) -
          Tensor0SSpace.toModel
            (∑ k : Fin q,
              chartTensor0SSlotCorrection (I := I) q g x (factorUnitEval (I := I) g T) X x k)) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (tensor0SIntrinsicChartCLM (I := I) q x (factorUnitEval (I := I) g T) x (X x))) -
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (∑ k : Fin q,
              chartTensor0SSlotCorrection (I := I) q g x (factorUnitEval (I := I) g T) X x k))
        from by
    rw [← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply,
      ← Bundle.continuousMultilinearMap.modelProductₗ_apply]
    rw [map_sub]]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensor0SCovariantDerivative_eq_abstract_gen
    (g : SmoothRiemannianMetric I M) {n : ℕ} (Y : Π b' : M, Tensor0SSpace n I b')
    (X : Π b' : M, TangentSpace I b') (x : M)
    (hY : TensorSectionMDiffAt (I := I) n Y x)
    (hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b' (X b')) x) :
    chartTensor0SCovariantDerivative (I := I) n g x Y X x =
      Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x (X x) := by
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  cases n with
  | succ m =>
      exact chartTensor0SCovariantDerivative_eq_abstract_succ_aux (I := I) (M := M) g x m Y X
        hx_good hY hX_at
  | zero =>
      exact chartTensor0SCovariantDerivative_eq_abstract_zero (I := I) (M := M) g x Y X hx_good

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma toModel_tensor0SCovariantDerivative_factorUnitEval_frame
    (g : SmoothRiemannianMetric I M) {s : ℕ} (W : SmoothCcTensor g 0 (s + 1))
    (X : Π b' : M, TangentSpace I b') (x : M)
    (hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b' (X b')) x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
          (factorUnitEval (I := I) g W) x (X x)) =
      Tensor0SSpace.toModel
        (chartTensor0SCovariantDerivative (I := I) (s + 1) g x (factorUnitEval (I := I) g W) X x) := by
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  rw [chartTensor0SCovariantDerivative_eq_abstract_succ_aux (I := I) (M := M) g x s
    (factorUnitEval (I := I) g W) X hx_good
    (factorUnitEval_tensorSectionMDiffAt (I := I) g W x) hX_at]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivUnitModel_prodUnitEval_frame (g : SmoothRiemannianMetric I M) {p' q' : ℕ}
    (S : SmoothCcTensor g 0 (p' + 1)) (T : SmoothCcTensor g 0 (q' + 1)) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M ((p' + 1) + (q' + 1)) (LeviCivita (I := I) g)
          (prodUnitEval (I := I) g S T) x
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (p' + 1) (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g S) x
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)))
          (unitModel (I := I) (M := M) g (q' + 1) T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (unitModel (I := I) (M := M) g (p' + 1) S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (q' + 1) (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g T) x
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x))) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  have hX_at := chartBasisVec_alpha_mdifferentiableAt (I := I) x i hx_good
  set Xf : Π b' : M, TangentSpace I b' :=
    DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i with hXf
  set P : Π b' : M, Tensor0SSpace ((p' + 1) + (q' + 1)) I b' := prodUnitEval (I := I) g S T with hP
  have hP_mdiff : TensorSectionMDiffAt (I := I) ((p' + 1) + (q' + 1)) P x := by
    rw [hP]; exact prodUnitEval_tensorSectionMDiffAt (I := I) g S T x

  have hprodaux : chartTensor0SCovariantDerivative (I := I) ((p' + 1) + (q' + 1)) g x P Xf x =
      Tensor0SNabla.tensor0SCovariantDerivative I M ((p' + 1) + (q' + 1)) (LeviCivita (I := I) g)
        P x (Xf x) :=
    chartTensor0SCovariantDerivative_eq_abstract_succ_aux (I := I) (M := M) g x
      (p' + 1 + q') P Xf (b := x) hx_good hP_mdiff hX_at
  rw [hP] at hprodaux
  rw [← hprodaux]
  rw [toModel_chartTensor0SCovariantDerivative_prodUnitEval_succ (I := I) g S T Xf x]
  rw [toModel_tensor0SCovariantDerivative_factorUnitEval_frame (I := I) g S Xf x hX_at,
    toModel_tensor0SCovariantDerivative_factorUnitEval_frame (I := I) g T Xf x hX_at]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma toModel_tensor0SCovariantDerivative_factorUnitEval_frame_gen
    (g : SmoothRiemannianMetric I M) {s : ℕ} (W : SmoothCcTensor g 0 s)
    (X : Π b' : M, TangentSpace I b') (x : M)
    (hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b' (X b')) x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
          (factorUnitEval (I := I) g W) x (X x)) =
      Tensor0SSpace.toModel
        (chartTensor0SCovariantDerivative (I := I) s g x (factorUnitEval (I := I) g W) X x) := by
  rw [chartTensor0SCovariantDerivative_eq_abstract_gen (I := I) g
    (factorUnitEval (I := I) g W) X x (factorUnitEval_tensorSectionMDiffAt (I := I) g W x) hX_at]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivUnitModel_prodUnitEval_frame_gen (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M (p + q) (LeviCivita (I := I) g)
          (prodUnitEval (I := I) g S T) x
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g S) x
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)))
          (unitModel (I := I) (M := M) g q T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g T) x
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x))) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  have hX_at := chartBasisVec_alpha_mdifferentiableAt (I := I) x i hx_good
  set Xf : Π b' : M, TangentSpace I b' :=
    DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i with hXf
  set P : Π b' : M, Tensor0SSpace (p + q) I b' := prodUnitEval (I := I) g S T with hP
  have hP_mdiff : TensorSectionMDiffAt (I := I) (p + q) P x := by
    rw [hP]; exact prodUnitEval_tensorSectionMDiffAt (I := I) g S T x
  have hprodaux : chartTensor0SCovariantDerivative (I := I) (p + q) g x P Xf x =
      Tensor0SNabla.tensor0SCovariantDerivative I M (p + q) (LeviCivita (I := I) g)
        P x (Xf x) :=
    chartTensor0SCovariantDerivative_eq_abstract_gen (I := I) g P Xf x hP_mdiff hX_at
  rw [hP] at hprodaux
  rw [← hprodaux]
  rw [toModel_chartTensor0SCovariantDerivative_prodUnitEval (I := I) g S T Xf x]
  rw [toModel_tensor0SCovariantDerivative_factorUnitEval_frame_gen (I := I) g S Xf x hX_at,
    toModel_tensor0SCovariantDerivative_factorUnitEval_frame_gen (I := I) g T Xf x hX_at]

omit [NeZero (Module.finrank ℝ E)] in
private lemma unitModel_covGrad_eq_tensor0SCovariantDerivative (g : SmoothRiemannianMetric I M)
    {s : ℕ} (W : SmoothCcTensor g 0 s) (x : M) (v : Fin (s + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s W) x v =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
          (factorUnitEval (I := I) g W) x (v 0))
        (Matrix.vecTail v) := by
  classical
  rw [unitModel]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s W).toSection x) (unitTensor (I := I) (M := M) x) =
      (covGrad (I := I) (M := M) g 0 s W).toSection x
        (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s W x
    (unitZeroSec (I := I) (M := M) x) v]
  rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s W x (v 0)]
  rw [tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g s
    W.toSection x (v 0)]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma modelProduct_finsum_smul_left {n m d : ℕ} (c : Fin d → ℝ)
    (A : Fin d → Tensor0SModel n ℝ E) (B : Tensor0SModel m ℝ E) :
    Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) n m (∑ i, c i • A i) B =
      ∑ i, c i • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) n m (A i) B := by
  classical
  rw [← Bundle.continuousMultilinearMap.modelProductL_apply, map_sum]
  simp only [map_smul, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
    Finset.sum_apply, Pi.smul_apply, Bundle.continuousMultilinearMap.modelProductL_apply]

omit [NeZero (Module.finrank ℝ E)] in
private lemma modelProduct_finsum_smul_right {n m d : ℕ} (c : Fin d → ℝ)
    (A : Tensor0SModel m ℝ E) (B : Fin d → Tensor0SModel n ℝ E) :
    Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m n A (∑ i, c i • B i) =
      ∑ i, c i • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m n A (B i) := by
  classical
  rw [← Bundle.continuousMultilinearMap.modelProductL_apply, map_sum]
  simp only [map_smul, Bundle.continuousMultilinearMap.modelProductL_apply]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivUnitModel_prodUnitEval (g : SmoothRiemannianMetric I M) {p' q' : ℕ}
    (S : SmoothCcTensor g 0 (p' + 1)) (T : SmoothCcTensor g 0 (q' + 1)) (x : M)
    (w : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M ((p' + 1) + (q' + 1)) (LeviCivita (I := I) g)
          (prodUnitEval (I := I) g S T) x w) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (p' + 1) (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g S) x w))
          (unitModel (I := I) (M := M) g (q' + 1) T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (unitModel (I := I) (M := M) g (p' + 1) S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (q' + 1) (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g T) x w)) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  have hxE : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => ((DifferentialGeometry.Integral.Measure.chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w)) i with hc

  have hdecomp : ∀ (n : ℕ) (Y : Π b' : M, Tensor0SSpace n I b'),
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x w) =
      ∑ i, c i • Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)) := by
    intro n Y
    conv_lhs => rw [chartBasisVecFiber_recompose (I := I) x hxE w]
    rw [map_sum (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x)]
    rw [← Tensor0SSpace.toModelL_apply, map_sum]
    simp only [map_smul, Tensor0SSpace.toModelL_apply, hc]
  rw [hdecomp ((p' + 1) + (q' + 1)) (prodUnitEval (I := I) g S T),
    hdecomp (p' + 1) (factorUnitEval (I := I) g S),
    hdecomp (q' + 1) (factorUnitEval (I := I) g T)]
  rw [modelProduct_finsum_smul_left, modelProduct_finsum_smul_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← smul_add, covDerivUnitModel_prodUnitEval_frame (I := I) g S T x i]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivUnitModel_prodUnitEval_gen (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M)
    (w : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M (p + q) (LeviCivita (I := I) g)
          (prodUnitEval (I := I) g S T) x w) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g S) x w))
          (unitModel (I := I) (M := M) g q T x) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g T) x w)) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_chartLeviCivitaGoodSet x
  have hxE : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => ((DifferentialGeometry.Integral.Measure.chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w)) i with hc
  have hdecomp : ∀ (n : ℕ) (Y : Π b' : M, Tensor0SSpace n I b'),
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x w) =
      ∑ i, c i • Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)) := by
    intro n Y
    conv_lhs => rw [chartBasisVecFiber_recompose (I := I) x hxE w]
    rw [map_sum (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g) Y x)]
    rw [← Tensor0SSpace.toModelL_apply, map_sum]
    simp only [map_smul, Tensor0SSpace.toModelL_apply, hc]
  rw [hdecomp (p + q) (prodUnitEval (I := I) g S T),
    hdecomp p (factorUnitEval (I := I) g S),
    hdecomp q (factorUnitEval (I := I) g T)]
  rw [modelProduct_finsum_smul_left, modelProduct_finsum_smul_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← smul_add, covDerivUnitModel_prodUnitEval_frame_gen (I := I) g S T x i]

omit [NeZero (Module.finrank ℝ E)] in
theorem unitModelProdSection_covGrad_unitModel (g : SmoothRiemannianMetric I M) {p' q' : ℕ}
    (S : SmoothCcTensor g 0 (p' + 1)) (T : SmoothCcTensor g 0 (q' + 1)) (x : M)
    (v : Fin ((p' + 1) + (q' + 1) + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g ((p' + 1) + (q' + 1) + 1)
        (covGrad (I := I) (M := M) g 0 ((p' + 1) + (q' + 1)) (unitModelProdSection (I := I) g S T))
        x v =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (p' + 1) (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g S) x (v 0)))
          (unitModel (I := I) (M := M) g (q' + 1) T x)
          (Matrix.vecTail v) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (p' + 1) (q' + 1)
          (unitModel (I := I) (M := M) g (p' + 1) S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (q' + 1) (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g T) x (v 0)))
          (Matrix.vecTail v) := by
  classical
  rw [unitModel_covGrad_eq_tensor0SCovariantDerivative (I := I) g
    (unitModelProdSection (I := I) g S T) x v]
  rw [show (factorUnitEval (I := I) g (unitModelProdSection (I := I) g S T)) =
      prodUnitEval (I := I) g S T from rfl]
  rw [covDerivUnitModel_prodUnitEval (I := I) g S T x (v 0)]
  rw [ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem unitModelProdSection_covGrad_unitModel_gen (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M)
    (v : Fin ((p + q) + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g ((p + q) + 1)
        (covGrad (I := I) (M := M) g 0 (p + q) (unitModelProdSection (I := I) g S T))
        x v =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g S) x (v 0)))
          (unitModel (I := I) (M := M) g q T x)
          (Matrix.vecTail v) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
              (factorUnitEval (I := I) g T) x (v 0)))
          (Matrix.vecTail v) := by
  classical
  rw [unitModel_covGrad_eq_tensor0SCovariantDerivative (I := I) g
    (unitModelProdSection (I := I) g S T) x v]
  rw [show (factorUnitEval (I := I) g (unitModelProdSection (I := I) g S T)) =
      prodUnitEval (I := I) g S T from rfl]
  rw [covDerivUnitModel_prodUnitEval_gen (I := I) g S T x (v 0)]
  rw [ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] in
private lemma unitModel_unitModelProdSection_covGrad_right (g : SmoothRiemannianMetric I M)
    {p q : ℕ} (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M)
    (v : Fin (p + (q + 1)) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (p + (q + 1))
        (unitModelProdSection (I := I) g S (covGrad (I := I) (M := M) g 0 q T)) x v =
      unitModel (I := I) (M := M) g p S x (v ∘ Fin.castAdd (q + 1)) *
        Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
            (factorUnitEval (I := I) g T) x (v (Fin.natAdd p 0)))
          (Matrix.vecTail (v ∘ Fin.natAdd p)) := by
  classical
  rw [unitModelProdSection_unitModel (I := I) g S (covGrad (I := I) (M := M) g 0 q T) x,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  rw [unitModel_covGrad_eq_tensor0SCovariantDerivative (I := I) g T x (v ∘ Fin.natAdd p)]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem unitModel_covGrad_unitForm (g : SmoothRiemannianMetric I M)
    {s : ℕ} (W : SmoothCcTensor g 0 s) (x : M) (v : Fin (s + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s W) x v =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
          (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            W.toSection y) (unitTensor (I := I) (M := M) y)) x (v 0))
        (Matrix.vecTail v) :=
  unitModel_covGrad_eq_tensor0SCovariantDerivative (I := I) g W x v

omit [NeZero (Module.finrank ℝ E)] in
theorem unitModelProdSection_covGrad_unitModel_pub (g : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g 0 p) (T : SmoothCcTensor g 0 q) (x : M)
    (v : Fin ((p + q) + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g ((p + q) + 1)
        (covGrad (I := I) (M := M) g 0 (p + q) (unitModelProdSection (I := I) g S T)) x v =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g)
              (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace p I y from
                S.toSection y) (unitTensor (I := I) (M := M) y)) x (v 0)))
          (unitModel (I := I) (M := M) g q T x)
          (Matrix.vecTail v) +
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (unitModel (I := I) (M := M) g p S x)
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
              (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace q I y from
                T.toSection y) (unitTensor (I := I) (M := M) y)) x (v 0)))
          (Matrix.vecTail v) :=
  unitModelProdSection_covGrad_unitModel_gen (I := I) g S T x v

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
