import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorRSMetricCompatible
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open TensorMetricLowering
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] in
lemma separableFormAt_zero
    (g : SmoothRiemannianMetric I M) (x : M) (w : Fin 0 → E) :
    separableFormAt (I := I) (M := M) g x 0 w =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [separableFormAt_apply]
  simp

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma lowerAllUpperIndices_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    lowerAllUpperIndices (I := I) (M := M) g r s x T = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact lowerAllUpperIndices_injective (I := I) (M := M) g r s x
      (h.trans (map_zero _).symm)
  · rw [h, map_zero]

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma finrank_tensor0SModel_eq (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) = (Module.finrank ℝ E) ^ n := by
  exact finrank_continuousMultilinearMap (𝕜 := ℝ) (F := E) n

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma finrank_tensorRSModel_eq_finrank_tensor0SModel (r s : ℕ) :
    Module.finrank ℝ (TensorRSModel r s ℝ E) =
      Module.finrank ℝ (Tensor0SModel (r + s) ℝ E) := by
  rw [finrank_tensorRSModel, finrank_tensor0SModel_eq]

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem lowerAllUpperIndices_bijective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Function.Bijective (lowerAllUpperIndices (I := I) (M := M) g r s x) := by
  refine ⟨lowerAllUpperIndices_injective (I := I) (M := M) g r s x, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_tensorRSModel_eq_finrank_tensor0SModel (E := E) r s)).mp
    (lowerAllUpperIndices_injective (I := I) (M := M) g r s x)

def lowerAllUpperIndicesEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    TensorRSModel r s ℝ E ≃L[ℝ] Tensor0SModel (r + s) ℝ E :=
  (LinearEquiv.ofBijective
      (lowerAllUpperIndices (I := I) (M := M) g r s x).toLinearMap
      (lowerAllUpperIndices_bijective (I := I) (M := M) g r s x)).toContinuousLinearEquiv

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

@[simp]
lemma lowerAllUpperIndicesEquiv_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x T =
      lowerAllUpperIndices (I := I) (M := M) g r s x T := rfl

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma lowerAllUpperIndicesEquiv_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ((lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x :
        TensorRSModel r s ℝ E →L[ℝ] Tensor0SModel (r + s) ℝ E)) =
      lowerAllUpperIndices (I := I) (M := M) g r s x := by
  ext T
  rfl

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

@[simp]
lemma lowerAllUpperIndicesEquiv_symm_apply_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).symm
        (lowerAllUpperIndices (I := I) (M := M) g r s x T) = T := by
  have h := (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).symm_apply_apply T
  rwa [lowerAllUpperIndicesEquiv_apply] at h

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

@[simp]
lemma lowerAllUpperIndicesEquiv_apply_symm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (U : Tensor0SModel (r + s) ℝ E) :
    lowerAllUpperIndices (I := I) (M := M) g r s x
        ((lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).symm U) = U := by
  have h := (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).apply_symm_apply U
  rwa [lowerAllUpperIndicesEquiv_apply] at h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma toModel_liftedTensorSection_eq_equiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y) =
      lowerAllUpperIndicesEquiv (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (S y)) := by
  rw [toModel_liftedTensorSection, lowerAllUpperIndicesEquiv_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma toModel_eq_symm_liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    TensorRSSpace.toModel (S y) =
      (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s y).symm
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y)) := by
  rw [toModel_liftedTensorSection_eq_equiv,
    ContinuousLinearEquiv.symm_apply_apply]

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] in

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma contMDiff_unitZeroSection :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
  rw [← contMDiff_scalarFn_iff_section (I := I) (M := M)]
  rw [scalarFn_unitZero (I := I) (M := M)]
  exact contMDiff_const

omit [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma toModel_tensorRS_apply
    (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) (D : Tensor0SSpace r I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) D) =
      TensorRSSpace.toModel T (Tensor0SSpace.toModel D) := by
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) D) =
    ((tensor0SSpace_continuousLinearEquiv (I := I) r x).arrowCongr
        (tensor0SSpace_continuousLinearEquiv (I := I) s x) T)
      (Tensor0SSpace.toModel D)
  rw [ContinuousLinearEquiv.arrowCongr_apply]
  have hD : (tensor0SSpace_continuousLinearEquiv (I := I) r x).symm
      (Tensor0SSpace.toModel D) = D :=
    (tensor0SSpace_continuousLinearEquiv (I := I) r x).symm_apply_apply D
  rw [hD]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma toModel_tensorRS_comp_apply
    (r s : ℕ) (x : M)
    (A : Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace s I x)
    (B : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (r + 1) I x)
    (D : Tensor0SModel r ℝ E) :
    TensorRSSpace.toModel
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from A.comp B) D =
      TensorRSSpace.toModel (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace s I x from A)
        (Tensor0SSpace.toModel (B (Tensor0SSpace.ofModel D))) := by
  have h1 := toModel_tensorRS_apply (I := I) (M := M) (r + 1) s x A (B (Tensor0SSpace.ofModel D))
  have h2 := toModel_tensorRS_apply (I := I) (M := M) r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from A.comp B) (Tensor0SSpace.ofModel D)
  rw [Tensor0SSpace.toModel_ofModel] at h2
  rw [← h2, ContinuousLinearMap.comp_apply, h1]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma liftedTensorSection_zero_eq_apply_unit
    (g : SmoothRiemannianMetric I M)
    (S : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (0 + 2) I y from S y)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) =
      liftedTensorSection (I := I) (M := M) g 0 2 S y := by
  refine Tensor0SSpace.toModel_injective ?_
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (0 + 2) I y from S y)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) =
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 2 S y)
  rw [toModel_liftedTensorSection]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 2 y (S y)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [lowerAllUpperIndices_apply]
  rw [separableFormAt_zero]
  congr 1
  funext j
  exact congrArg u (Fin.ext (by simp))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweredCovDerivAt_eq_lower_tensorCovDerivAt
    (g : SmoothRiemannianMetric I M)
    (S : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) S x v)) := by
  classical
  let unitSec : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
    ⟨fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
      contMDiff_unitZeroSection (I := I) (M := M)⟩
  have hcoe : (fun y : M => unitSec y) =
      fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hunit_model : Tensor0SSpace.toModel (unitSec x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    change Tensor0SSpace.toModel (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = _
    rw [Tensor0SSpace.toModel_ofModel]
  have hlowerA :
      lowerAllUpperIndices (I := I) (M := M) g 0 2 x
          (TensorRSSpace.toModel
            (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) S x v)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) S x v)
            (unitSec x)) := by
    rw [toModel_tensorRS_apply (I := I) (M := M) 0 2 x
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) S x v) (unitSec x)]
    rw [hunit_model]
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [lowerAllUpperIndices_apply, separableFormAt_zero]
    congr 1
    funext j
    exact congrArg u (Fin.ext (by simp))
  rw [hlowerA]
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 2
    (LeviCivita (I := I) g) S unitSec x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitSec y) x v) = 0 from by
    rw [hcoe]
    exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]
  rw [loweredCovDerivAt_def]
  have hsec : (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (0 + 2) I y from S y) (unitSec y)) =
      liftedTensorSection (I := I) (M := M) g 0 2 S := by
    funext y
    exact liftedTensorSection_zero_eq_apply_unit (I := I) (M := M) g S y
  rw [hsec]

noncomputable def metricFormFun (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, Tensor0SSpace r I y :=
  fun y => Tensor0SSpace.ofModel
    (separableFormAt (I := I) (M := M) g y r (fun i : Fin r => Y i y))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
lemma toModel_metricFormFun (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel (metricFormFun (I := I) (M := M) g r Y y) =
      separableFormAt (I := I) (M := M) g y r (fun i : Fin r => Y i y) := by
  rw [metricFormFun, Tensor0SSpace.toModel_ofModel]

private noncomputable def evalAtBasisCLE_loc (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
  set L : Tensor0SModel n ℝ E →ₗ[ℝ] ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
    { toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hL
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_eq, Module.finrank_pi, Fintype.card_pi]
    simp [Fintype.card_fin]
  have hinj : Function.Injective L := by
    intro Φ₁ Φ₂ h
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
    intro v
    exact congrFun h v
  exact LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective L
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp hinj⟩)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma evalAtBasisCLE_loc_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLE_loc (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis_loc
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => evalAtBasisCLE_loc (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (evalAtBasisCLE_loc (E := E) n).symm :=
    (evalAtBasisCLE_loc (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLE_loc (E := E) n).symm_apply_apply (Φ b)).symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma contMDiffOn_metricFormFun_baseSet
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        (metricFormFun (I := I) (M := M) g r Y y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set e : Trivialization (Tensor0SModel r ℝ E)
    (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) → M) :=
    trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α
  have hbaseSet_eq : e.baseSet = (trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_iff := e.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
    (s := fun y => metricFormFun (I := I) (M := M) g r Y y)
  rw [hbaseSet_eq] at h_iff
  refine h_iff.mpr ?_
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_loc (I := I) (M := M) _ ?_
  intro ψ
  have hfibre : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      (e (TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) b
          (metricFormFun (I := I) (M := M) g r Y b))).2
        (fun k : Fin r => (chartModelBasis E) (ψ k)) =
        ∏ k : Fin r, g.inner b (Y k b)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b ((chartModelBasis E) (ψ k))) := by
    intro b _
    change ((separableFormAt (I := I) (M := M) g b r
          (fun k : Fin r => Y k b)).compContinuousLinearMap
          (fun _ : Fin r => (trivializationAt E (TangentSpace I) α).symmL ℝ b))
        (fun k : Fin r => (chartModelBasis E) (ψ k)) = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, separableFormAt_apply]
    rfl
  have hfibre' : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      (e (TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) b
          (metricFormFun (I := I) (M := M) g r Y b))).2
        (fun k : Fin r => (chartModelBasis E) (ψ k)) =
        ∏ k : Fin r, g.inner b (Y k b) (chartBasisVecFiber (I := I) α (ψ k) b) := by
    intro b hb
    rw [hfibre b hb]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [Bundle.Trivialization.symmL_apply]
    rfl
  refine ContMDiffOn.congr ?_ hfibre'
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g.inner b (Y k b)
          (chartBasisVecFiber (I := I) α (ψ k) b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) g.contMDiff.contMDiffOn (Y k).contMDiff.contMDiffOn
      (chartBasisVec_contMDiffOn (I := I) α (ψ k))
  intro x hx
  have hpb := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma contMDiff_metricFormFun (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        (metricFormFun (I := I) (M := M) g r Y y)) := by
  intro x₀
  refine ((contMDiffOn_metricFormFun_baseSet (I := I) (M := M) g r Y x₀).contMDiffAt
    ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)))

noncomputable def metricFormSection
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
  ⟨metricFormFun (I := I) (M := M) g r Y, contMDiff_metricFormFun (I := I) (M := M) g r Y⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
lemma metricFormSection_apply
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    metricFormSection (I := I) (M := M) g r Y y =
      metricFormFun (I := I) (M := M) g r Y y := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
lemma toModel_metricFormSection
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel (metricFormSection (I := I) (M := M) g r Y y) =
      separableFormAt (I := I) (M := M) g y r (fun i : Fin r => Y i y) := by
  rw [metricFormSection_apply, toModel_metricFormFun]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricFormFun_tensorSectionMDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TensorSectionMDiffAt (I := I) r (metricFormFun (I := I) (M := M) g r Y) x :=
  (contMDiff_metricFormFun (I := I) (M := M) g r Y x).mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma curriedSection_metricFormFun_succ
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Y : Fin (r + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) (v : E) :
    curriedSection I M (metricFormFun (I := I) (M := M) g (r + 1) Y) y v =
      (g.inner y (Y 0 y) v) • metricFormFun (I := I) (M := M) g r
        (fun i : Fin r => Y i.succ) y := by
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel (curriedSection I M
      (metricFormFun (I := I) (M := M) g (r + 1) Y) y v) m =
    Tensor0SSpace.toModel ((g.inner y (Y 0 y) v) •
      metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ) y) m
  rw [curriedSection_apply, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    toModel_metricFormFun]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := metricFormFun (I := I) (M := M) g (r + 1) Y y) (v0 := v) (vs := m)]
  rw [toModel_metricFormFun, separableFormAt_apply, separableFormAt_apply,
    Fin.prod_univ_succ, smul_eq_mul, Fin.cons_zero]
  refine congrArg (g.inner y (Y 0 y) v * ·) ?_
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Fin.cons_succ]

noncomputable def rawLiftFun (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π y : M, TensorRSSpace r s I y) : Π y : M, Tensor0SSpace (r + s) I y :=
  fun y => Tensor0SSpace.ofModel
    (lowerAllUpperIndices (I := I) (M := M) g r s y (TensorRSSpace.toModel (T y)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
lemma toModel_rawLiftFun (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π y : M, TensorRSSpace r s I y) (y : M) :
    Tensor0SSpace.toModel (rawLiftFun (I := I) (M := M) g r s T y) =
      lowerAllUpperIndices (I := I) (M := M) g r s y (TensorRSSpace.toModel (T y)) := by
  rw [rawLiftFun, Tensor0SSpace.toModel_ofModel]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma separableFormAt_succ_cons_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ) (f : Fin (r + 1) → E)
    (w : Fin (r + 1) → E) :
    separableFormAt (I := I) (M := M) g x (r + 1) f w =
      g.inner x (f 0) (w 0) *
        separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => f i.succ) (fun i : Fin r => w i.succ) := by
  rw [separableFormAt_apply, separableFormAt_apply, Fin.prod_univ_succ]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma toModel_covDeriv_metricFormSection (g : SmoothRiemannianMetric I M) :
    ∀ (r : ℕ) (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (x : M) (v : TangentSpace I x),
      Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            (metricFormFun (I := I) (M := M) g r Y) x v) =
        ∑ k : Fin r, separableFormAt (I := I) (M := M) g x r
          (Function.update (fun i : Fin r => Y i x) k
            ((LeviCivita (I := I) g).toFun (fun y => Y k y) x v))
  | 0, Y, x, v => by
      have hunit : metricFormFun (I := I) (M := M) g 0 Y =
            fun _ : M => Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := by
        funext y
        refine Tensor0SSpace.toModel_injective ?_
        change Tensor0SSpace.toModel (metricFormFun (I := I) (M := M) g 0 Y y) =
          Tensor0SSpace.toModel (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
        rw [toModel_metricFormFun, Tensor0SSpace.toModel_ofModel]
        exact separableFormAt_zero (I := I) (M := M) g y _
      rw [hunit, tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
        (LeviCivita (I := I) g) x v, Tensor0SSpace.toModel_zero]
      simp
  | (r + 1), Y, x, v => by
      classical
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      obtain ⟨Yw, hYwx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (w 0)

      have hpeel := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g r
        (W := metricFormFun (I := I) (M := M) g (r + 1) Y)
        (metricFormFun_tensorSectionMDiffAt (I := I) (M := M) g (r + 1) Y x)
        Yw v (Fin.tail w)
      rw [hYwx] at hpeel

      have hcurriedEq : (fun y : M => curriedSection I M
            (metricFormFun (I := I) (M := M) g (r + 1) Y) y (Yw y)) =
          (fun y : M => (fun z : M => g.inner z (Y 0 z) (Yw z)) y •
            metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ) y) := by
        funext y
        rw [curriedSection_metricFormFun_succ]

      have hfscal_smooth : ContMDiff I 𝓘(ℝ) ∞
          (fun z : M => g.inner z (Y 0 z) (Yw z)) := by
        have happ : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
            (fun z : M => (⟨z, g.inner z (Y 0 z) (Yw z)⟩ :
                TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
          ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
            (b := id) g.contMDiff (Y 0).contMDiff Yw.contMDiff
        intro z
        have hz := happ z
        rw [Bundle.contMDiffAt_totalSpace] at hz
        exact hz.2
      set fscal : C^∞⟮I, M; ℝ⟯ :=
        ⟨fun z : M => g.inner z (Y 0 z) (Yw z), hfscal_smooth⟩ with hfscal
      have hleibTerm :
          tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => curriedSection I M
                (metricFormFun (I := I) (M := M) g (r + 1) Y) y (Yw y)) x v =
            fscal x • tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ)) x v +
              (extDerivFun (I := I) (fun z : M => fscal z) x v) •
                metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ) x := by
        rw [hcurriedEq]
        have hLeib := (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
          ).isCovariantDerivativeOn.leibniz (s := Set.univ)
          (σ := fun y : M => metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ) y)
          (g := fun z : M => fscal z) (x := x)
          (metricFormFun_tensorSectionMDiffAt (I := I) (M := M) g r (fun i : Fin r => Y i.succ) x)
          (fscal.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Set.mem_univ x)
        have hcong : (fun y : M => (fun z : M => g.inner z (Y 0 z) (Yw z)) y •
              metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ) y) =
            (fun z : M => fscal z) •
              (fun y : M => metricFormFun (I := I) (M := M) g r (fun i : Fin r => Y i.succ) y) :=
          rfl
        rw [hcong, hLeib, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]

      have hYw_mdiff : MDiffAt (T% fun z => Yw z) x :=
        Yw.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hY0_mdiff : MDiffAt (T% fun z => Y 0 z) x :=
        (Y 0).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hfscal_deriv : extDerivFun (I := I) (fun z : M => fscal z) x v =
          g.inner x ((LeviCivita (I := I) g).toFun (fun z => Y 0 z) x v) (Yw x) +
          g.inner x (Y 0 x) ((LeviCivita (I := I) g).toFun (fun z => Yw z) x v) := by
        have hext : extDerivFun (I := I) (fun z : M => fscal z) x v =
            mfderiv I 𝓘(ℝ, ℝ) (fun z : M => g.inner z (Y 0 z) (Yw z)) x v := by
          simp only [extDerivFun, ContinuousLinearMap.comp_apply,
            ContinuousLinearEquiv.coe_coe]
          simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
            LinearEquiv.coe_mk]
          rfl
        rw [hext]
        exact (LeviCivita_isMetricCompatible (I := I) g).apply hY0_mdiff hYw_mdiff v

      have hconsw : Fin.cons (w 0) (Fin.tail w) = w := Fin.cons_self_tail w
      rw [show ((tensor0SCovariantDerivative I M (r + 1) (LeviCivita (I := I) g)
            (metricFormFun (I := I) (M := M) g (r + 1) Y) x v)).toModel w =
          ((tensor0SCovariantDerivative I M (r + 1) (LeviCivita (I := I) g)
            (metricFormFun (I := I) (M := M) g (r + 1) Y) x v)).toModel
            (Fin.cons (w 0) (Fin.tail w)) from by rw [hconsw]]
      rw [hpeel, hleibTerm]

      rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
        ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
        ContinuousMultilinearMap.smul_apply, toModel_covDeriv_metricFormSection g r
          (fun i : Fin r => Y i.succ) x v, toModel_metricFormFun, hfscal_deriv, hYwx]

      rw [toModel_metricFormFun,
        separableFormAt_succ_cons_apply (I := I) (M := M) g x r (fun i => Y i x)
          (Fin.cons ((LeviCivita (I := I) g).toFun (fun z => Yw z) x v) (Fin.tail w))]
      simp only [Fin.cons_zero, Fin.cons_succ]

      rw [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]

      rw [Fin.sum_univ_succ (fun k : Fin (r + 1) => separableFormAt (I := I) (M := M) g x (r + 1)
        (Function.update (fun i : Fin (r + 1) => Y i x) k
          ((LeviCivita (I := I) g).toFun (fun z => Y k z) x v)) w)]

      rw [separableFormAt_succ_cons_apply (I := I) (M := M) g x r
        (Function.update (fun i : Fin (r + 1) => Y i x) 0
          ((LeviCivita (I := I) g).toFun (fun z => Y 0 z) x v)) w]
      rw [Function.update_self]
      have hupd0_succ : (fun i : Fin r =>
            Function.update (fun i : Fin (r + 1) => Y i x) 0
              ((LeviCivita (I := I) g).toFun (fun z => Y 0 z) x v) i.succ) =
          fun i : Fin r => Y i.succ x := by
        funext i
        rw [Function.update_of_ne (Fin.succ_ne_zero i)]
      rw [hupd0_succ]

      have hsucc_summand : ∀ j : Fin r,
          separableFormAt (I := I) (M := M) g x (r + 1)
              (Function.update (fun i : Fin (r + 1) => Y i x) j.succ
                ((LeviCivita (I := I) g).toFun (fun z => Y j.succ z) x v)) w =
            g.inner x (Y 0 x) (w 0) *
              separableFormAt (I := I) (M := M) g x r
                (Function.update (fun i : Fin r => Y i.succ x) j
                  ((LeviCivita (I := I) g).toFun (fun z => Y j.succ z) x v))
                (fun i : Fin r => w i.succ) := by
        intro j
        rw [separableFormAt_succ_cons_apply (I := I) (M := M) g x r
          (Function.update (fun i : Fin (r + 1) => Y i x) j.succ
            ((LeviCivita (I := I) g).toFun (fun z => Y j.succ z) x v)) w]
        rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
        refine congrArg (g.inner x (Y 0 x) (w 0) * · ) ?_
        have htail_upd : (fun i : Fin r =>
              Function.update (fun i : Fin (r + 1) => Y i x) j.succ
                ((LeviCivita (I := I) g).toFun (fun z => Y j.succ z) x v) i.succ) =
            Function.update (fun i : Fin r => Y i.succ x) j
              ((LeviCivita (I := I) g).toFun (fun z => Y j.succ z) x v) := by
          funext i
          rw [Function.update_apply, Function.update_apply]
          by_cases hij : i = j
          · subst hij; simp
          · rw [if_neg hij, if_neg (fun h => hij (Fin.succ_injective r h))]
        rw [htail_upd]
      rw [Finset.sum_congr rfl (fun j _ => hsucc_summand j)]

      have hfscalx : fscal x = g.inner x (Y 0 x) (w 0) := by
        change g.inner x (Y 0 x) (Yw x) = g.inner x (Y 0 x) (w 0)
        rw [hYwx]
      rw [hfscalx]
      rw [show Fin.tail w = fun i : Fin r => w i.succ from rfl]
      simp only [smul_eq_mul, ← Finset.mul_sum]
      ring

noncomputable def prependMetricCLM
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (r + 1) I y :=
  (tensor0S_curry (I := I) (M := M) r y).symm.toContinuousLinearMap.comp
    ((((ContinuousLinearEquiv.refl ℝ (TangentSpace I y)).arrowCongr
          (tensor0SSpace_continuousLinearEquiv (I := I) r y).symm).toContinuousLinearMap).comp
      ((ContinuousLinearMap.smulRightL ℝ E (Tensor0SModel r ℝ E)
          (g.inner y (X y))).comp
        (tensor0SSpace_continuousLinearEquiv (I := I) r y).toContinuousLinearMap))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma toModel_prependMetricCLM
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M)
    (γ : Tensor0SSpace r I y) (z : Fin (r + 1) → E) :
    Tensor0SSpace.toModel (prependMetricCLM (I := I) (M := M) g r X y γ) z =
      g.inner y (X y) (z 0) *
        Tensor0SSpace.toModel γ (fun i : Fin r => z i.succ) := by
  have hval : Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) r y
        (prependMetricCLM (I := I) (M := M) g r X y γ) (z 0)) =
      (g.inner y (X y) (z 0)) • Tensor0SSpace.toModel γ := by
    rw [prependMetricCLM]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_symm]
    change Tensor0SSpace.toModel (Tensor0SSpace.ofModel
        ((g.inner y (X y)).smulRight (Tensor0SSpace.toModel γ)
          ((ContinuousLinearEquiv.refl ℝ (TangentSpace I y)) (z 0)))) = _
    rw [Tensor0SSpace.toModel_ofModel, ContinuousLinearMap.smulRight_apply]
    rfl
  have hcurry := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := prependMetricCLM (I := I) (M := M) g r X y γ) (v0 := z 0) (vs := fun i : Fin r => z i.succ)
  rw [hval, ContinuousMultilinearMap.smul_apply, smul_eq_mul] at hcurry
  have hzcons : Tensor0SSpace.toModel (prependMetricCLM (I := I) (M := M) g r X y γ) z =
      Tensor0SSpace.toModel (prependMetricCLM (I := I) (M := M) g r X y γ)
        (Fin.cons (z 0) (fun i : Fin r => z i.succ)) := by
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
  rw [hzcons, hcurry]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensor0SCovDeriv_cast_transport
    {a b : ℕ} (g : SmoothRiemannianMetric I M) (h : a = b)
    (W : Π y : M, Tensor0SSpace b I y) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M a (LeviCivita (I := I) g)
        (fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) h.symm) (W y)) x v =
      cast (congrArg (fun n => Tensor0SSpace n I x) h.symm)
        (tensor0SCovariantDerivative I M b (LeviCivita (I := I) g) W x v) := by
  subst h; rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma toModel_cast_transport
    {a b : ℕ} (h : a = b) {x : M} (T : Tensor0SSpace b I x) :
    Tensor0SSpace.toModel (cast (congrArg (fun n => Tensor0SSpace n I x) h.symm) T) =
      (Tensor0SSpace.toModel T).domDomCongr (finCongr h.symm) := by
  cases h
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorSectionMDiffAt_cast_transport
    {a b : ℕ} (h : a = b) (W : Π y : M, Tensor0SSpace b I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) b W x) :
    TensorSectionMDiffAt (I := I) a
      (fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) h.symm) (W y)) x := by
  cases h; exact hW

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorSectionMDiffAt_curriedSection_applyVF
    (s : ℕ) (W : Π y : M, Tensor0SSpace (s + 1) I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma curriedSection_castLift_succ_eq_rawLiftFun_comp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π y : M, TensorRSSpace (r + 1) s I y)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun y : M => curriedSection I M
        (fun z : M => cast (congrArg (fun n => Tensor0SSpace n I z)
            ((Nat.succ_add r s).symm : (r + s) + 1 = (r + 1) + s).symm)
          (rawLiftFun (I := I) (M := M) g (r + 1) s T z)) y (X y)) =
      rawLiftFun (I := I) (M := M) g r s
        (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace s I y from T y).comp
          (prependMetricCLM (I := I) (M := M) g r X y)) := by
  set h : (r + s) + 1 = (r + 1) + s := (Nat.succ_add r s).symm with hh
  funext y
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun z => ?_)

  have hLHS : Tensor0SSpace.toModel
        (curriedSection I M
          (fun w : M => cast (congrArg (fun n => Tensor0SSpace n I w) h.symm)
            (rawLiftFun (I := I) (M := M) g (r + 1) s T w)) y (X y)) z =
      TensorRSSpace.toModel (T y)
          (separableFormAt (I := I) (M := M) g y (r + 1)
            (fun k : Fin (r + 1) =>
            (Fin.cons (X y) z : Fin (r + s + 1) → E) ((finCongr h.symm) (Fin.castAdd s k))))
          (fun j : Fin s =>
            (Fin.cons (X y) z : Fin (r + s + 1) → E) ((finCongr h.symm) (Fin.natAdd (r + 1) j))) := by
    rw [curriedSection_apply, TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := cast (congrArg (fun n => Tensor0SSpace n I y) h.symm)
        (rawLiftFun (I := I) (M := M) g (r + 1) s T y)) (v0 := X y) (vs := z)]
    rw [toModel_cast_transport h (rawLiftFun (I := I) (M := M) g (r + 1) s T y)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [toModel_rawLiftFun, lowerAllUpperIndices_apply]

  have hRHS : Tensor0SSpace.toModel
        (rawLiftFun (I := I) (M := M) g r s
          (fun w : M => (show Tensor0SSpace (r + 1) I w →L[ℝ] Tensor0SSpace s I w from T w).comp
            (prependMetricCLM (I := I) (M := M) g r X w)) y) z =
      TensorRSSpace.toModel (T y)
          (Tensor0SSpace.toModel
            (prependMetricCLM (I := I) (M := M) g r X y
              (Tensor0SSpace.ofModel
                (separableFormAt (I := I) (M := M) g y r
                  (fun i : Fin r => z (Fin.castAdd s i))))))
          (fun j : Fin s => z (Fin.natAdd r j)) := by
    rw [toModel_rawLiftFun, lowerAllUpperIndices_apply]
    rw [toModel_tensorRS_comp_apply (I := I) (M := M) r s y (T y)
      (prependMetricCLM (I := I) (M := M) g r X y)
      (separableFormAt (I := I) (M := M) g y r (fun i : Fin r => z (Fin.castAdd s i)))]

  have hlo : (fun k : Fin (r + 1) =>
        (Fin.cons (X y) z : Fin (r + s + 1) → E) ((finCongr h.symm) (Fin.castAdd s k))) =
      Fin.cons (X y) (fun i : Fin r => z (Fin.castAdd s i)) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]
      have : (finCongr h.symm) (Fin.castAdd s (0 : Fin (r + 1))) = (0 : Fin (r + s + 1)) :=
        Fin.ext (by simp)
      rw [this, Fin.cons_zero]
    · rw [Fin.cons_succ]
      have : (finCongr h.symm) (Fin.castAdd s i.succ) =
          Fin.succ ((Fin.castAdd s i : Fin (r + s))) := Fin.ext (by simp [Fin.succ])
      rw [this, Fin.cons_succ]
  have hhi : (fun j : Fin s =>
        (Fin.cons (X y) z : Fin (r + s + 1) → E) ((finCongr h.symm) (Fin.natAdd (r + 1) j))) =
      (fun j : Fin s => z (Fin.natAdd r j)) := by
    funext j
    have : (finCongr h.symm) (Fin.natAdd (r + 1) j) =
        Fin.succ ((Fin.natAdd r j : Fin (r + s))) := Fin.ext (by simp [Fin.succ, Nat.add_right_comm])
    rw [this, Fin.cons_succ]
  rw [hLHS, hRHS, hlo, hhi]

  have hform : separableFormAt (I := I) (M := M) g y (r + 1)
        (Fin.cons (X y) (fun i : Fin r => z (Fin.castAdd s i))) =
      Tensor0SSpace.toModel
        (prependMetricCLM (I := I) (M := M) g r X y
          (Tensor0SSpace.ofModel
            (separableFormAt (I := I) (M := M) g y r (fun i : Fin r => z (Fin.castAdd s i))))) := by
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [toModel_prependMetricCLM, Tensor0SSpace.toModel_ofModel, separableFormAt_succ_cons_apply,
      Fin.cons_zero]
    refine congrArg (g.inner y (X y) (u 0) * ·) ?_
    simp only [Fin.cons_succ]
  rw [hform]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma loweredCovDeriv_metricForm_eval_aux (g : SmoothRiemannianMetric I M) :
    ∀ (r s : ℕ) (T : Π y : M, TensorRSSpace r s I y)
      (_hLiftDiff : ∀ z : M, TensorSectionMDiffAt (I := I) (r + s)
        (rawLiftFun (I := I) (M := M) g r s T) z)
      (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (x : M) (v : TangentSpace I x) (m : Fin s → E),
      Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
            (rawLiftFun (I := I) (M := M) g r s T) x v)
          (Fin.append (fun i : Fin r => Y i x) m) =
        Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
              (fun y : M =>
                (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from T y)
                  (metricFormSection (I := I) (M := M) g r Y y)) x v) m
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T x)
                (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
                  (fun y : M => metricFormSection (I := I) (M := M) g r Y y) x v)) m := by
  intro r
  induction r with
  | zero =>
    intro s T _hLiftDiff Y x v m

    have hcorr0 : tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => metricFormSection (I := I) (M := M) g 0 Y y) x v = 0 := by
      refine Tensor0SSpace.toModel_injective ?_
      beta_reduce
      rw [show (fun y : M => metricFormSection (I := I) (M := M) g 0 Y y) =
          metricFormFun (I := I) (M := M) g 0 Y from rfl]
      rw [toModel_covDeriv_metricFormSection g 0 Y x v, Tensor0SSpace.toModel_zero]
      simp
    rw [hcorr0, map_zero, Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply,
      sub_zero]

    have hunit : ∀ y : M, metricFormSection (I := I) (M := M) g 0 Y y =
        Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := by
      intro y
      refine Tensor0SSpace.toModel_injective ?_
      beta_reduce
      rw [show metricFormSection (I := I) (M := M) g 0 Y y =
          metricFormFun (I := I) (M := M) g 0 Y y from rfl]
      rw [toModel_metricFormFun, Tensor0SSpace.toModel_ofModel]
      exact separableFormAt_zero (I := I) (M := M) g y _
    have hliftEq : rawLiftFun (I := I) (M := M) g 0 s T =
        fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T y)
            (metricFormSection (I := I) (M := M) g 0 Y y)) := by
      funext y
      refine Tensor0SSpace.toModel_injective ?_
      beta_reduce
      rw [toModel_rawLiftFun, toModel_cast_transport (Nat.zero_add s)
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T y)
          (metricFormSection (I := I) (M := M) g 0 Y y))]
      rw [toModel_tensorRS_apply (I := I) (M := M) 0 s y (T y)
        (metricFormSection (I := I) (M := M) g 0 Y y)]
      rw [show metricFormSection (I := I) (M := M) g 0 Y y =
          metricFormFun (I := I) (M := M) g 0 Y y from rfl, toModel_metricFormFun]
      refine ContinuousMultilinearMap.ext (fun u => ?_)
      rw [lowerAllUpperIndices_apply, ContinuousMultilinearMap.domDomCongr_apply,
        separableFormAt_zero]
      congr 1
      funext j
      congr 1
      exact (Fin.ext (by simp)).symm
    rw [hliftEq]
    rw [tensor0SCovDeriv_cast_transport g (Nat.zero_add s)
      (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T y)
        (metricFormSection (I := I) (M := M) g 0 Y y)) x v]
    rw [toModel_cast_transport (Nat.zero_add s)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext j
    rw [show (fun i : Fin 0 => Y i x) = (Fin.elim0 : Fin 0 → E) from by funext i; exact i.elim0]
    rw [Fin.elim0_append]
    rfl
  | succ r ih =>
    intro s T hLiftDiff Y x v m
    classical
    set h : (r + s) + 1 = (r + 1) + s := (Nat.succ_add r s).symm with hh

    set castLift : Π z : M, Tensor0SSpace ((r + s) + 1) I z :=
      fun z : M => cast (congrArg (fun n => Tensor0SSpace n I z) h.symm)
        (rawLiftFun (I := I) (M := M) g (r + 1) s T z) with hcastLift

    have hcastLiftDiff : ∀ z : M, TensorSectionMDiffAt (I := I) ((r + s) + 1) castLift z := by
      intro z
      exact tensorSectionMDiffAt_cast_transport h
        (rawLiftFun (I := I) (M := M) g (r + 1) s T) (hLiftDiff z)

    set T' : Π y : M, TensorRSSpace r s I y :=
      fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace s I y from T y).comp
        (prependMetricCLM (I := I) (M := M) g r (Y 0) y) with hT'

    have hpeelEq : (fun y : M => curriedSection I M castLift y (Y 0 y)) =
        rawLiftFun (I := I) (M := M) g r s T' := by
      rw [hcastLift, hT']
      exact curriedSection_castLift_succ_eq_rawLiftFun_comp (I := I) (M := M) g r s T (Y 0)

    have hLiftDiff' : ∀ z : M, TensorSectionMDiffAt (I := I) (r + s)
        (rawLiftFun (I := I) (M := M) g r s T') z := by
      intro z
      rw [← hpeelEq]
      exact tensorSectionMDiffAt_curriedSection_applyVF (I := I) (M := M) (r + s)
        castLift (hcastLiftDiff z) (Y 0)

    have hYcons : (fun k : Fin (r + 1) => Y k x) =
        Fin.cons (Y 0 x) (fun k : Fin r => Y k.succ x) := by
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ]
    have htuple : (fun i : Fin ((r + s) + 1) =>
          (Fin.append (fun k : Fin (r + 1) => Y k x) m) ((finCongr h) i)) =
        Fin.cons (Y 0 x) (Fin.append (fun k : Fin r => Y k.succ x) m) := by
      funext i
      rw [hYcons, Fin.append_cons, Function.comp_apply]
      have hidx : (Fin.cast (Nat.add_right_comm r 1 s)) ((finCongr h) i) = i :=
        Fin.ext (by simp [finCongr])
      rw [hidx]

    have hLHSeq : Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M ((r + 1) + s) (LeviCivita (I := I) g)
            (rawLiftFun (I := I) (M := M) g (r + 1) s T) x v)
          (Fin.append (fun k : Fin (r + 1) => Y k x) m) =
        Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M ((r + s) + 1) (LeviCivita (I := I) g) castLift x v)
          (Fin.cons (Y 0 x) (Fin.append (fun k : Fin r => Y k.succ x) m)) := by
      have hrawCast : rawLiftFun (I := I) (M := M) g (r + 1) s T =
          fun z : M => cast (congrArg (fun n => Tensor0SSpace n I z) h) (castLift z) := by
        funext z
        rw [hcastLift]
        simp
      rw [hrawCast]
      rw [tensor0SCovDeriv_cast_transport g h.symm castLift x v]
      rw [toModel_cast_transport h.symm
        (tensor0SCovariantDerivative I M ((r + s) + 1) (LeviCivita (I := I) g) castLift x v)]
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      rw [← htuple]
    rw [hLHSeq]

    rw [tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g (r + s)
      (W := castLift) (hcastLiftDiff x) (Y 0) v
      (Fin.append (fun k : Fin r => Y k.succ x) m)]
    rw [hpeelEq]

    rw [ih s T' hLiftDiff' (fun k : Fin r => Y k.succ) x v m]

    have hpartialEq : (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from T' y)
          (metricFormSection (I := I) (M := M) g r (fun k : Fin r => Y k.succ) y)) =
        (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace s I y from T y)
          (metricFormSection (I := I) (M := M) g (r + 1) Y y)) := by
      funext y
      rw [hT']
      change (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace s I y from T y)
          (prependMetricCLM (I := I) (M := M) g r (Y 0) y
            (metricFormSection (I := I) (M := M) g r (fun k : Fin r => Y k.succ) y)) = _
      congr 1
      refine Tensor0SSpace.toModel_injective ?_
      refine ContinuousMultilinearMap.ext (fun u => ?_)
      beta_reduce
      rw [toModel_prependMetricCLM, toModel_metricFormSection]
      rw [show metricFormSection (I := I) (M := M) g (r + 1) Y y =
          metricFormFun (I := I) (M := M) g (r + 1) Y y from rfl, toModel_metricFormFun,
        separableFormAt_succ_cons_apply]
    rw [hpartialEq]

    rw [sub_sub]
    congr 1

    set nablaY : Fin (r + 1) → E :=
      fun k => (LeviCivita (I := I) g).toFun (fun y => Y k y) x v with hnablaY
    set RHSk : Fin (r + 1) → ℝ := fun k => TensorRSSpace.toModel (T x)
      (separableFormAt (I := I) (M := M) g x (r + 1)
        (Function.update (fun l : Fin (r + 1) => Y l x) k (nablaY k))) m with hRHSk

    have hgoalCorr : Tensor0SSpace.toModel
          ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace s I x from T x)
            (tensor0SCovariantDerivative I M (r + 1) (LeviCivita (I := I) g)
              (fun y : M => metricFormSection (I := I) (M := M) g (r + 1) Y y) x v)) m =
        ∑ k : Fin (r + 1), RHSk k := by
      rw [show (fun y : M => metricFormSection (I := I) (M := M) g (r + 1) Y y) =
          metricFormFun (I := I) (M := M) g (r + 1) Y from rfl]
      rw [toModel_tensorRS_apply (I := I) (M := M) (r + 1) s x (T x)
        (tensor0SCovariantDerivative I M (r + 1) (LeviCivita (I := I) g)
          (metricFormFun (I := I) (M := M) g (r + 1) Y) x v)]
      rw [toModel_covDeriv_metricFormSection g (r + 1) Y x v]
      rw [map_sum, ContinuousMultilinearMap.sum_apply]

    have hk0 : Tensor0SSpace.toModel (castLift x)
          (Fin.cons (nablaY 0) (Fin.append (fun k : Fin r => Y k.succ x) m)) = RHSk 0 := by
      rw [hRHSk]
      change Tensor0SSpace.toModel (castLift x)
          (Fin.cons (nablaY 0) (Fin.append (fun k : Fin r => Y k.succ x) m)) =
        TensorRSSpace.toModel (T x)
          (separableFormAt (I := I) (M := M) g x (r + 1)
            (Function.update (fun l : Fin (r + 1) => Y l x) 0 (nablaY 0))) m
      rw [hcastLift]
      rw [toModel_cast_transport h (rawLiftFun (I := I) (M := M) g (r + 1) s T x)]
      rw [ContinuousMultilinearMap.domDomCongr_apply, toModel_rawLiftFun,
        lowerAllUpperIndices_apply]
      have hform : separableFormAt (I := I) (M := M) g x (r + 1)
            (fun k : Fin (r + 1) => (Fin.cons (nablaY 0)
              (Fin.append (fun l : Fin r => Y l.succ x) m) : Fin (r + s + 1) → E)
              ((finCongr h.symm) (Fin.castAdd s k))) =
          separableFormAt (I := I) (M := M) g x (r + 1)
            (Function.update (fun l : Fin (r + 1) => Y l x) 0 (nablaY 0)) := by
        congr 1
        funext k
        refine Fin.cases ?_ (fun j => ?_) k
        · rw [Function.update_self]
          have : (finCongr h.symm) (Fin.castAdd s (0 : Fin (r + 1))) =
              (0 : Fin ((r + s) + 1)) := Fin.ext (by simp)
          rw [this, Fin.cons_zero]
        · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
          have : (finCongr h.symm) (Fin.castAdd s j.succ) =
              Fin.succ ((Fin.castAdd s j : Fin (r + s))) := Fin.ext (by simp [Fin.succ])
          rw [this, Fin.cons_succ, Fin.append_left]
      have htail : (fun j : Fin s => (Fin.cons (nablaY 0)
            (Fin.append (fun l : Fin r => Y l.succ x) m) : Fin (r + s + 1) → E)
              ((finCongr h.symm) (Fin.natAdd (r + 1) j))) = m := by
        funext j
        have : (finCongr h.symm) (Fin.natAdd (r + 1) j) =
            Fin.succ ((Fin.natAdd r j : Fin (r + s))) :=
          Fin.ext (by simp [Fin.succ, Nat.add_right_comm])
        rw [this, Fin.cons_succ, Fin.append_right]
      rw [hform, htail]

    have hksucc : ∀ j : Fin r, RHSk j.succ = TensorRSSpace.toModel (T x)
          (Tensor0SSpace.toModel
            (prependMetricCLM (I := I) (M := M) g r (Y 0) x
              (Tensor0SSpace.ofModel
                (separableFormAt (I := I) (M := M) g x r
                  (Function.update (fun l : Fin r => Y l.succ x) j (nablaY j.succ)))))) m := by
      intro j
      rw [hRHSk]
      change TensorRSSpace.toModel (T x)
          (separableFormAt (I := I) (M := M) g x (r + 1)
            (Function.update (fun l : Fin (r + 1) => Y l x) j.succ (nablaY j.succ))) m = _
      congr 2
      refine ContinuousMultilinearMap.ext (fun u => ?_)
      rw [toModel_prependMetricCLM, Tensor0SSpace.toModel_ofModel,
        separableFormAt_succ_cons_apply, separableFormAt_apply, separableFormAt_apply]
      rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
      refine congrArg (g.inner x (Y 0 x) (u 0) * ·) ?_
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Function.update_apply, Function.update_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun hcontra => hij (Fin.succ_injective r hcontra))]

    have hIHcorr : Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T' x)
            (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => metricFormSection (I := I) (M := M) g r (fun k : Fin r => Y k.succ) y)
              x v)) m =
        ∑ j : Fin r, RHSk j.succ := by
      rw [show (fun y : M => metricFormSection (I := I) (M := M) g r (fun k : Fin r => Y k.succ) y) =
          metricFormFun (I := I) (M := M) g r (fun k : Fin r => Y k.succ) from rfl]
      rw [toModel_tensorRS_apply (I := I) (M := M) r s x (T' x)
        (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
          (metricFormFun (I := I) (M := M) g r (fun k : Fin r => Y k.succ)) x v)]
      rw [toModel_covDeriv_metricFormSection g r (fun k : Fin r => Y k.succ) x v]
      rw [map_sum, ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hksucc j, hT']
      rw [toModel_tensorRS_comp_apply (I := I) (M := M) r s x (T x)
        (prependMetricCLM (I := I) (M := M) g r (Y 0) x)
        (separableFormAt (I := I) (M := M) g x r
          (Function.update (fun l : Fin r => Y l.succ x) j (nablaY j.succ)))]

    rw [hgoalCorr, hIHcorr, hk0, add_comm, ← Fin.sum_univ_succ]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma loweredCovDeriv_metricForm_eval (g : SmoothRiemannianMetric I M) :
    ∀ (r s : ℕ) (T : Π y : M, TensorRSSpace r s I y)
      (_hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (T y)))
      (Y : Fin r → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (x : M) (v : TangentSpace I x) (m : Fin s → E),
      Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
            (rawLiftFun (I := I) (M := M) g r s T) x v)
          (Fin.append (fun i : Fin r => Y i x) m) =
        Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
              (fun y : M =>
                (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from T y)
                  (metricFormSection (I := I) (M := M) g r Y y)) x v) m
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T x)
                (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
                  (fun y : M => metricFormSection (I := I) (M := M) g r Y y) x v)) m := by
  intro r s T hT Y x v m
  refine loweredCovDeriv_metricForm_eval_aux (I := I) (M := M) g r s T ?_ Y x v m
  intro z
  exact (contMDiff_lifted_section (I := I) (M := M) g r s ⟨T, hT⟩ z).mdifferentiableAt (by simp)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweredCovDerivAt_eval_eq_partialEval_sub_lowerFormCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) (u : Fin (r + s) → E)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯)
    (hw_at : Tensor0SSpace.toModel (w x) =
      separableFormAt (I := I) (M := M) g x r (fun i : Fin r => u (Fin.castAdd s i))) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s S x v) u =
      Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
          (fun y : M =>
            (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from S y) (w y)) x v)
        (fun j : Fin s => u (Fin.natAdd r j))
      - Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S x)
            (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => w y) x v))
          (fun j : Fin s => u (Fin.natAdd r j)) := by
  classical

  choose Y hYx using fun i : Fin r =>
    ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (u (Fin.castAdd s i))

  have hWform_x : metricFormSection (I := I) (M := M) g r Y x = w x := by
    refine Tensor0SSpace.toModel_injective ?_
    change Tensor0SSpace.toModel (metricFormSection (I := I) (M := M) g r Y x) =
      Tensor0SSpace.toModel (w x)
    rw [toModel_metricFormSection, hw_at]
    refine ContinuousMultilinearMap.ext (fun z => ?_)
    rw [separableFormAt_apply, separableFormAt_apply]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hYx i]

  have hlift : loweredCovDerivAt (I := I) (M := M) g r s S x v =
      tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
        (rawLiftFun (I := I) (M := M) g r s (fun y : M => S y)) x v := by
    rw [loweredCovDerivAt_def]
    congr 1

  have hu_app : u = Fin.append (fun i : Fin r => Y i x) (fun j : Fin s => u (Fin.natAdd r j)) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact (hYx i).symm
    · rw [Fin.append_right]

  rw [hlift]
  conv_lhs => rw [hu_app]
  rw [loweredCovDeriv_metricForm_eval (I := I) (M := M) g r s (fun y : M => S y)
      S.contMDiff Y x v (fun j : Fin s => u (Fin.natAdd r j))]

  have hbracket : ∀ ww : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯,
      Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from S y) (ww y))
            x v) (fun j : Fin s => u (Fin.natAdd r j)) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S x)
            (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) (fun y : M => ww y) x v))
          (fun j : Fin s => u (Fin.natAdd r j)) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
              tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v) (ww x))
          (fun j : Fin s => u (Fin.natAdd r j)) := by
    intro ww
    have hap := tensorRSCovariantDerivative_apply (I := I) M r s (LeviCivita (I := I) g) S ww x v
    rw [← ContinuousMultilinearMap.sub_apply, ← Tensor0SSpace.toModel_sub, ← hap]

  conv_rhs => rw [hbracket w]
  conv_lhs => rw [hbracket (metricFormSection (I := I) (M := M) g r Y)]
  rw [hWform_x]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v)) := by
  classical
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [lowerAllUpperIndices_apply]
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel r ℝ E) (V := fun y : M => Tensor0SSpace r I y) (n := (⊤ : ℕ∞)) x
    (Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g x r (fun i : Fin r => u (Fin.castAdd s i))))
  have hw_at : Tensor0SSpace.toModel (w x) =
      separableFormAt (I := I) (M := M) g x r (fun i : Fin r => u (Fin.castAdd s i)) := by
    rw [hw, Tensor0SSpace.toModel_ofModel]
  have hRSeval :
      (TensorRSSpace.toModel
            (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v))
          (separableFormAt (I := I) (M := M) g x r (fun i : Fin r => u (Fin.castAdd s i)))
          (fun j : Fin s => u (Fin.natAdd r j)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
              tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v) (w x))
          (fun j : Fin s => u (Fin.natAdd r j)) := by
    rw [toModel_tensorRS_apply (I := I) (M := M) r s x
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v) (w x), hw_at]
  rw [hRSeval]
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) r s
    (LeviCivita (I := I) g) S w x v]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [loweredCovDerivAt_eval_eq_partialEval_sub_lowerFormCorrection
    (I := I) (M := M) g r s S x v u w hw_at]

end Connection
end Integral
end DifferentialGeometry

end
