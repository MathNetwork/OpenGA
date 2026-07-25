import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
namespace DifferentialGeometry
namespace Integral
namespace Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear
open TensorRSNabla
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def endoCovariantDerivative (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I (E →L[ℝ] E)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    E (fun x : M => TangentSpace I x) E (fun x : M => TangentSpace I x)
    (LeviCivita (I := I) g) (LeviCivita (I := I) g)

instance endoCovariantDerivative_contMDiff (g : SmoothRiemannianMetric I M) :
    (endoCovariantDerivative (I := I) (M := M) g).ContMDiffCovariantDerivative ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    E (fun x : M => TangentSpace I x) E (fun x : M => TangentSpace I x)
    (LeviCivita (I := I) g) (LeviCivita (I := I) g)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [CompleteSpace E] in
theorem endoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((endoCovariantDerivative (I := I) (M := M) g) Λ x v) (Y x) =
      (LeviCivita (I := I) g) (fun y => (Λ y) (Y y)) x v -
        (Λ x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    E (fun x : M => TangentSpace I x) E (fun x : M => TangentSpace I x)
    (LeviCivita (I := I) g) (LeviCivita (I := I) g) Λ Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem endoApplySection_contMDiff
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (Y : ContMDiffSection I E ∞ (fun y : M => TangentSpace I y)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((Λ y) (Y y))) := by
  have hΛsm : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) y (Λ y)) := Λ.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) hΛsm Y.contMDiff

set_option backward.isDefEq.respectTransparency false in
def endoSlotZeroCcTensor (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    SmoothCcTensor g (s + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Λ x))
      contMDiff_toFun :=
        slotInsertEndoFib_contMDiff (I := I) (M := M) g (s + 1) 0 (fun x : M => Λ x) Λ.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma slotInsertEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ).toSection x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Λ x) := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma curry_slotInsertEndoFib_zero (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace (s + 1) I x) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x Λ A) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A).comp Λ := by
  apply ContinuousLinearMap.ext
  intro v0
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  rw [tensor0S_curry_apply_eval, slotInsertEndoFib_apply_eval,
    ContinuousLinearMap.comp_apply, tensor0S_curry_apply_eval]
  congr 1
  rw [Fin.cons_zero, Fin.update_cons_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem core_slotInsert_curry_reading (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (v : E) (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g s Λ) x v) D)) v0 =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x D)
        (((endoCovariantDerivative (I := I) (M := M) g) Λ x v) v0) := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  set SIΛ := endoSlotZeroCcTensor (I := I) (M := M) g s Λ with hSIΛ
  have hlamY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((Λ y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) Λ Y
  let lamY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ :=
    ⟨fun y : M => (Λ y) (Y y), hlamY⟩
  have hw_at : TensorSectionMDiffAt (I := I) (s + 1) (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) SIΛ.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) (w y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hCL_wlamY := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g s
    (fun y : M => w y) (x := x) hw_at lamY v
  have hCL_U := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g s
    (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) (w y))
    (x := x) hU_at Y v
  have hHL_SI := tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1) (LeviCivita (I := I) g)
    SIΛ.toSection w x v
  have hEndo := endoCovariantDerivative_apply (I := I) (M := M) g Λ Y x v
  have hfun : (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1) I z from
          SIΛ.toSection z) (w z)) y (Y y)) =
      (fun y : M => Tensor0SNabla.curriedSection I M (fun z : M => w z) y (lamY y)) := by
    funext y
    change tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) (w y)) (Y y) =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y (w y) (lamY y)
    rw [hSIΛ, slotInsertEndoCc_toSection, curry_slotInsertEndoFib_zero, ContinuousLinearMap.comp_apply]
    rfl
  have hcurU_op : Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1) I z from
          SIΛ.toSection z) (w z)) x =
      (Tensor0SNabla.curriedSection I M (fun z : M => w z) x).comp (Λ x) := by
    change tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SIΛ.toSection x) (w x)) = _
    rw [hSIΛ, slotInsertEndoCc_toSection, curry_slotInsertEndoFib_zero]
    rfl
  rw [← hw, ← hY,
    tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1) SIΛ x v]
  rw [hHL_SI, map_sub, ContinuousLinearMap.sub_apply]
  rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl]
  rw [eq_sub_of_add_eq hCL_U.symm]
  rw [hfun, hCL_wlamY]
  rw [show Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1) I z from
          SIΛ.toSection z) (w z)) x =
      (Tensor0SNabla.curriedSection I M (fun z : M => w z) x).comp (Λ x) from hcurU_op]
  rw [hSIΛ]
  simp only [slotInsertEndoCc_toSection]
  rw [curry_slotInsertEndoFib_zero, ContinuousLinearMap.comp_apply]
  have hlamY_eq : ∀ y : M, lamY y = (Λ y) (Y y) := fun _ => rfl
  simp only [hlamY_eq]
  rw [ContinuousLinearMap.comp_apply]
  rw [eq_add_of_sub_eq hEndo.symm]
  rw [map_add]
  rw [show Tensor0SNabla.curriedSection I M (fun y : M => w y) x =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x (w x) from rfl]
  abel

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_slotInsertEndoCc_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (v : E) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g s Λ) x v) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        ((endoCovariantDerivative (I := I) (M := M) g) Λ x v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [slotInsertEndoFib_apply_eval]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (T := (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  rw [core_slotInsert_curry_reading (I := I) (M := M) g s Λ x v D (m 0)]
  rw [tensor0S_curry_apply_eval]
  congr 1
  rw [Fin.cons_zero, Fin.update_cons_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_slotInsertEndoCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
            ((endoCovariantDerivative (I := I) (M := M) g) Λ x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g s Λ) x D v]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s Λ x (v 0)]

def identityHomTensorRSField (r a : ℕ) :
    HomTensorRSField (E := E) (M := M) r a a I where
  toFun := fun x : M => (ContinuousLinearMap.id ℝ (TensorRSSpace r a I x) :
    HomTensorRSSpace r a a I x)
  contMDiff_toFun :=
    contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (V₁ := fun x : M => TensorRSSpace r a I x)
      (V₂ := fun x : M => TensorRSSpace r a I x)
      (φ := fun x : M => ContinuousLinearMap.id ℝ (TensorRSSpace r a I x))
      (fun Y => Y.contMDiff)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma idHomTensorRSField_apply (r a : ℕ) (x : M) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r a I x from
        identityHomTensorRSField (E := E) (M := M) (I := I) r a x) =
      ContinuousLinearMap.id ℝ (TensorRSSpace r a I x) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma appFullSec_idHomTensorRSField (g : SmoothRiemannianMetric I M) (r a : ℕ)
    (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a a (identityHomTensorRSField (E := E) (M := M) (I := I) r a) W = W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection, idHomTensorRSField_apply, ContinuousLinearMap.id_apply]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_slotInsertEndoCc_expansion (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (k : ℕ) :
    ∃ D : (i : ℕ) → HomTensorRSField (E := E) (M := M) (s + 1) (s + 1 + i) (s + 1 + k) I,
      iteratedCovGrad g (s + 1) (s + 1) k (endoSlotZeroCcTensor (I := I) (M := M) g s Λ) =
        ∑ i ∈ Finset.range (k + 1),
          homTensorRSFieldApply (I := I) (M := M) g (s + 1) (s + 1 + i) (s + 1 + k) (D i)
            (iteratedCovGrad g (s + 1) (s + 1) i (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)) := by
  obtain ⟨D, hD⟩ :=
    homFieldAction_iteratedCovGrad_expansion (I := I) (M := M) g (s + 1) (s + 1) (s + 1)
      (identityHomTensorRSField (E := E) (M := M) (I := I) (s + 1) (s + 1)) k
  refine ⟨D, ?_⟩
  have hbase := hD (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)
  rw [appFullSec_idHomTensorRSField (I := I) (M := M) g (s + 1) (s + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)] at hbase
  exact hbase
omit [CompleteSpace E] in


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cotangent_slot_apply (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w) =
      Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
        (fun _ : Fin 1 => (show E from w)) from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update (fun _ : Fin 1 => (show E from w)) 0
        (Λ ((fun _ : Fin 1 => (show E from w)) 0)) =
      (fun _ : Fin 1 => (show E from Λ w)) from by
    funext k
    fin_cases k
    simp]
  rfl


end Connection
end Integral
end DifferentialGeometry
end
