import DifferentialGeometry.Tensor.RSTensor.Derivation.LieDerivative
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.RSTensor.Basis
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors




namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative










omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_apply_slots {s : ℕ}
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α slots =
      dα_X slots -
        ∑ a : Fin s, α (Function.update slots a (ΓX (slots a))) := by
  classical
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_apply_slots {s : ℕ}
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E)
    (slots : Fin s → E) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x slots =
      fderivWithin 𝕜 α u x (X x) slots -
        ∑ a : Fin s, α x (Function.update slots a (ΓX x (slots a))) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_apply_slots (𝕜 := 𝕜) (E := E)
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) slots


theorem lieDeriv_correctionL_apply_slots {s : ℕ}
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX α) slots =
      ∑ a : Fin s, α (Function.update slots a (ΓX (slots a))) := by
  classical
  rw [lieDeriv_correctionL_apply]
  unfold lieDeriv_correction substituteArg
  simp only [ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]





omit [CompleteSpace 𝕜] in
theorem fderivWithin_tensor0SModel_eval_linear_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (L : Fin s → E → 𝕜 →L[𝕜] E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y)
    (c : Fin s → 𝕜) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (c a))) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (c b)) a
            (fderivWithin 𝕜 (L a) u y Xy (c a))) := by
  classical
  let F : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => 𝕜) 𝕜 :=
    fun z => (α z).compContinuousLinearMap (fun a : Fin s => L a z)
  have hFdiff : DifferentiableWithinAt 𝕜 F u y := by
    exact hα.continuousMultilinearMapCompContinuousLinearMap hL
  have happly :=
    fderivWithin_continuousMultilinear_apply_const_apply
      (𝕜 := 𝕜) (s := u) (x := y) (c := F) hu hFdiff c Xy
  change fderivWithin 𝕜 (fun z : E => F z c) u y Xy =
    (fderivWithin 𝕜 F u y) Xy c at happly
  change fderivWithin 𝕜 (fun z : E => F z c) u y Xy =
    fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
      ∑ a : Fin s,
        α y (Function.update (fun b : Fin s => L b y (c b)) a
          (fderivWithin 𝕜 (L a) u y Xy (c a)))
  rw [happly]
  have hF :=
    fderivWithin_continuousMultilinearMapCompContinuousLinearMap
      (𝕜 := 𝕜) (f := α) (g := L) (s := u) (x := y) hα hL hu
  rw [hF]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.add_apply]
  change
    ((fderivWithin 𝕜 α u y) Xy).compContinuousLinearMap
        (fun x : Fin s => L x y) c +
      (ContinuousMultilinearMap.fderivCompContinuousLinearMap (α y)
        (fun x : Fin s => L x y)
        (fun i : Fin s => (fderivWithin 𝕜 (L i) u y) Xy)) c =
    ((fderivWithin 𝕜 α u y) Xy) (fun a : Fin s => L a y (c a)) +
      ∑ a : Fin s,
        α y (Function.update (fun a : Fin s => L a y (c a)) a
          (((fderivWithin 𝕜 (L a) u y) Xy) (c a)))
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]



omit [CompleteSpace 𝕜] in
theorem fderivWithin_tensor0SModel_eval_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
  classical
  let one : 𝕜 →L[𝕜] 𝕜 := 1
  let A : E →L[𝕜] (𝕜 →L[𝕜] E) :=
    ContinuousLinearMap.smulRightL 𝕜 𝕜 E one
  let L : Fin s → E → 𝕜 →L[𝕜] E := fun a z => A (V a z)
  have hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y := by
    intro a
    exact A.differentiableWithinAt.comp y (hV a) (Set.mapsTo_univ _ _)
  have h := fderivWithin_tensor0SModel_eval_linear_slots
    (𝕜 := 𝕜) (E := E) (s := s) α L u y Xy hα hL hu (fun _ => (1 : 𝕜))
  have hderiv (a : Fin s) :
      ((fderivWithin 𝕜 (L a) u y) Xy) (1 : 𝕜) =
        fderivWithin 𝕜 (V a) u y Xy := by
    have hA :
        fderivWithin 𝕜 (L a) u y =
          A.comp (fderivWithin 𝕜 (V a) u y) := by
      have hcomp := A.hasFDerivAt.comp_hasFDerivWithinAt y (hV a).hasFDerivWithinAt
      simpa [L, Function.comp_def] using hcomp.fderivWithin hu
    rw [hA]
    simp [A, one, ContinuousLinearMap.smulRight_apply]
  calc
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy
        = fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (1 : 𝕜))) u y Xy := by
            simp [L, A, one, ContinuousLinearMap.smulRight_apply]
    _ = fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (1 : 𝕜)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (1 : 𝕜)) a
            (((fderivWithin 𝕜 (L a) u y) Xy) (1 : 𝕜))) := h
    _ = fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
            congr 1
            · congr
              funext a
              simp [L, A, one, ContinuousLinearMap.smulRight_apply]
            · refine Finset.sum_congr rfl fun a _ => ?_
              congr 1
              funext b
              by_cases hb : b = a
              · subst hb
                simpa using hderiv b
              · simp [Function.update, hb, L, A, one, ContinuousLinearMap.smulRight_apply]

end ModelCovariantDerivative

end

end TensorLieDeriv
