import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false























noncomputable section

namespace Tensor0SBundle

open Bundle Set IsManifold ContinuousLinearMap TensorLieDeriv DifferentialGeometry
open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [T2Space M]













omit [CompleteSpace E] [T2Space M] in
theorem nabla0SFun_hasDerivWithinAt_pt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      HasDerivWithinAt
        (fun r : Real => extDerivFun (I := I)
          (fun p : M => (α r) p (fun a : Fin s => V a p)) x₀ (X x₀))
        (extDerivFun (I := I)
          (fun p : M => (β t) p (fun a : Fin s => V a p)) x₀ (X x₀))
        timeSet t)
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α r) x₀) (fun a : Fin s => V a x₀))
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (β t) x₀) (fun a : Fin s => V a x₀))
      timeSet t := by
  simp only [nabla0SFun_eval_smooth_slots]
  refine HasDerivWithinAt.sub ?_ ?_
  · exact hswap
  · have key :
        (fun r : Real => ∑ a : Fin s, (α r) x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀))))
          = ∑ a : Fin s, (fun r : Real => (α r) x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀)))) := by
      funext r
      simp only [Finset.sum_apply]
    rw [key]
    exact HasDerivWithinAt.sum (fun (a : Fin s) (_ : a ∈ Finset.univ) => hpt a)



omit [CompleteSpace E] [T2Space M] in
theorem nabla0SFun_hasDerivWithinAt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M)
        (fun r p => (α r) p (fun a : Fin s => V a p))
        (fun r p => (β r) p (fun a : Fin s => V a p)))
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α r) x₀) (fun a : Fin s => V a x₀))
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (β t) x₀) (fun a : Fin s => V a x₀))
      timeSet t :=
  nabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t
    (hswap t x₀ (Set.mem_singleton x₀) (X x₀)) hpt







omit [CompleteSpace E] [T2Space M] in
theorem totalNabla0SFun_hasDerivWithinAt_pt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      HasDerivWithinAt
        (fun r : Real => extDerivFun (I := I)
          (fun p : M => (α r) p (fun a : Fin s => V a p)) x₀ (X x₀))
        (extDerivFun (I := I)
          (fun p : M => (β t) p (fun a : Fin s => V a p)) x₀ (X x₀))
        timeSet t)
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (α r) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      ((totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (β t) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      timeSet t := by
  simpa only [totalNabla0SFun_apply_section] using
    nabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t hswap hpt



omit [CompleteSpace E] [T2Space M] in
theorem totalNabla0SFun_hasDerivWithinAt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M)
        (fun r p => (α r) p (fun a : Fin s => V a p))
        (fun r p => (β r) p (fun a : Fin s => V a p)))
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (α r) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      ((totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (β t) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      timeSet t :=
  totalNabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t
    (hswap t x₀ (Set.mem_singleton x₀) (X x₀)) hpt

end Tensor0SBundle
