import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false



















noncomputable section

namespace Tensor0SBundle

open Bundle Set IsManifold ContinuousLinearMap TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [T2Space M]



omit [CompleteSpace E] in
theorem totalNabla0SFun_smul {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (c : Real)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (c • α) x
      = c • totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov α x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin (s + 1) => basis (idx a))
        = Fin.cons (X x) (fun a : Fin s => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons]
  rw [Tensor0SSpace.smul_apply, totalNabla0SFun_apply_section,
    totalNabla0SFun_apply_section, nabla0SFun_smul]
  rw [Tensor0SSpace.smul_apply]



omit [CompleteSpace E] in
theorem totalNabla0SFun_add {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (α + β) x
      = totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov α x
        + totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov β x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin (s + 1) => basis (idx a))
        = Fin.cons (X x) (fun a : Fin s => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons]
  rw [Tensor0SSpace.add_apply, totalNabla0SFun_apply_section,
    totalNabla0SFun_apply_section, totalNabla0SFun_apply_section, nabla0SFun_add]
  rw [Tensor0SSpace.add_apply]

end Tensor0SBundle
