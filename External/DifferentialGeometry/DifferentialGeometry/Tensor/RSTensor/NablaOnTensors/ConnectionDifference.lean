import DifferentialGeometry.Tensor.RSTensor.Components
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false












noncomputable section

namespace Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x : M}

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_one_apply_add
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    α (fun _ : Fin 1 => X + Y) =
      α (fun _ : Fin 1 => X) + α (fun _ : Fin 1 => Y) := by
  let base : Fin 1 -> TangentSpace I x := fun _ => 0
  have h := α.map_update_add base (0 : Fin 1) X Y
  have hleft :
      Function.update base (0 : Fin 1) (X + Y) =
        (fun _ : Fin 1 => X + Y) := by
    funext i
    fin_cases i
    simp [base]
  have hX :
      Function.update base (0 : Fin 1) X =
        (fun _ : Fin 1 => X) := by
    funext i
    fin_cases i
    simp [base]
  have hY :
      Function.update base (0 : Fin 1) Y =
        (fun _ : Fin 1 => Y) := by
    funext i
    fin_cases i
    simp [base]
  rw [← hleft, ← hX, ← hY]
  exact h

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_one_apply_smul
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (c : Real) (X : TangentSpace I x) :
    α (fun _ : Fin 1 => c • X) =
      c • α (fun _ : Fin 1 => X) := by
  let base : Fin 1 -> TangentSpace I x := fun _ => 0
  have h := α.map_update_smul base (0 : Fin 1) c X
  have hleft :
      Function.update base (0 : Fin 1) (c • X) =
        (fun _ : Fin 1 => c • X) := by
    funext i
    fin_cases i
    simp [base]
  have hX :
      Function.update base (0 : Fin 1) X =
        (fun _ : Fin 1 => X) := by
    funext i
    fin_cases i
    simp [base]
  rw [← hleft, ← hX]
  exact h

private noncomputable def connDiffSlotCLM
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => α (fun _ : Fin 1 => (A Y) X)
      map_add' := by
        intro Y Z
        change α (fun _ : Fin 1 => (A (Y + Z)) X) =
          α (fun _ : Fin 1 => (A Y) X) + α (fun _ : Fin 1 => (A Z) X)
        rw [map_add]
        exact tensor0S_one_apply_add (I := I) α ((A Y) X) ((A Z) X)
      map_smul' := by
        intro c Y
        change α (fun _ : Fin 1 => (A (c • Y)) X) =
          c • α (fun _ : Fin 1 => (A Y) X)
        rw [map_smul]
        exact tensor0S_one_apply_smul (I := I) α c ((A Y) X) }





noncomputable def connectionDifferenceOutput
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
            (connDiffSlotCLM (I := I) A α X)
        map_add' := by
          intro X Y
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change α (fun _ : Fin 1 => (A Z) (X + Y)) =
            α (fun _ : Fin 1 => (A Z) X) + α (fun _ : Fin 1 => (A Z) Y)
          rw [map_add]
          exact tensor0S_one_apply_add (I := I) α ((A Z) X) ((A Z) Y)
        map_smul' := by
          intro c X
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change α (fun _ : Fin 1 => (A Z) (c • X)) =
            c • α (fun _ : Fin 1 => (A Z) X)
          rw [map_smul]
          exact tensor0S_one_apply_smul (I := I) α c ((A Z) X) })

@[simp]
theorem connectionDifferenceOutput_apply
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    connectionDifferenceOutput (I := I) A α v =
      α (fun _ : Fin 1 => (A (v 1)) (v 0)) := by
  unfold connectionDifferenceOutput
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (connDiffSlotCLM (I := I) A α (v 0))) (fun i : Fin 1 => v i.succ) =
      α (fun _ : Fin 1 => (A (v 1)) (v 0))
  have htail : (fun i : Fin 1 => v i.succ) = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  rw [htail]
  rfl

@[simp]
theorem connectionDifferenceOutput_apply_slots
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    connectionDifferenceOutput (I := I) A α
        (fun q : Fin 2 => if q = 0 then X else Y) =
      α (fun _ : Fin 1 => (A Y) X) := by
  rw [connectionDifferenceOutput_apply]
  simp




noncomputable def connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        connectionDifferenceOutput (I := I)
          (CovariantDerivative.difference cov cov' x) α
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        rw [connectionDifferenceOutput_apply]
        change (α + β) (fun _ : Fin 1 =>
            (CovariantDerivative.difference cov cov' x (v 1)) (v 0)) =
          connectionDifferenceOutput (I := I)
              (CovariantDerivative.difference cov cov' x) α v +
            connectionDifferenceOutput (I := I)
              (CovariantDerivative.difference cov cov' x) β v
        rw [connectionDifferenceOutput_apply, connectionDifferenceOutput_apply]
        rfl
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        rw [connectionDifferenceOutput_apply]
        change (c • α) (fun _ : Fin 1 =>
            (CovariantDerivative.difference cov cov' x (v 1)) (v 0)) =
          c • connectionDifferenceOutput (I := I)
            (CovariantDerivative.difference cov cov' x) α v
        rw [connectionDifferenceOutput_apply]
        rfl }

@[simp]
theorem connectionDifferenceTensorAt_apply
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    connectionDifferenceTensorAt (I := I) cov cov' x α v =
      α (fun _ : Fin 1 =>
        ((CovariantDerivative.difference cov cov' x) (v 1)) (v 0)) := by
  change connectionDifferenceOutput (I := I)
      (CovariantDerivative.difference cov cov' x) α v =
    α (fun _ : Fin 1 =>
      ((CovariantDerivative.difference cov cov' x) (v 1)) (v 0))
  rw [connectionDifferenceOutput_apply]

@[simp]
theorem connectionDifferenceTensorAt_apply_slots
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    connectionDifferenceTensorAt (I := I) cov cov' x α
        (fun q : Fin 2 => if q = 0 then X else Y) =
      α (fun _ : Fin 1 =>
        ((CovariantDerivative.difference cov cov' x) Y) X) := by
  rw [connectionDifferenceTensorAt_apply]
  simp



theorem componentRS_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (i j k : Idx) :
    componentRS_gen (I := I) basis (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      basis.coord k
        (((CovariantDerivative.difference cov cov' x) (basis j)) (basis i)) := by
  rw [componentRS_apply_gen, connectionDifferenceTensorAt_apply]
  simp [basisTensor0S_apply]

end Tensor0SBundle
