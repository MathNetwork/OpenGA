import DifferentialGeometry.Tensor.RSTensor.Field










namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]



noncomputable def TensorRSField.rs0 {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) n T
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) n)

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.rs0_apply {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    TensorRSField.rs0 (n := n) T x =
      T x (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) := by
  rw [TensorRSField.rs0, tensorRSField_applyInput_apply]

omit [IsManifold I (n + 1) M] in
private theorem rankZero_eq_smul_one
    (x : M) (c : Tensor0SSpace 0 I x) :
    c = tensor0SSpace_evalScalar x c •
      Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x := by
  apply (tensor0SSpace_continuousLinearEquiv 0 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel c v =
    Tensor0SSpace.toModel
      (tensor0SSpace_evalScalar x c •
        Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) n x) v
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SField.one0_apply, smul_eq_mul, mul_one,
    Tensor0SSpace.evalScalar_apply]
  exact congrArg (Tensor0SSpace.toModel c) (Subsingleton.elim v Fin.elim0)



omit [IsManifold I (n + 1) M] in
theorem TensorRSField.toRS0_rs0 {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (TensorRSField.rs0 (n := n) T).toTensorRSField n = T := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SField.toRS0_apply, TensorRSField.rs0_apply]
  calc
    tensor0SSpace_evalScalar x c •
          T x (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) n x) =
        T x (tensor0SSpace_evalScalar x c •
          Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) n x) := by
          rw [map_smul]
    _ = T x c := congrArg (T x) (rankZero_eq_smul_one (n := n) x c).symm


omit [IsManifold I (n + 1) M] in
theorem TensorRSField.rs0_toRS0 {s : ℕ}
    (A : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.rs0 (n := n) (A.toTensorRSField n) = A := by
  apply ContMDiffSection.ext
  intro x
  rw [TensorRSField.rs0_apply, Tensor0SField.toRS0_apply]
  have hone : tensor0SSpace_evalScalar x
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    exact Tensor0SField.one0_apply (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n x Fin.elim0
  rw [hone, one_smul]


noncomputable def TensorRSField.scalar0
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    M → 𝕜 :=
  (TensorRSField.rs0 (n := n) T).toScalarField n


theorem TensorRSField.scalar0_smooth
  (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) n (TensorRSField.scalar0 (n := n) T) :=
  Tensor0SField.toScalarField_contMDiff n inferInstance (TensorRSField.rs0 (n := n) T)

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_zero :
    TensorRSField.scalar0 (n := n)
        (0 : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) =
      0 := by
  funext x
  simp [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply]
  rw [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_add
    (S T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (S + T) =
      TensorRSField.scalar0 (n := n) S + TensorRSField.scalar0 (n := n) T := by
  funext x
  simp [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_smul
    (c : 𝕜)
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (c • T) =
      c • TensorRSField.scalar0 (n := n) T := by
  funext x
  simp [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply]
  rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_neg
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (-T) =
      -TensorRSField.scalar0 (n := n) T := by
  rw [show -T = (-1 : 𝕜) • T by simp, TensorRSField.scalar0_smul]
  simp

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_sub
    (S T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (S - T) =
      TensorRSField.scalar0 (n := n) S - TensorRSField.scalar0 (n := n) T := by
  rw [sub_eq_add_neg, TensorRSField.scalar0_add, TensorRSField.scalar0_neg]
  rw [sub_eq_add_neg]



theorem TensorRSField.lift_scalar0
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (Tensor0SField.fromScalarField n (TensorRSField.scalar0 (n := n) T)
      (TensorRSField.scalar0_smooth (n := n) T)).toTensorRSField n = T := by
  calc
    (Tensor0SField.fromScalarField n (TensorRSField.scalar0 (n := n) T)
          (TensorRSField.scalar0_smooth (n := n) T)).toTensorRSField n =
        (TensorRSField.rs0 (n := n) T).toTensorRSField n := by
          congr 1
          simp [TensorRSField.scalar0]
    _ = T := TensorRSField.toRS0_rs0 (n := n) T

end

end Tensor0SBundle
