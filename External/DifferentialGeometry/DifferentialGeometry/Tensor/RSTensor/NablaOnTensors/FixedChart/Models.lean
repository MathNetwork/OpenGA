import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Endomorphism
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

section SmoothVectorFieldRSNabla









variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_apply (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → E) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x A slots =
      A (fun a : Fin s =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x (slots a)) := by
  unfold tensor0SModelAt
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x₀
  change (((e₀.continuousMultilinearMap 𝕜 s) ⟨x, A⟩).2) slots =
    A (fun a : Fin s => e₀.symmL 𝕜 x (slots a))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl

omit [CompleteSpace 𝕜] in
theorem tensor0SModelInChart_center_eq_tensor0SModelAt (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀) =
      tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (A x₀) := by
  unfold tensor0SModelInChart
  rw [extChartAt_to_inv]


omit [CompleteSpace 𝕜] in
theorem tensor0SModelInChart_apply (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) (slots : Fin s → E) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ A y slots =
      A ((extChartAt I x₀).symm y)
        (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) (slots a)) := by
  unfold tensor0SModelInChart
  rw [tensor0SModelAt_apply]

noncomputable def tensorRSModelAt (r s : ℕ) (x₀ x : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x) :
    TensorRSModel r s 𝕜 E := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  exact ((trivializationAt (TensorRSModel r s 𝕜 E)
    (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2



omit [CompleteSpace 𝕜] in
theorem tensorRSModelAt_trivializationAt_symm (r s : ℕ) (x₀ : M)
    (T : TensorRSModel r s 𝕜 E) :
    letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ x₀
        ((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀).symm x₀ T) = T := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  unfold tensorRSModelAt
  exact congrArg Prod.snd
    ((trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀).apply_mk_symm
        (mem_baseSet_trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)
        T)



noncomputable def tensorRSModelInChart (r s : ℕ) (x₀ : M)
    (T : (x : M) →
      TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (y : E) : TensorRSModel r s 𝕜 E :=
  tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    r s x₀ ((extChartAt I x₀).symm y) (T ((extChartAt I x₀).symm y))
end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
