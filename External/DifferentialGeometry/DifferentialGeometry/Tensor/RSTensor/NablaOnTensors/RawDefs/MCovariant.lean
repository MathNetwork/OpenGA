import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.FixedChart.Models
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.FixedChart.Nabla0S
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
variable (n : WithTop ℕ∞ := ∞) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]






omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem modelAt_mcovRS {r s : ℕ}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (u : Set M) (x₀ : M) :
    tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ x₀
        (mcovariantDeriv_tensorRSWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) r s X ΓX T u x₀) =
      covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          X (Set.range I))
        ΓX
        (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r s x₀ (fun x => T x))
        ((extChartAt I x₀).symm ⁻¹' u ∩ Set.range I)
        (extChartAt I x₀ x₀) := by
  unfold mcovariantDeriv_tensorRSWithin
  rw [tensorRSModelAt_trivializationAt_symm]
  rfl


omit [IsManifold I n M] [IsManifold I (n + 1) M] in
omit [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_apply_slots {s : ℕ}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → E) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        slots =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          slots -
        ∑ a : Fin s,
          (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x₀ (α x₀))
            (Function.update slots a (ΓX (extChartAt I x₀ x₀) (slots a))) := by
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl


section ExtractedConnection

variable [IsManifold I 2 M]


end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
