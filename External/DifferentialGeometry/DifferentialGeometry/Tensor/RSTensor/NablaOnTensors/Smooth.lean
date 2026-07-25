import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TensorRS
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S








namespace Tensor0SBundle

noncomputable section

open Bundle Set TensorLieDeriv
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]



noncomputable def nabla0S_smooth (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  nabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α
    (nabla0S_reg (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov hcov X α)



noncomputable def nablaRS_smooth (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s :=
  nablaRS (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T
    (nablaRS_reg (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov hcov X T)

@[simp] theorem nabla0S_smooth_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0S_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov hcov X α x =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x := rfl

@[simp] theorem nablaRS_smooth_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRS_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov hcov X T x =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x := rfl

end

end Tensor0SBundle
