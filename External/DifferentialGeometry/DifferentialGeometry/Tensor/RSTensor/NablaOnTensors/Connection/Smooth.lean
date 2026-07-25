import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Model.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Model.TensorRS
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Model.Smoothness
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic







namespace CovariantDerivative

open Bundle
open scoped Manifold ContDiff








def ContMDiffCovariantDerivativeLocally
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (k : WithTop ℕ∞) : Prop :=
  ∀ ⦃u : Set M⦄, IsOpen u → ContMDiffCovariantDerivativeOn E k cov.toFun u







theorem ContMDiffCovariantDerivative.contMDiff_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    {n : WithTop ℕ∞}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivative cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (Y : ContMDiffSection I E (n + 1) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) n
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) := by
  have hY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (n + 1)
        (fun p : M =>
          (⟨p, Y p⟩ : TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    Y.contMDiff.contMDiffOn
  have hcovY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p))) Set.univ :=
    hcov.contMDiff.contMDiff hY
  have hX :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) n
        (fun p : M =>
          (⟨p, X p⟩ : TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    X.contMDiff.contMDiffOn
  rw [← contMDiffOn_univ]
  simpa using hcovY.clm_bundle_apply hX

end CovariantDerivative
