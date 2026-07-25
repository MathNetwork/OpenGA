import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SNabla

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace TensorRSNabla

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def tensorRSCovariantDerivative (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)

noncomputable instance tensorRSCovariantDerivative_contMDiff (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (tensorRSCovariantDerivative I M r s cov) ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)

omit [CompleteSpace E] in
theorem tensorRSCovariantDerivative_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M r s cov τ x v) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s cov
        (fun y =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from τ y) (w y)) x v -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
    τ w x v

omit [CompleteSpace E] in
theorem tensorRSCovariantDerivative_apply_of_mdifferentiableAt (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (τ : Π x : M, TensorRSSpace r s I x)
    (w : Π x : M, Tensor0SSpace r I x)
    (V_field : Π x : M, TangentSpace I x)
    {x : M}
    (hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (τ y)) x)
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (w y)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (V_field y)) x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M r s cov τ x (V_field x)) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s cov
        (fun y =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from τ y) (w y))
          x (V_field x) -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x (V_field x)) := by
  exact HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y)
    (Tensor0SModel s ℝ E) (fun y : M => Tensor0SSpace s I y)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
    τ hτ hV hw

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel 1 2 ℝ E)
      (fun x : M => TensorRSSpace 1 2 I x) :=
  tensorRSCovariantDerivative I M 1 2 cov

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (tensorRSCovariantDerivative I M 1 2 cov) ∞ :=
  inferInstance

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel 2 1 ℝ E)
      (fun x : M => TensorRSSpace 2 1 I x) :=
  tensorRSCovariantDerivative I M 2 1 cov

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (tensorRSCovariantDerivative I M 2 1 cov) ∞ :=
  inferInstance

end TensorRSNabla

end
