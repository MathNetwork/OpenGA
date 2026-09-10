import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_Section
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.VectorBundle.Basic

namespace DifferentialGeometry

namespace TensorLieDeriv

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    DifferentialGeometry.Tensor0SBundle Function

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]

variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section TangentCovariantDerivative

variable [IsManifold I 1 M]

noncomputable def tangentConstInChart (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma tangentConstInChart_apply (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v := by
  rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_add (x₀ : M) (v w : E) :
    (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
        tangentConstInChart x₀ w := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (v + w) =
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v +
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p w
  exact map_add _ _ _

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_smul (x₀ : M) (a : 𝕜) (v : E) :
    (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (a • v) =
    a • (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v
  exact map_smul _ _ _

section ConnectionEndomorphism

variable [IsManifold I 2 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma mdifferentiableAt_tangentConstInChart_of_mem
    {x₀ p : M} (v : E)
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p := by
  let e := trivializationAt E (TangentSpace I) x₀
  refine (e.mdifferentiableAt_section_iff I
    (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) hp).mpr ?_
  have hconst :
      (fun y : M =>
        (e ((T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) y)).2) =ᶠ[𝓝 p]
          fun _ : M => v := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with y hy
    have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hy
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
      (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)
  exact hconst.mdifferentiableAt_iff.mpr mdifferentiableAt_const

end ConnectionEndomorphism

end TangentCovariantDerivative

end

end TensorLieDeriv

end DifferentialGeometry
