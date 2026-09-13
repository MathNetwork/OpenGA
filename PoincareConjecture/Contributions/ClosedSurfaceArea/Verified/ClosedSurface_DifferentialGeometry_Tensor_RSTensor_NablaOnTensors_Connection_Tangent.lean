import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
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
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
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
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth

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

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentConstInChart_self_continuousLinearMapAt
    (x : M) (v : TangentSpace I x) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x
        ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
          𝕜 x v) x =
      v := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  rw [tangentConstInChart_apply]
  exact e.symmL_continuousLinearMapAt (R := 𝕜) hx v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
omit [IsManifold I n M] in
lemma tangentConstInChart_contMDiffOn_baseSet (x₀ : M) (v : E)
    [IsManifold I (n + 1) M] :
    CMDiff[(trivializationAt E (TangentSpace I) x₀).baseSet] n
      (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v :
        (p : M) → TangentSpace I p)) := by
  let e := trivializationAt E (TangentSpace I) x₀
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  rw [e.contMDiffOn_section_baseSet_iff]
  refine (contMDiffOn_const (c := v)).congr ?_
  intro y hy
  have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
    e.coe_linearMapAt_of_mem (R := 𝕜) hy
  simpa [e, tangentConstInChart, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
    (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)

end TangentCovariantDerivative

end

end TensorLieDeriv

end DifferentialGeometry
