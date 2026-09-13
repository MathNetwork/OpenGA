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
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
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
import Mathlib.Topology.VectorBundle.Hom
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Tangent

set_option autoImplicit false

namespace DifferentialGeometry

namespace Tensor0SBundle

open Bundle Set DifferentialGeometry.TensorLieDeriv

open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

variable {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I ∞ M]

omit [CompleteSpace 𝕜] in
theorem tensor0SConstInChart_contMDiffAt_of_mem {r : ℕ}
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) {x : M}
    (hx : x ∈ (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun p : M => Tensor0SSpace r I p) x₀).baseSet) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x := by
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx' : x ∈ e.baseSet := by simpa [e] using hx
  refine (e.contMDiffAt_section_iff hx').mpr ?_
  have hconst : ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
      (fun _ : M => β) x := contMDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx'] with p hp
  have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
    e.coe_linearMapAt_of_mem (R := 𝕜) hp
  change (e ⟨p, e.symmL 𝕜 p β⟩).2 = β
  calc
    (e ⟨p, e.symmL 𝕜 p β⟩).2 =
        (e.linearMapAt 𝕜 p) (e.symmL 𝕜 p β) :=
      (congrFun hcoe (e.symmL 𝕜 p β)).symm
    _ = β := e.continuousLinearMapAt_symmL (R := 𝕜) hp β

omit [CompleteSpace 𝕜] in
theorem tensor0SConstInChart_contMDiffAt {r : ℕ}
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
  exact tensor0SConstInChart_contMDiffAt_of_mem
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    x₀ β (mem_baseSet_trivializationAt
      (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)

end Tensor0SBundle

end DifferentialGeometry
