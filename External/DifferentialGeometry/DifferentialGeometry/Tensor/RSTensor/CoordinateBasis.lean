import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false









noncomputable section

namespace Tensor0SBundle

open Bundle Module
open scoped Manifold BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section ModelBasis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]





end ModelBasis

section Tensor0S

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {s : Nat} {x : M}


omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_sum_apply {ι : Type*} [Fintype ι]
    (T : ι -> Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      change (0 : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v = 0
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change T a v + (∑ i ∈ S, T i) v = T a v + ∑ i ∈ S, T i v
      rw [ih]




theorem basisTensor0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (slots : Fin s -> Idx) (v : Fin s -> TangentSpace I x) :
    basisTensor0S (I := I) basis slots v =
      ∏ a : Fin s, basis.coord (slots a) (v a) := by
  change (continuousMultilinearMapBasis basis s slots) v =
    ∏ a : Fin s, basis.coord (slots a) (v a)
  rw [continuousMultilinearMapBasis_apply]
  simp [continuousMultilinearMapBasisElem]



theorem tensor0S_apply_eq_sum
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    A v =
      ∑ slots : Fin s -> Idx,
        component0S (I := I) basis A slots *
          ∏ a : Fin s, basis.coord (slots a) (v a) := by
  conv_lhs => rw [← (tensor0SBasis (I := I) basis s).sum_repr A]
  rw [tensor0S_sum_apply]
  refine Finset.sum_congr rfl ?_
  intro slots _hslots
  rw [tensor0SBasis_repr]
  change component0S (I := I) basis A slots *
      ((tensor0SBasis (I := I) basis s) slots) v =
    component0S (I := I) basis A slots *
      ∏ a : Fin s, basis.coord (slots a) (v a)
  have hb :
      ((tensor0SBasis (I := I) basis s) slots) v =
        ∏ a : Fin s, basis.coord (slots a) (v a) := by
    change basisTensor0S (I := I) basis slots v =
      ∏ a : Fin s, basis.coord (slots a) (v a)
    exact basisTensor0S_apply (I := I) basis slots v
  rw [hb]

end Tensor0S

end Tensor0SBundle
