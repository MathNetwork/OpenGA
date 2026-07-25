import DifferentialGeometry.Analysis.Time
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic
import DifferentialGeometry.Tensor.Multilinear.Tensor
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
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Tensor.Product.Pretrivialization
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.LinearAlgebra.Alternating.Basic
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Geometry.Coordinates.Tensor

set_option autoImplicit false
set_option linter.style.longLine false


















namespace DifferentialGeometry
namespace Tensor

noncomputable section

open scoped TensorProduct Manifold ContDiff



structure CovariantTensorBundleSupport
    (R : Type*) [CommSemiring R] (Point : Type*) where

  Vec : Point -> Type*

  Tensor0 : Nat -> Type*

  eval0 : {s : Nat} -> Tensor0 s -> (x : Point) -> (Fin s -> Vec x) -> R

  tensorProduct0 : {s q : Nat} -> Tensor0 s -> Tensor0 q -> Tensor0 (s + q)

  tensorProduct0_eval :
    forall {s q : Nat} (A : Tensor0 s) (B : Tensor0 q)
      (x : Point) (v : Fin (s + q) -> Vec x),
      eval0 (tensorProduct0 A B) x v =
        eval0 A x (v ∘ Fin.castAdd q) * eval0 B x (v ∘ Fin.natAdd s)

  trace02 : Tensor0 2 -> Point -> R

  inner02 : Tensor0 2 -> Tensor0 2 -> Point -> R

  normSq02 : Tensor0 2 -> Point -> R

  normSq02_eq_inner02 :
    forall (A : Tensor0 2) (x : Point), normSq02 A x = inner02 A A x

namespace CovariantTensorBundleSupport

variable {R : Type*} [CommSemiring R] {Point : Type*}
variable (S : CovariantTensorBundleSupport R Point)


def component0 {s : Nat} (A : S.Tensor0 s)
    (x : Point) (frame : Nat -> S.Vec x) (slots : Fin s -> Nat) : R :=
  S.eval0 A x (fun i => frame (slots i))

@[simp] theorem component0_eval {s : Nat} (A : S.Tensor0 s)
    (x : Point) (frame : Nat -> S.Vec x) (slots : Fin s -> Nat) :
    S.component0 A x frame slots = S.eval0 A x (fun i => frame (slots i)) := by
  rfl

@[simp] theorem tensorProduct0_eval' {s q : Nat}
    (A : S.Tensor0 s) (B : S.Tensor0 q)
    (x : Point) (v : Fin (s + q) -> S.Vec x) :
    S.eval0 (S.tensorProduct0 A B) x v =
      S.eval0 A x (v ∘ Fin.castAdd q) * S.eval0 B x (v ∘ Fin.natAdd s) :=
  S.tensorProduct0_eval A B x v

@[simp] theorem normSq02_eq_inner02' (A : S.Tensor0 2) (x : Point) :
    S.normSq02 A x = S.inner02 A A x :=
  S.normSq02_eq_inner02 A x

end CovariantTensorBundleSupport




structure Section12ScalarHeatSupport
    (R : Type*) [Sub R] (Time Point : Type*) where
  dt : (Time -> Point -> R) -> Time -> Point -> R
  laplacian : (Time -> Point -> R) -> Time -> Point -> R

namespace Section12ScalarHeatSupport

variable {R : Type*} [Sub R] {Time Point : Type*}
variable (H : Section12ScalarHeatSupport R Time Point)


def heat (f : Time -> Point -> R) (t : Time) (x : Point) : R :=
  H.dt f t x - H.laplacian f t x

@[simp] theorem heat_eq (f : Time -> Point -> R) (t : Time) (x : Point) :
    H.heat f t x = H.dt f t x - H.laplacian f t x := by
  rfl

end Section12ScalarHeatSupport




def TracefreeRicciNormSqDecomposition
    {R : Type*} [Mul R] [Sub R] (nInv : R)
    {Time Point : Type*}
    (scalarCurvature ricciNormSq tracefreeRicciNormSq : Time -> Point -> R) :
    Prop :=
  forall t x,
    tracefreeRicciNormSq t x =
      ricciNormSq t x - nInv * scalarCurvature t x * scalarCurvature t x





structure Section12CurvatureScalars
    (R : Type*) [Mul R] [Sub R] (Time Point : Type*) where
  scalarCurvature : Time -> Point -> R
  ricciNormSq : Time -> Point -> R
  tracefreeRicciNormSq : Time -> Point -> R
  tracefreeRicciNormSq_nInv : R
  tracefreeRicciNormSq_decomp :
    TracefreeRicciNormSqDecomposition tracefreeRicciNormSq_nInv
      scalarCurvature ricciNormSq tracefreeRicciNormSq
  cubicQ : Time -> Point -> R

namespace Section12CurvatureScalars

variable {R : Type*} [Mul R] [Sub R] {Time Point : Type*}


theorem tracefreeRicciNormSqDecomposition
    (Q : Section12CurvatureScalars R Time Point) :
    TracefreeRicciNormSqDecomposition Q.tracefreeRicciNormSq_nInv
      Q.scalarCurvature Q.ricciNormSq Q.tracefreeRicciNormSq :=
  Q.tracefreeRicciNormSq_decomp

end Section12CurvatureScalars



def CubicReactionIdentity
    {R : Type*} [OfNat R 2] [Mul R] [Sub R]
    {Time Point : Type*} (Q : Section12CurvatureScalars R Time Point)
    (reaction : Time -> Point -> R) : Prop :=
  forall t x,
    2 * Q.scalarCurvature t x * reaction t x =
      2 * Q.ricciNormSq t x * Q.ricciNormSq t x - Q.cubicQ t x








namespace MultilinearBundle

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup K] [NormedSpace K K]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace K EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners K EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B -> Type*} [forall x, NormedAddCommGroup (E x)]
  [forall x, NormedSpace K (E x)]
  [TopologicalSpace (Bundle.TotalSpace F E)]
  [FiberBundle F E] [VectorBundle K F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]








noncomputable abbrev covariantTensorProductBundleEquiv (s q : Nat) :=
  MultilinearSection.multilinearBundle_tensorProduct_equiv
    (𝕜 := K) (F := F) (E := E) (IB := IB) (n := n) (s := s) (q := q)

end MultilinearBundle

end

end Tensor
end DifferentialGeometry
