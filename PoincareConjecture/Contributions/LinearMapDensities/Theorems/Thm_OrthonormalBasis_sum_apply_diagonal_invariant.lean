import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearMap

open OrthonormalBasis
variable {ι ι' : Type*} [Fintype ι] [Fintype ι']
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
open scoped InnerProductSpace

theorem OrthonormalBasis.sum_apply_diagonal_invariant
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι' ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) :
    ∑ i, B (b i) (b i) = ∑ i, B (b' i) (b' i) := by sorry
