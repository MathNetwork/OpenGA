import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OpenGA_AreaEnergyDensities

/-!
# Area and energy densities

For the images `v`, `w` of an orthonormal tangent frame under a differential,
the area density is the square root of the Gram determinant and the energy
density is half the sum of the squared norms. The area is bounded by the
energy, with equality precisely for orthogonal vectors of equal norm.

The integral results assume measurable vector fields and integrable energy;
integrability of the area is a conclusion, not an additional assumption.
They apply on any measure space, including a restricted domain measure.
Identifying these fields with a Sobolev differential on a surface remains a
separate geometric interface. No global frame on the sphere is asserted.

Reference: Colding-Minicozzi, *Width and Finite Extinction Time of Ricci Flow*,
arXiv:0707.0108v1, equation (1.4) and the following equality discussion, p. 3.
https://arxiv.org/pdf/0707.0108v1#page=3
-/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace OpenGA

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]





lemma areaDensity_nonneg (v w : F) : 0 ≤ areaDensity v w :=
  Real.sqrt_nonneg _



lemma areaDensity_sq (v w : F) :
    areaDensity v w ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 := by
  apply Real.sq_sqrt
  have h := real_inner_mul_inner_self_le v w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith









section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v w : X → F}







end Integral

end OpenGA

/-!
# Area and energy densities of a linear map

For a linear map from a two-dimensional real inner product space, the area
density evaluated on an orthonormal basis is Mathlib's `LinearMap.normDet`.
Consequently, it is independent of the chosen orthonormal basis. The energy
density is likewise independent of that choice, by invariance of the
diagonal sum of the pulled-back inner product.

The codomain can have arbitrary dimension. No injectivity or orientation
assumption is imposed, so the results also apply to degenerate differentials
and orientation-reversing changes of frame.

This is the pointwise linear-algebra interface for the surface densities in
Colding-Minicozzi, *Width and Finite Extinction Time of Ricci Flow*,
arXiv:0707.0108v1, equation (1.4), p. 3. Applying it to manifold derivatives
and constructing global surface integrals remain separate steps.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace OpenGA

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]







end OpenGA

set_option autoImplicit false
open scoped InnerProductSpace
open OpenGA
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** The area density in any orthonormal basis of a two-dimensional
domain is the intrinsic area factor of the linear map. -/
theorem solution (L : E →ₗ[ℝ] F) (b : OrthonormalBasis (Fin 2) ℝ E) :
    areaDensity (L (b 0)) (L (b 1)) = L.normDet := by
  apply (sq_eq_sq₀ (areaDensity_nonneg _ _) L.normDet_nonneg).mp
  have hdet : L.normDet ^ 2 = (Matrix.gram ℝ (fun i => L (b i))).det := by
    simpa using L.normDet_sq_eq_det_gram b
  rw [areaDensity_sq, hdet]
  simp only [Matrix.det_fin_two, Matrix.gram_apply, real_inner_self_eq_norm_sq,
    real_inner_comm (L (b 1)) (L (b 0))]
  ring
