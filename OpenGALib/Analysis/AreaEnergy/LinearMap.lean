import OpenGALib.Analysis.AreaEnergy
import OpenGALib.Algebraic.Auxiliary.OrthonormalBasisDiagonal
import Mathlib.Analysis.InnerProductSpace.NormDet

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

/-- **Math.** The area density in any orthonormal basis of a two-dimensional
domain is the intrinsic area factor of the linear map. -/
theorem areaDensity_eq_normDet (L : E →ₗ[ℝ] F) (b : OrthonormalBasis (Fin 2) ℝ E) :
    areaDensity (L (b 0)) (L (b 1)) = L.normDet := by
  apply (sq_eq_sq₀ (areaDensity_nonneg _ _) L.normDet_nonneg).mp
  have hdet : L.normDet ^ 2 = (Matrix.gram ℝ (fun i => L (b i))).det := by
    simpa using L.normDet_sq_eq_det_gram b
  rw [areaDensity_sq, hdet]
  simp only [Matrix.det_fin_two, Matrix.gram_apply, real_inner_self_eq_norm_sq,
    real_inner_comm (L (b 1)) (L (b 0))]
  ring

/-- **Math.** The two-dimensional area density is unchanged by an orthonormal
change of basis, including changes that reverse orientation. -/
theorem areaDensity_basis_independent (L : E →ₗ[ℝ] F)
    (b c : OrthonormalBasis (Fin 2) ℝ E) :
    areaDensity (L (b 0)) (L (b 1)) = areaDensity (L (c 0)) (L (c 1)) := by
  rw [areaDensity_eq_normDet L b, areaDensity_eq_normDet L c]

omit [FiniteDimensional ℝ E] in
/-- **Math.** The two-dimensional Dirichlet energy density is unchanged by
an orthonormal change of basis. -/
theorem energyDensity_basis_independent (L : E →ₗ[ℝ] F)
    (b c : OrthonormalBasis (Fin 2) ℝ E) :
    energyDensity (L (b 0)) (L (b 1)) = energyDensity (L (c 0)) (L (c 1)) := by
  have h := OrthonormalBasis.sum_apply_diagonal_invariant b c
    ((innerₗ F).compl₁₂ L L)
  simpa only [energyDensity, Fin.sum_univ_two, LinearMap.compl₁₂_apply,
    innerₗ_apply_apply, real_inner_self_eq_norm_sq] using
    congrArg (fun x : ℝ => x / 2) h

end OpenGA
