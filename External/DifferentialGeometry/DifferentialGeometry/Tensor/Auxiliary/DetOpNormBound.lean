import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Determinant

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem abs_det_le_factorial_mul_opNormPow_finrank
    (L : E →L[ℝ] E) :
    |LinearMap.det (L : E →ₗ[ℝ] E)| ≤
      ((Module.finrank ℝ E).factorial : ℝ) * ‖L‖ ^ (Module.finrank ℝ E) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set e : OrthonormalBasis (Fin n) ℝ E := stdOrthonormalBasis ℝ E with he
  set b : Module.Basis (Fin n) ℝ E := e.toBasis with hb
  set M : Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toMatrix b b (L : E →ₗ[ℝ] E) with hM
  have hopNorm_nonneg : (0 : ℝ) ≤ ‖L‖ := norm_nonneg _
  have entry_bound : ∀ i j : Fin n, |M i j| ≤ ‖L‖ := by
    intro i j
    have hMij : M i j = ⟪e i, L (e j)⟫_ℝ := by
      simp [hM, hb, LinearMap.toMatrix_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply]
    rw [hMij]
    have hCS : |⟪e i, L (e j)⟫_ℝ| ≤ ‖e i‖ * ‖L (e j)‖ :=
      abs_real_inner_le_norm (e i) (L (e j))
    have hei : ‖e i‖ = 1 := e.norm_eq_one i
    have hLej : ‖L (e j)‖ ≤ ‖L‖ * ‖e j‖ := L.le_opNorm (e j)
    have hej : ‖e j‖ = 1 := e.norm_eq_one j
    calc |⟪e i, L (e j)⟫_ℝ|
        ≤ ‖e i‖ * ‖L (e j)‖ := hCS
      _ = ‖L (e j)‖ := by rw [hei, one_mul]
      _ ≤ ‖L‖ * ‖e j‖ := hLej
      _ = ‖L‖ := by rw [hej, mul_one]
  have hdet :
      AbsoluteValue.abs (M.det) ≤
        (Fintype.card (Fin n)).factorial • ‖L‖ ^ Fintype.card (Fin n) :=
    Matrix.det_le (abv := AbsoluteValue.abs) (x := ‖L‖) entry_bound
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hMdet : M.det = LinearMap.det (L : E →ₗ[ℝ] E) := by
    simp [hM, hb, LinearMap.det_toMatrix]
  have h1 :
      |LinearMap.det (L : E →ₗ[ℝ] E)| ≤
        (Fintype.card (Fin n)).factorial • ‖L‖ ^ Fintype.card (Fin n) := by
    have := hdet
    rw [AbsoluteValue.abs_apply, hMdet] at this
    exact this
  have h2 :
      (Fintype.card (Fin n)).factorial • ‖L‖ ^ Fintype.card (Fin n) =
        ((n.factorial : ℕ) : ℝ) * ‖L‖ ^ n := by
    rw [hcard, nsmul_eq_mul]
  calc |LinearMap.det (L : E →ₗ[ℝ] E)|
      ≤ (Fintype.card (Fin n)).factorial • ‖L‖ ^ Fintype.card (Fin n) := h1
    _ = ((n.factorial : ℕ) : ℝ) * ‖L‖ ^ n := h2
    _ = (n.factorial : ℝ) * ‖L‖ ^ n := by norm_cast

end ContinuousLinearMap

end
