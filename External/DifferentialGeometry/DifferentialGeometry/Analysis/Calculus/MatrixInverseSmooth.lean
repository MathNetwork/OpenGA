import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse



















noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]



theorem contDiff_det_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) :
    ContDiff ℝ ∞ (fun x => (N x).det) := by
  classical
  simp_rw [Matrix.det_apply]
  exact ContDiff.sum (fun σ _ => ContDiff.const_smul (Equiv.Perm.sign σ)
    (contDiff_prod (fun i _ => hN (σ i) i)))




theorem contDiff_adjugate_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) (k l : Fin n) :
    ContDiff ℝ ∞ (fun x => (N x).adjugate k l) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  refine contDiff_det_of_entries (fun x => (N x).updateRow l (Pi.single k 1)) (fun a b => ?_)
  rcases eq_or_ne a l with h | h
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact hN a b




theorem contDiffAt_inv_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) {x₀ : X} (hx₀ : (N x₀).det ≠ 0)
    (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun x => (N x)⁻¹ k l) x₀ := by
  have hcongr : (fun x => (N x)⁻¹ k l) = fun x => ((N x).det)⁻¹ * (N x).adjugate k l := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiff_det_of_entries N hN).contDiffAt.inv hx₀).mul
    (contDiff_adjugate_of_entries N hN k l).contDiffAt

end Analysis
end DifferentialGeometry

end
