import Theorems.Thm_DifferentialGeometry_Integral_Measure_hasDerivAt_det_of_entries
import Theorems.Thm_DifferentialGeometry_Integral_Measure_perm_sum_eq_trace_adjugate_mul
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace


section

noncomputable section

open Matrix

open scoped Matrix BigOperators

namespace DifferentialGeometry

namespace Integral

namespace Measure

section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem hasDerivAt_det_eq_trace_adjugate_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (trace (adjugate (G t) * G')) t := by
  have h := hasDerivAt_det_of_entries (n := n) G G' t hG
  rw [perm_sum_eq_trace_adjugate_mul (n := n) (G t) G'] at h
  exact h

lemma adjugate_eq_det_smul_inv
    {A : Matrix n n ℝ} (h : IsUnit A.det) :
    adjugate A = A.det • A⁻¹ := by
  rw [Matrix.inv_def]
  rw [smul_smul]
  rw [Ring.mul_inverse_cancel _ h]
  rw [one_smul]

theorem hasDerivAt_det_eq_det_mul_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hunit : IsUnit (G t).det) :
    HasDerivAt (fun t => (G t).det)
      ((G t).det * trace ((G t)⁻¹ * G')) t := by
  have h := hasDerivAt_det_eq_trace_adjugate_mul (n := n) G G' t hG
  have hadj := adjugate_eq_det_smul_inv (n := n) (A := G t) hunit
  have hrewrite : trace (adjugate (G t) * G') = (G t).det * trace ((G t)⁻¹ * G') := by
    rw [hadj]
    rw [Matrix.smul_mul]
    rw [Matrix.trace_smul]
    rfl
  rw [hrewrite] at h
  exact h

end Jacobi

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Matrix

open scoped Matrix BigOperators

namespace DifferentialGeometry
end DifferentialGeometry
open _root_.DifferentialGeometry

namespace DifferentialGeometry.Integral
end DifferentialGeometry.Integral
open _root_.DifferentialGeometry
open _root_.DifferentialGeometry.Integral

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry
open _root_.DifferentialGeometry.Integral
open _root_.DifferentialGeometry.Integral.Measure

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

theorem solution
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det) t := by
  have hunit : IsUnit (G t).det := (ne_of_gt hpos).isUnit
  have hdet := hasDerivAt_det_eq_det_mul_trace_inv_mul (n := n) G G' t hG hunit
  have hne : (G t).det ≠ 0 := ne_of_gt hpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (G t).det)) (G t).det :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.comp t hdet
  have hsqrt_ne : Real.sqrt (G t).det ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hkey :
      (1 / (2 * Real.sqrt (G t).det)) * ((G t).det * trace ((G t)⁻¹ * G'))
        = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by
    have hdiv : (G t).det / Real.sqrt (G t).det = Real.sqrt (G t).det := by
      rw [eq_comm, eq_div_iff hsqrt_ne]
      exact Real.mul_self_sqrt hpos.le
    calc (1 / (2 * Real.sqrt (G t).det))
            * ((G t).det * trace ((G t)⁻¹ * G'))
        = ((G t).det / Real.sqrt (G t).det) * ((1 / 2) * trace ((G t)⁻¹ * G')) := by
          ring
      _ = Real.sqrt (G t).det * ((1 / 2) * trace ((G t)⁻¹ * G')) := by
          rw [hdiv]
      _ = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by ring
  rw [hkey] at hcomp
  simpa [Function.comp] using! hcomp
