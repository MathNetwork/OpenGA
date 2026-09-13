
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

lemma hasDerivAt_prod_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (σ : Equiv.Perm n) :
    HasDerivAt (fun t => ∏ i, G t (σ i) i)
      (∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k) t := by
  classical
  have hfactor : ∀ k ∈ (Finset.univ : Finset n),
      HasDerivAt (fun t : ℝ => G t (σ k) k) (G' (σ k) k) t :=
    fun k _ => hG (σ k) k
  exact HasDerivAt.fun_finsetProd hfactor

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
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
  classical
  have hexpand : (fun s : ℝ => (G s).det)
      = (fun s : ℝ =>
          ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i, G s (σ i) i) := by
    funext s
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexpand]
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      HasDerivAt
        (fun s : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, G s (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
    intro σ _
    have hprod := hasDerivAt_prod_of_entries (n := n) G G' t hG σ
    have hmul := hprod.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))
    have hsum_eq :
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k
          = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k := by
      simp [smul_eq_mul]
    rw [← hsum_eq]
    exact hmul
  exact HasDerivAt.fun_sum hterm
