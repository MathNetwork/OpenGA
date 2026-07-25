import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower

set_option autoImplicit false
set_option linter.style.longLine false











noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


omit [DecidableEq Idx] in
theorem covDerivStepComp_add {r : ℕ}
    (extA extB : (Fin r → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A B : (Fin r → Idx) → Real) (n : Fin (r + 1) → Idx) :
    covDerivStepComp (fun m d => extA m d + extB m d) chr
        (fun k => A k + B k) n =
      covDerivStepComp extA chr A n + covDerivStepComp extB chr B n := by
  classical
  unfold covDerivStepComp
  have hsum :
      (∑ s : Fin r, ∑ p : Idx,
          chr (n 0) (Fin.tail n s) p *
            (A (Function.update (Fin.tail n) s p) + B (Function.update (Fin.tail n) s p))) =
        (∑ s : Fin r, ∑ p : Idx,
            chr (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p)) +
          (∑ s : Fin r, ∑ p : Idx,
            chr (n 0) (Fin.tail n s) p * B (Function.update (Fin.tail n) s p)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  ring


omit [DecidableEq Idx] in
theorem covDerivStepComp_smul {r : ℕ} (c : Real)
    (ext : (Fin r → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) (n : Fin (r + 1) → Idx) :
    covDerivStepComp (fun m d => c * ext m d) chr (fun k => c * A k) n =
      c * covDerivStepComp ext chr A n := by
  classical
  unfold covDerivStepComp
  have hsum :
      (∑ s : Fin r, ∑ p : Idx,
          chr (n 0) (Fin.tail n s) p * (c * A (Function.update (Fin.tail n) s p))) =
        c * ∑ s : Fin r, ∑ p : Idx,
          chr (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  ring

end DifferentialGeometry.PDE.RicciFlow
