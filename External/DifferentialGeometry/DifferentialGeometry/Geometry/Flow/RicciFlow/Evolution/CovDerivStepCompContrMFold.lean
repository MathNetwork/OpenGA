import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContrNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompLinear

set_option autoImplicit false
set_option linter.style.longLine false














noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]



def iterDl (D : ∀ {r : ℕ}, ((Fin r → Idx) → Real) → ((Fin (r + 1) → Idx) → Real))
    {r : ℕ} : (m : ℕ) → ((Fin r → Idx) → Real) → ((Fin (r + m) → Idx) → Real)
  | 0, T => T
  | (m + 1), T => D (iterDl D m T)



def iterDU (DU : ∀ {r : ℕ}, ((Fin (r + 1) → Idx) → Real) → ((Fin (r + 2) → Idx) → Real))
    {p : ℕ} : (c : ℕ) → ((Fin (p + 1) → Idx) → Real) → ((Fin ((p + c) + 1) → Idx) → Real)
  | 0, A => A
  | (c + 1), A => DU (iterDU DU c A)

omit [Fintype Idx] [DecidableEq Idx] in
@[simp] theorem iterDl_zero
    (D : ∀ {r : ℕ}, ((Fin r → Idx) → Real) → ((Fin (r + 1) → Idx) → Real))
    {r : ℕ} (T : (Fin r → Idx) → Real) : iterDl D 0 T = T := rfl

omit [Fintype Idx] [DecidableEq Idx] in
@[simp] theorem iterDl_succ
    (D : ∀ {r : ℕ}, ((Fin r → Idx) → Real) → ((Fin (r + 1) → Idx) → Real))
    {r : ℕ} (m : ℕ) (T : (Fin r → Idx) → Real) :
    iterDl D (m + 1) T = D (iterDl D m T) := rfl

omit [Fintype Idx] [DecidableEq Idx] in
@[simp] theorem iterDU_zero
    (DU : ∀ {r : ℕ}, ((Fin (r + 1) → Idx) → Real) → ((Fin (r + 2) → Idx) → Real))
    {p : ℕ} (A : (Fin (p + 1) → Idx) → Real) : iterDU DU 0 A = A := rfl

omit [Fintype Idx] [DecidableEq Idx] in
@[simp] theorem iterDU_succ
    (DU : ∀ {r : ℕ}, ((Fin (r + 1) → Idx) → Real) → ((Fin (r + 2) → Idx) → Real))
    {p : ℕ} (c : ℕ) (A : (Fin (p + 1) → Idx) → Real) :
    iterDU DU (c + 1) A = DU (iterDU DU c A) := rfl

end DifferentialGeometry.PDE.RicciFlow
