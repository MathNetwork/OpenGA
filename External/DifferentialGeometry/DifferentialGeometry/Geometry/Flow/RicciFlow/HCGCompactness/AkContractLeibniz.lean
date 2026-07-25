import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.GammaAlgebra

set_option autoImplicit false
set_option linter.style.longLine false






















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def covD2 (Γ : ι → ι → Real) (g dg : ι → ι → Real) (i j : ι) : Real :=
  dg i j - (∑ p : ι, Γ p i * g p j) - (∑ p : ι, Γ p j * g i p)



def covD12 (Γ : ι → ι → Real) (A dA : ι → ι → ι → Real) (k i j : ι) : Real :=
  dA k i j + (∑ p : ι, Γ k p * A p i j) -
    (∑ p : ι, Γ p i * A k p j) - (∑ p : ι, Γ p j * A k i p)



def starAg (A : ι → ι → ι → Real) (g : ι → ι → Real) (i j d : ι) : Real :=
  ∑ k : ι, A k i j * g k d



def dStarAg (A dA : ι → ι → ι → Real) (g dg : ι → ι → Real) (i j d : ι) : Real :=
  ∑ k : ι, (dA k i j * g k d + A k i j * dg k d)




omit [DecidableEq ι] in
theorem covD3_starAg_leibniz
    (Γ : ι → ι → Real) (A dA : ι → ι → ι → Real) (g dg : ι → ι → Real)
    (i j d : ι) :
    covD3 Γ (starAg A g) (dStarAg A dA g dg) i j d =
      starAg (covD12 Γ A dA) g i j d + starAg A (covD2 Γ g dg) i j d := by
  classical
  unfold covD3 starAg dStarAg covD12 covD2

  have hL :
      (∑ k : ι, (dA k i j + (∑ p : ι, Γ k p * A p i j) -
          (∑ p : ι, Γ p i * A k p j) - (∑ p : ι, Γ p j * A k i p)) * g k d) =
        (∑ k : ι, dA k i j * g k d) +
          (∑ k : ι, (∑ p : ι, Γ k p * A p i j) * g k d) -
          (∑ k : ι, (∑ p : ι, Γ p i * A k p j) * g k d) -
          (∑ k : ι, (∑ p : ι, Γ p j * A k i p) * g k d) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hR :
      (∑ k : ι, A k i j * (dg k d - (∑ p : ι, Γ p k * g p d) -
          (∑ p : ι, Γ p d * g k p))) =
        (∑ k : ι, A k i j * dg k d) -
          (∑ k : ι, A k i j * (∑ p : ι, Γ p k * g p d)) -
          (∑ k : ι, A k i j * (∑ p : ι, Γ p d * g k p)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

  have hD :
      (∑ k : ι, (dA k i j * g k d + A k i j * dg k d)) =
        (∑ k : ι, dA k i j * g k d) + (∑ k : ι, A k i j * dg k d) :=
    Finset.sum_add_distrib
  rw [hD, hL, hR]

  have hC1 :
      (∑ k : ι, (∑ p : ι, Γ p i * A k p j) * g k d) =
        ∑ p : ι, Γ p i * ∑ k : ι, A k p j * g k d := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  have hC2 :
      (∑ k : ι, (∑ p : ι, Γ p j * A k i p) * g k d) =
        ∑ p : ι, Γ p j * ∑ k : ι, A k i p * g k d := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  have hC3 :
      (∑ k : ι, A k i j * (∑ p : ι, Γ p d * g k p)) =
        ∑ p : ι, Γ p d * ∑ k : ι, A k i j * g k p := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring

  have hcancel :
      (∑ k : ι, (∑ p : ι, Γ k p * A p i j) * g k d) =
        ∑ k : ι, A k i j * (∑ p : ι, Γ p k * g p d) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hC1, hC2, hC3, hcancel]
  ring
