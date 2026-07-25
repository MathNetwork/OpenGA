import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false










noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Topology
open ContinuousLinearMap Ring Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [HasSummableGeomSeries R]


theorem contDiffOn_ringInverse (n : WithTop ℕ∞) :
    ContDiffOn 𝕜 n Ring.inverse {y : R | IsUnit y} := by
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨u, rfl⟩ := hy
  exact (contDiffAt_ringInverse 𝕜 u).contDiffWithinAt



set_option synthInstance.maxHeartbeats 1000000 in


theorem norm_iteratedFDerivWithin_ringInverse_le : ∀ (i : ℕ) (x : Rˣ),
    ‖iteratedFDerivWithin 𝕜 i Ring.inverse {y : R | IsUnit y} (x : R)‖
      ≤ (i.factorial : ℝ) * ‖(↑x⁻¹ : R)‖ ^ (i + 1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
  intro x
  set S : Set R := {y : R | IsUnit y} with hSdef
  have hSopen : IsOpen S := Units.isOpen
  have hSu : UniqueDiffOn 𝕜 S := hSopen.uniqueDiffOn
  have hxS : (↑x : R) ∈ S := x.isUnit
  cases i with
  | zero =>
    rw [norm_iteratedFDerivWithin_zero, Ring.inverse_unit]
    simp
  | succ m =>
    set Lambda : ℝ := ‖(↑x⁻¹ : R)‖ with hLambda
    rw [← norm_iteratedFDerivWithin_fderivWithin hSu hxS]
    have heq : fderivWithin 𝕜 Ring.inverse S =ᶠ[𝓝[S] (↑x)]
        (fun y => (-mulLeftRight 𝕜 R) (Ring.inverse y) (Ring.inverse y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [fderivWithin_of_isOpen hSopen hy]
      simp only [hSdef, Set.mem_setOf_eq] at hy
      obtain ⟨u, rfl⟩ := hy
      rw [fderiv_inverse, Ring.inverse_unit]
      ext v
      simp [ContinuousLinearMap.neg_apply, mulLeftRight_apply]
    rw [heq.iteratedFDerivWithin_eq (heq.self_of_nhdsWithin hxS) m]
    have hcd : ContDiffOn 𝕜 (⊤ : WithTop ℕ∞) Ring.inverse S :=
      contDiffOn_ringInverse ⊤
    have hsum : ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ)
          * ‖iteratedFDerivWithin 𝕜 k Ring.inverse S (↑x)‖
          * ‖iteratedFDerivWithin 𝕜 (m - k) Ring.inverse S (↑x)‖
        ≤ ((m + 1).factorial : ℝ) * Lambda ^ (m + 1 + 1) := by
      calc
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ)
              * ‖iteratedFDerivWithin 𝕜 k Ring.inverse S (↑x)‖
              * ‖iteratedFDerivWithin 𝕜 (m - k) Ring.inverse S (↑x)‖
            ≤ ∑ _k ∈ Finset.range (m + 1),
                (m.factorial : ℝ) * Lambda ^ (m + 2) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
              have h1 : (m.choose k : ℝ) * (k.factorial : ℝ) *
                    ((m - k).factorial : ℝ) = (m.factorial : ℝ) := by
                rw [← Nat.cast_mul, ← Nat.cast_mul,
                  Nat.choose_mul_factorial_mul_factorial hkm]
              calc
                (m.choose k : ℝ) *
                      ‖iteratedFDerivWithin 𝕜 k Ring.inverse S (↑x)‖ *
                      ‖iteratedFDerivWithin 𝕜 (m - k) Ring.inverse S (↑x)‖
                    ≤ (m.choose k : ℝ) * ((k.factorial : ℝ) * Lambda ^ (k + 1)) *
                        (((m - k).factorial : ℝ) * Lambda ^ (m - k + 1)) := by
                      refine mul_le_mul
                        (mul_le_mul_of_nonneg_left (IH k (by omega) x) (by positivity))
                        (IH (m - k) (by omega) x) (norm_nonneg _) (by positivity)
                _ = ((m.choose k : ℝ) * (k.factorial : ℝ) *
                      ((m - k).factorial : ℝ)) *
                      (Lambda ^ (k + 1) * Lambda ^ (m - k + 1)) := by ring
                _ = (m.factorial : ℝ) * Lambda ^ (m + 2) := by
                  rw [h1, ← pow_add,
                    show (k + 1) + (m - k + 1) = m + 2 from by omega]
        _ = ((m + 1).factorial : ℝ) * Lambda ^ (m + 1 + 1) := by
          rw [Finset.sum_const, Finset.card_range, Nat.factorial_succ]
          push_cast
          ring
    refine (ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear
      (-mulLeftRight 𝕜 R) hcd hcd hSu hxS le_top).trans ?_
    exact (mul_le_mul ((opNorm_neg _).trans_le (opNorm_mulLeftRight_le 𝕜 R)) hsum
      (Finset.sum_nonneg fun k _ => by positivity) zero_le_one).trans_eq (one_mul _)


theorem norm_iteratedFDeriv_ringInverse_le (i : ℕ) (x : Rˣ) :
    ‖iteratedFDeriv 𝕜 i Ring.inverse (x : R)‖ ≤
      (i.factorial : ℝ) * ‖(↑x⁻¹ : R)‖ ^ (i + 1) := by
  have h : iteratedFDerivWithin 𝕜 i Ring.inverse {y : R | IsUnit y} (↑x)
      = iteratedFDeriv 𝕜 i Ring.inverse (↑x) :=
    iteratedFDerivWithin_of_isOpen i Units.isOpen x.isUnit
  rw [← h]
  exact norm_iteratedFDerivWithin_ringInverse_le i x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem norm_iteratedFDeriv_invComp_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace E]
    (A : P → (E →L[ℝ] E)) (x : P) (m : ℕ) (Lambda D : ℝ)
    (hA : ContDiffAt ℝ (m : WithTop ℕ∞) A x)
    (hunit : ∀ᶠ p in nhds x, IsUnit (A p))
    (hLambda : ‖Ring.inverse (A x)‖ ≤ Lambda)
    (hD : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i A x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ m (fun p => Ring.inverse (A p)) x‖ ≤
      (m.factorial : ℝ) * ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) * D ^ m := by
  obtain ⟨u, hu_mem, hAu⟩ := hA.contDiffOn le_rfl (by simp)
  set s : Set P := interior u ∩ interior {p : P | IsUnit (A p)} with hs_def
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.2 hu_mem, mem_interior_iff_mem_nhds.2 hunit⟩
  have hAs : ContDiffOn ℝ (m : WithTop ℕ∞) A s :=
    hAu.mono (Set.inter_subset_left.trans interior_subset)
  have hmaps : Set.MapsTo A s {y : E →L[ℝ] E | IsUnit y} := fun p hp => by
    have h : p ∈ {q : P | IsUnit (A q)} := interior_subset hp.2
    simpa only [Set.mem_setOf_eq] using h
  obtain ⟨w, hw⟩ := hunit.self_of_nhds
  have hwinv : ‖((↑w⁻¹ : E →L[ℝ] E))‖ ≤ max Lambda 1 := by
    have h : Ring.inverse (A x) = (↑w⁻¹ : E →L[ℝ] E) := by
      rw [← hw, Ring.inverse_unit]
    rw [← h]
    exact hLambda.trans (le_max_left _ _)
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i Ring.inverse {y : E →L[ℝ] E | IsUnit y} (A x)‖
        ≤ (m.factorial : ℝ) * max Lambda 1 ^ (m + 1) := by
    intro i him
    have hN := norm_iteratedFDerivWithin_ringInverse_le (𝕜 := ℝ) i w
    rw [hw] at hN
    refine hN.trans ?_
    have h1 : (i.factorial : ℝ) ≤ (m.factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le him)
    have h2 : ‖((↑w⁻¹ : E →L[ℝ] E))‖ ^ (i + 1) ≤
        max Lambda 1 ^ (m + 1) := by
      calc
        ‖((↑w⁻¹ : E →L[ℝ] E))‖ ^ (i + 1)
            ≤ max Lambda 1 ^ (i + 1) := pow_le_pow_left₀ (norm_nonneg _) hwinv _
        _ ≤ max Lambda 1 ^ (m + 1) :=
          pow_le_pow_right₀ (le_max_right Lambda 1) (by omega)
    exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
  have hD' : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i A s x‖ ≤ D ^ i := by
    intro i hi him
    rw [iteratedFDerivWithin_of_isOpen i hs_open hxs]
    exact hD i hi him
  have hcomp : ‖iteratedFDerivWithin ℝ m (fun p => Ring.inverse (A p)) s x‖ ≤
      (m.factorial : ℝ) * ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) * D ^ m :=
    norm_iteratedFDerivWithin_comp_le
      (contDiffOn_ringInverse (𝕜 := ℝ) (m : WithTop ℕ∞)) hAs le_rfl
      Units.isOpen.uniqueDiffOn hs_open.uniqueDiffOn hmaps hxs hC hD'
  rwa [iteratedFDerivWithin_of_isOpen m hs_open hxs] at hcomp

end HCGCompactness
end DifferentialGeometry
