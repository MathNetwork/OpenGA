import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef



















namespace DifferentialGeometry.HCGCompactness

open scoped BigOperators
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]



private lemma isHermitian_entry
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k : n,
        (hA.eigenvectorUnitary : Matrix n n ℝ) i k *
          hA.eigenvalues k *
          (hA.eigenvectorUnitary : Matrix n n ℝ) j k := by
  classical
  have hspec : A = ((hA.eigenvectorUnitary : Matrix n n ℝ) *
      (Matrix.diagonal hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ)) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hcomp : (RCLike.ofReal (K := ℝ)) ∘ hA.eigenvalues = hA.eigenvalues := by
      funext k; simp
    rw [hcomp] at h
    exact h
  have h := congr_fun (congr_fun hspec i) j
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq]
    have hstar : (star (hA.eigenvectorUnitary : Matrix n n ℝ)) k j =
        (hA.eigenvectorUnitary : Matrix n n ℝ) j k := by
      change star ((hA.eigenvectorUnitary : Matrix n n ℝ) j k) = _
      exact star_trivial _
    rw [hstar]
  · intro ℓ _ hℓ
    rw [Matrix.diagonal_apply_ne _ hℓ]
    ring
  · intro hk
    exact absurd (Finset.mem_univ k) hk

omit [DecidableEq n] in


theorem sum_posSemidef_mul_posSemidef_nonneg
    {M G : Matrix n n ℝ} (hM : M.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, M i j * G i j := by
  classical
  set U : Matrix n n ℝ := (hM.isHermitian.eigenvectorUnitary : Matrix n n ℝ) with hU
  have hexp : ∀ i j : n, M i j * G i j =
      ∑ k, hM.isHermitian.eigenvalues k * (U i k * U j k * G i j) := by
    intro i j
    rw [isHermitian_entry hM.isHermitian i j, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by rw [hU]; ring)
  have hreorder : ∑ i, ∑ j, M i j * G i j =
      ∑ k, hM.isHermitian.eigenvalues k * (∑ i, ∑ j, U i k * U j k * G i j) := by
    have h1 : ∑ i, ∑ j, M i j * G i j =
        ∑ i, ∑ j, ∑ k,
          hM.isHermitian.eigenvalues k * (U i k * U j k * G i j) :=
      Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => hexp i j))
    rw [h1]
    rw [show (∑ i, ∑ j, ∑ k,
          hM.isHermitian.eigenvalues k * (U i k * U j k * G i j))
        = ∑ i, ∑ k, ∑ j,
          hM.isHermitian.eigenvalues k * (U i k * U j k * G i j)
      from Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hreorder]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (Matrix.PosSemidef.eigenvalues_nonneg hM k)
  have hquad : ∑ i, ∑ j, U i k * U j k * G i j
      = (fun i => U i k) ⬝ᵥ (G *ᵥ fun i => U i k) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [hquad]
  exact hG.dotProduct_mulVec_nonneg _



section KroneckerPow

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [DecidableEq Idx] in

private lemma sum_fin_succ_fun {R : Type*} [AddCommMonoid R] (s : ℕ)
    (f : (Fin (s + 1) → Idx) → R) :
    (∑ I : Fin (s + 1) → Idx, f I)
      = ∑ k : Idx, ∑ I : Fin s → Idx, f (Fin.cons k I) := by
  classical
  calc (∑ I : Fin (s + 1) → Idx, f I)
      = ∑ p : Idx × (Fin s → Idx),
          f ((Fin.consEquiv (fun _ : Fin (s + 1) => Idx)) p) :=
        ((Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).sum_comp f).symm
    _ = ∑ k : Idx, ∑ I : Fin s → Idx, f (Fin.cons k I) := by
        rw [Fintype.sum_prod_type]
        rfl

omit [DecidableEq Idx] in

private lemma sum_fin_succ_fun₂ {R : Type*} [AddCommMonoid R] (s : ℕ)
    (f : (Fin (s + 1) → Idx) → (Fin (s + 1) → Idx) → R) :
    (∑ I : Fin (s + 1) → Idx, ∑ J : Fin (s + 1) → Idx, f I J)
      = ∑ k : Idx, ∑ I : Fin s → Idx, ∑ l : Idx, ∑ J : Fin s → Idx,
          f (Fin.cons k I) (Fin.cons l J) := by
  rw [sum_fin_succ_fun (s := s) (f := fun I => ∑ J, f I J)]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun I _ =>
    sum_fin_succ_fun (s := s) (f := fun J => f (Fin.cons k I) J)

omit [Fintype Idx] [DecidableEq Idx] in

private lemma prod_fin_succ_Q (s : ℕ) (Q : Idx → Idx → ℝ)
    (k l : Idx) (I J : Fin s → Idx) :
    (∏ a : Fin (s + 1),
        Q ((Fin.cons k I : Fin (s + 1) → Idx) a)
          ((Fin.cons l J : Fin (s + 1) → Idx) a))
      = Q k l * ∏ a : Fin s, Q (I a) (J a) := by
  rw [Fin.prod_univ_succ]
  simp


private lemma diag_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (G : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, (α * (if i = j then (1 : ℝ) else 0)) * G i j)
      = α * ∑ i : ι, G i i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h


private lemma matrix_posSemidef_of_quad_nonneg {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hquad : ∀ x : ι → ℝ, 0 ≤ ∑ i : ι, ∑ j : ι, A i j * (x i * x j)) :
    (Matrix.of A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simpa using hsymm j i
  · intro x
    have hstar : star x = x := funext fun i => star_trivial _
    have hexp : x ⬝ᵥ (Matrix.of A *ᵥ x) = ∑ i : ι, ∑ j : ι, A i j * (x i * x j) := by
      simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [hstar, hexp]
    exact hquad x


private lemma shifted_posSemidef
    (Q : Idx → Idx → ℝ) (α : ℝ)
    (hQsymm : ∀ i j, Q i j = Q j i)
    (hQlb : ∀ w : Idx → ℝ, α * ∑ i, w i ^ 2 ≤ ∑ i, ∑ j, Q i j * (w i * w j)) :
    (Matrix.of fun i j : Idx =>
      Q i j - α * (if i = j then (1 : ℝ) else 0)).PosSemidef := by
  refine matrix_posSemidef_of_quad_nonneg _ ?_ ?_
  · intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij, hQsymm i j]
  · intro x
    have hsplit : (∑ i : Idx, ∑ j : Idx,
          (Q i j - α * (if i = j then (1 : ℝ) else 0)) * (x i * x j))
        = (∑ i : Idx, ∑ j : Idx, Q i j * (x i * x j)) - α * ∑ i : Idx, x i ^ 2 := by
      calc (∑ i : Idx, ∑ j : Idx,
            (Q i j - α * (if i = j then (1 : ℝ) else 0)) * (x i * x j))
          = ∑ i : Idx, ∑ j : Idx,
              (Q i j * (x i * x j)
                - (α * (if i = j then (1 : ℝ) else 0)) * (x i * x j)) :=
            Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ i : Idx, ∑ j : Idx, Q i j * (x i * x j))
              - ∑ i : Idx, ∑ j : Idx,
                  (α * (if i = j then (1 : ℝ) else 0)) * (x i * x j) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_sub_distrib]
        _ = (∑ i : Idx, ∑ j : Idx, Q i j * (x i * x j)) - α * ∑ i : Idx, x i * x i := by
            rw [diag_pairing α (fun i j => x i * x j)]
        _ = (∑ i : Idx, ∑ j : Idx, Q i j * (x i * x j)) - α * ∑ i : Idx, x i ^ 2 := by
            have h : (∑ i : Idx, x i * x i) = ∑ i : Idx, x i ^ 2 :=
              Finset.sum_congr rfl fun i _ => (pow_two (x i)).symm
            rw [h]
    rw [hsplit]
    exact sub_nonneg.mpr (hQlb x)

omit [DecidableEq Idx] in

private lemma kron_kernel_posSemidef_of_ih (s : ℕ) (Q : Idx → Idx → ℝ) (α : ℝ)
    (hαnonneg : 0 ≤ α)
    (hQsymm : ∀ i j, Q i j = Q j i)
    (ih : ∀ w : (Fin s → Idx) → ℝ,
      α ^ s * ∑ I : Fin s → Idx, w I ^ 2 ≤
        ∑ I : Fin s → Idx, ∑ J : Fin s → Idx,
          (∏ a : Fin s, Q (I a) (J a)) * (w I * w J)) :
    (Matrix.of fun I J : Fin s → Idx =>
      ∏ a : Fin s, Q (I a) (J a)).PosSemidef := by
  refine matrix_posSemidef_of_quad_nonneg _ ?_ ?_
  · intro I J
    exact Finset.prod_congr rfl fun a _ => hQsymm (I a) (J a)
  · intro w
    exact le_trans
      (mul_nonneg (pow_nonneg hαnonneg s)
        (Finset.sum_nonneg fun I _ => sq_nonneg (w I)))
      (ih w)


private lemma sandwich_entry {ι κ : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (V : Matrix ι κ ℝ) (k l : κ) :
    (Vᴴ * P * V) k l = ∑ I : ι, ∑ J : ι, P I J * (V I k * V J l) := by
  rw [Matrix.mul_apply]
  calc (∑ J : ι, (Vᴴ * P) k J * V J l)
      = ∑ J : ι, (∑ I : ι, V I k * P I J) * V J l := by
        refine Finset.sum_congr rfl fun J _ => ?_
        congr 1
    _ = ∑ J : ι, ∑ I : ι, P I J * (V I k * V J l) := by
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun I _ => by ring
    _ = ∑ I : ι, ∑ J : ι, P I J * (V I k * V J l) := Finset.sum_comm

omit [DecidableEq Idx] in






theorem quadForm_id_le_pow
    (Q : Idx → Idx → ℝ) (C : ℝ) (hC : 0 < C)
    (hQsymm : ∀ i j, Q i j = Q j i)
    (hQlb : ∀ w : Idx → ℝ, (1 / C) * ∑ i, w i ^ 2 ≤
      ∑ i, ∑ j, Q i j * (w i * w j)) :
    ∀ (s : ℕ) (c : (Fin s → Idx) → ℝ),
      (1 / C) ^ s * ∑ I0 : Fin s → Idx, c I0 ^ 2 ≤
        ∑ I0 : Fin s → Idx, ∑ J0 : Fin s → Idx,
          (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0) := by
  classical
  have hαnonneg : (0 : ℝ) ≤ 1 / C := le_of_lt (one_div_pos.mpr hC)
  intro s
  induction s with
  | zero =>
      intro c
      simp [pow_two]
  | succ s ih =>
      intro c
      set W : Matrix (Fin s → Idx) Idx ℝ :=
        Matrix.of fun I k => c (Fin.cons k I) with hW
      set P : Matrix (Fin s → Idx) (Fin s → Idx) ℝ :=
        Matrix.of fun I J => ∏ a : Fin s, Q (I a) (J a) with hP
      set S : Matrix Idx Idx ℝ := Wᴴ * P * W with hS
      have hMpsd := shifted_posSemidef Q (1 / C) hQsymm hQlb
      have hPpsd : P.PosSemidef := by
        rw [hP]
        exact kron_kernel_posSemidef_of_ih s Q (1 / C) hαnonneg hQsymm ih
      have hSpsd : S.PosSemidef := by
        rw [hS]
        exact hPpsd.conjTranspose_mul_mul_same W
      have hSentry : ∀ k l : Idx, S k l
          = ∑ I : Fin s → Idx, ∑ J : Fin s → Idx,
              (∏ a : Fin s, Q (I a) (J a))
                * (c (Fin.cons k I) * c (Fin.cons l J)) := by
        intro k l
        rw [hS, sandwich_entry]
        refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
        rw [hP, hW]
        simp only [Matrix.of_apply]

      have hexpand : (∑ i : Idx, ∑ j : Idx,
            (Matrix.of fun i j : Idx =>
              Q i j - 1 / C * (if i = j then (1 : ℝ) else 0)) i j * S i j)
          = (∑ k : Idx, ∑ l : Idx, Q k l * S k l) - 1 / C * ∑ k : Idx, S k k := by
        calc (∑ i : Idx, ∑ j : Idx,
              (Matrix.of fun i j : Idx =>
                Q i j - 1 / C * (if i = j then (1 : ℝ) else 0)) i j * S i j)
            = ∑ i : Idx, ∑ j : Idx,
                (Q i j * S i j
                  - (1 / C * (if i = j then (1 : ℝ) else 0)) * S i j) := by
              refine Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun j _ => ?_
              rw [Matrix.of_apply]
              ring
          _ = (∑ i : Idx, ∑ j : Idx, Q i j * S i j)
                - ∑ i : Idx, ∑ j : Idx,
                    (1 / C * (if i = j then (1 : ℝ) else 0)) * S i j := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_sub_distrib]
          _ = (∑ k : Idx, ∑ l : Idx, Q k l * S k l) - 1 / C * ∑ k : Idx, S k k := by
              rw [diag_pairing (1 / C) (fun i j => S i j)]
      have hdiag_le : 1 / C * ∑ k : Idx, S k k
          ≤ ∑ k : Idx, ∑ l : Idx, Q k l * S k l := by
        have h0 := sum_posSemidef_mul_posSemidef_nonneg hMpsd hSpsd
        rw [hexpand] at h0
        linarith

      have hdiagIH : ∀ k : Idx,
          (1 / C) ^ s * ∑ I : Fin s → Idx, c (Fin.cons k I) ^ 2 ≤ S k k := by
        intro k
        rw [hSentry k k]
        exact ih (fun I => c (Fin.cons k I))
      have hsum_ih : (1 / C) ^ s
            * (∑ k : Idx, ∑ I : Fin s → Idx, c (Fin.cons k I) ^ 2)
          ≤ ∑ k : Idx, S k k := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => hdiagIH k
      have hNorm : (∑ I0 : Fin (s + 1) → Idx, c I0 ^ 2)
          = ∑ k : Idx, ∑ I : Fin s → Idx, c (Fin.cons k I) ^ 2 :=
        sum_fin_succ_fun s (fun I0 => c I0 ^ 2)
      have hRHS : (∑ I0 : Fin (s + 1) → Idx, ∑ J0 : Fin (s + 1) → Idx,
            (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0))
          = ∑ k : Idx, ∑ l : Idx, Q k l * S k l := by
        rw [sum_fin_succ_fun₂ s
          (f := fun I0 J0 => (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0))]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hSentry k l, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [prod_fin_succ_Q s Q k l I J]
        ring
      calc (1 / C) ^ (s + 1) * ∑ I0 : Fin (s + 1) → Idx, c I0 ^ 2
          = (1 / C) * ((1 / C) ^ s
              * ∑ k : Idx, ∑ I : Fin s → Idx, c (Fin.cons k I) ^ 2) := by
            rw [hNorm, pow_succ]
            ring
        _ ≤ (1 / C) * ∑ k : Idx, S k k :=
            mul_le_mul_of_nonneg_left hsum_ih hαnonneg
        _ ≤ ∑ k : Idx, ∑ l : Idx, Q k l * S k l := hdiag_le
        _ = ∑ I0 : Fin (s + 1) → Idx, ∑ J0 : Fin (s + 1) → Idx,
              (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0) := hRHS.symm







theorem quad_lb_of_near_id {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ι → ι → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hnear : ∀ i j, |Q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 2) :
    ∀ w : ι → ℝ, (1 / 2) * ∑ i, w i ^ 2 ≤ ∑ i, ∑ j, Q i j * (w i * w j) := by
  intro w
  have hsq_nonneg : (0 : ℝ) ≤ ∑ i, w i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (w i)

  have hsplit : (∑ i, ∑ j, Q i j * (w i * w j))
      = (∑ i, w i ^ 2)
        + ∑ i, ∑ j, (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j) := by
    have hid : (∑ i, ∑ j,
          ((1 : ℝ) * (if i = j then (1 : ℝ) else 0)) * (w i * w j))
        = (1 : ℝ) * ∑ i, w i * w i :=
      diag_pairing 1 (fun i j => w i * w j)
    calc (∑ i, ∑ j, Q i j * (w i * w j))
        = ∑ i, ∑ j,
            (((1 : ℝ) * (if i = j then (1 : ℝ) else 0)) * (w i * w j)
              + (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ i, ∑ j, ((1 : ℝ) * (if i = j then (1 : ℝ) else 0)) * (w i * w j))
            + ∑ i, ∑ j, (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_add_distrib]
      _ = (∑ i, w i ^ 2)
            + ∑ i, ∑ j, (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j) := by
          rw [hid, one_mul]
          congr 1
          exact Finset.sum_congr rfl fun i _ => (pow_two (w i)).symm

  have herr : |∑ i, ∑ j, (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j)|
      ≤ ε * ((∑ i, |w i|) * (∑ j, |w j|)) := by
    calc |∑ i, ∑ j, (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j)|
        ≤ ∑ i, |∑ j, (Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(Q i j - (if i = j then (1 : ℝ) else 0)) * (w i * w j)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ε * (|w i| * |w j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul (hnear i j) le_rfl
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hε0
      _ = ε * ((∑ i, |w i|) * (∑ j, |w j|)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]

  have hCS : ((∑ i, |w i|) * (∑ j, |w j|)) ≤ (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => |w i|)
    calc (∑ i, |w i|) * (∑ j, |w j|)
        = (∑ i, |w i|) ^ 2 := (pow_two _).symm
      _ ≤ (Finset.univ : Finset ι).card * ∑ i, |w i| ^ 2 := by simpa using h
      _ = (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
          rw [Finset.card_univ]
          congr 1
          exact Finset.sum_congr rfl fun i _ => sq_abs (w i)

  have hEbound : ε * ((∑ i, |w i|) * (∑ j, |w j|))
      ≤ (1 / 2) * ∑ i, w i ^ 2 := by
    calc ε * ((∑ i, |w i|) * (∑ j, |w j|))
        ≤ ε * ((Fintype.card ι : ℝ) * ∑ i, w i ^ 2) :=
          mul_le_mul_of_nonneg_left hCS hε0
      _ = ((Fintype.card ι : ℝ) * ε) * ∑ i, w i ^ 2 := by ring
      _ ≤ (1 / 2) * ∑ i, w i ^ 2 :=
          mul_le_mul_of_nonneg_right hsmall hsq_nonneg
  have hElb := (abs_le.mp herr).1
  rw [hsplit]
  linarith





theorem quad_ub_of_near_id {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ι → ι → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hnear : ∀ i j, |Q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε)
    (s : ℕ) (c : (Fin s → ι) → ℝ) :
    (∑ I0 : Fin s → ι, ∑ J0 : Fin s → ι,
        (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0)) ≤
      ((1 + ε) * (Fintype.card ι : ℝ)) ^ s * ∑ I0 : Fin s → ι, c I0 ^ 2 := by
  classical
  have hQabs : ∀ i j, |Q i j| ≤ 1 + ε := by
    intro i j
    have h := hnear i j
    have habs : |if i = j then (1 : ℝ) else 0| ≤ 1 := by
      by_cases hij : i = j <;> simp [hij]
    calc |Q i j|
        = |(Q i j - (if i = j then (1 : ℝ) else 0)) + (if i = j then (1 : ℝ) else 0)| := by
          congr 1
          ring
      _ ≤ |Q i j - (if i = j then (1 : ℝ) else 0)| + |if i = j then (1 : ℝ) else 0| :=
          abs_add_le _ _
      _ ≤ ε + 1 := add_le_add h habs
      _ = 1 + ε := by ring
  have hprod : ∀ I0 J0 : Fin s → ι, |∏ a, Q (I0 a) (J0 a)| ≤ (1 + ε) ^ s := by
    intro I0 J0
    rw [Finset.abs_prod]
    calc (∏ a, |Q (I0 a) (J0 a)|)
        ≤ ∏ _a : Fin s, (1 + ε) :=
          Finset.prod_le_prod (fun a _ => abs_nonneg _) (fun a _ => hQabs _ _)
      _ = (1 + ε) ^ s := by simp
  calc (∑ I0 : Fin s → ι, ∑ J0 : Fin s → ι,
        (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0))
      ≤ ∑ I0 : Fin s → ι, ∑ J0 : Fin s → ι,
          (1 + ε) ^ s * (|c I0| * |c J0|) := by
        refine Finset.sum_le_sum fun I0 _ => Finset.sum_le_sum fun J0 _ => ?_
        calc (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0)
            ≤ |(∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0)| := le_abs_self _
          _ = |∏ a, Q (I0 a) (J0 a)| * (|c I0| * |c J0|) := by
              rw [abs_mul, abs_mul]
          _ ≤ (1 + ε) ^ s * (|c I0| * |c J0|) :=
              mul_le_mul_of_nonneg_right (hprod I0 J0)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (1 + ε) ^ s * ((∑ I0 : Fin s → ι, |c I0|) * (∑ J0 : Fin s → ι, |c J0|)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I0 _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (1 + ε) ^ s * ((Fintype.card (Fin s → ι) : ℝ) * ∑ I0 : Fin s → ι, c I0 ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (∑ I0 : Fin s → ι, |c I0|) * (∑ J0 : Fin s → ι, |c J0|)
            = (∑ I0 : Fin s → ι, |c I0|) ^ 2 := (pow_two _).symm
          _ ≤ (Finset.univ : Finset (Fin s → ι)).card * ∑ I0 : Fin s → ι, |c I0| ^ 2 := by
              simpa using sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (Fin s → ι))) (f := fun I0 => |c I0|)
          _ = (Fintype.card (Fin s → ι) : ℝ) * ∑ I0 : Fin s → ι, c I0 ^ 2 := by
              rw [Finset.card_univ]
              congr 1
              exact Finset.sum_congr rfl fun I0 _ => sq_abs (c I0)
    _ = ((1 + ε) * (Fintype.card ι : ℝ)) ^ s * ∑ I0 : Fin s → ι, c I0 ^ 2 := by
        have hcard : (Fintype.card (Fin s → ι) : ℝ) = ((Fintype.card ι : ℝ)) ^ s := by
          rw [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hcard, mul_pow]
        ring

end KroneckerPow

end DifferentialGeometry.HCGCompactness
