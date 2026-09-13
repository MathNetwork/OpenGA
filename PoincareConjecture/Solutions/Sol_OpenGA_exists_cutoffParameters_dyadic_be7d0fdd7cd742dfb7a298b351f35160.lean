import Definitions.Def_OpenGA_CutoffSurgeryProcess
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false

open Set
open OpenGA

/-- The dyadic block index of a time `t`: the least `j` with `t < 2 ^ (j + 1) * eps`. -/
private noncomputable def blockIndex (eps : ℝ) (t : ℝ) : ℕ :=
  sInf {j : ℕ | t < 2 ^ (j + 1) * eps}

private lemma blockIndex_spec (eps : ℝ) (heps : 0 < eps) (t : ℝ) :
    t < 2 ^ (blockIndex eps t + 1) * eps := by
  have hne : {j : ℕ | t < 2 ^ (j + 1) * eps}.Nonempty := by
    obtain ⟨j, hj⟩ : ∃ j : ℕ, t / eps < 2 ^ j := pow_unbounded_of_one_lt _ one_lt_two
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ heps] at hj
    calc t < 2 ^ j * eps := hj
      _ ≤ 2 ^ (j + 1) * eps := by
          have : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := by
            apply pow_le_pow_right₀ one_le_two
            omega
          nlinarith
  exact Nat.sInf_mem hne

private lemma blockIndex_mono (eps : ℝ) (heps : 0 < eps) {t t' : ℝ} (h : t ≤ t') :
    blockIndex eps t ≤ blockIndex eps t' :=
  Nat.sInf_le (lt_of_le_of_lt h (blockIndex_spec eps heps t'))

private lemma blockIndex_eq (eps : ℝ) (heps : 0 < eps) (j : ℕ) (t : ℝ)
    (h1 : 2 ^ j * eps ≤ t) (h2 : t < 2 ^ (j + 1) * eps) : blockIndex eps t = j := by
  refine le_antisymm (Nat.sInf_le h2) ?_
  by_contra hcon
  have hlt : blockIndex eps t < j := Nat.lt_of_not_le hcon
  have hmem : t < 2 ^ (blockIndex eps t + 1) * eps := blockIndex_spec eps heps t
  have : (2 : ℝ) ^ (blockIndex eps t + 1) ≤ 2 ^ j := by
    apply pow_le_pow_right₀ one_le_two
    omega
  nlinarith

theorem solution (eps : ℝ) (heps : 0 < eps) (rs ds : ℕ → ℝ)
    (hr : ∀ j : ℕ, 0 < rs j) (hd : ∀ j : ℕ, 0 < ds j)
    (hra : Antitone rs) (hda : Antitone ds) :
    ∃ p : CutoffParameters,
      (∀ t : ℝ, 0 ≤ t → t < eps → p.r t = rs 0 ∧ p.delta t = ds 0) ∧
      (∀ (j : ℕ) (t : ℝ), 2 ^ j * eps ≤ t → t < 2 ^ (j + 1) * eps →
        p.r t = rs j ∧ p.delta t = ds j) := by
  refine ⟨{ r := fun t => rs (blockIndex eps t)
            delta := fun t => ds (blockIndex eps t)
            r_pos := fun t _ => hr _
            delta_pos := fun t _ => hd _
            r_antitoneOn := fun t _ t' _ h => hra (blockIndex_mono eps heps h)
            delta_antitoneOn := fun t _ t' _ h => hda (blockIndex_mono eps heps h) }, ?_, ?_⟩
  · intro t _ ht
    have hmem : t < 2 ^ (0 + 1) * eps := by
      norm_num
      linarith
    have : blockIndex eps t = 0 := le_antisymm (Nat.sInf_le hmem) (Nat.zero_le _)
    simp [this]
  · intro j t h1 h2
    simp [blockIndex_eq eps heps j t h1 h2]
