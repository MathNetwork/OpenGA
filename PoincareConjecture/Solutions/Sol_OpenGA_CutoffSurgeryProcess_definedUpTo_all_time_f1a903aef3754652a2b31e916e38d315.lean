import Definitions.Def_OpenGA_CutoffSurgeryProcess
import Theorems.Thm_OpenGA_RadialSurgeryVolumeBudget_events_finite

set_option autoImplicit false

open Set
open OpenGA

theorem solution (P : CutoffSurgeryProcess) (T : ℝ) (hT : 0 ≤ T) : P.DefinedUpTo T := by
  by_contra hbad
  set B : Set ℝ := {t : ℝ | 0 ≤ t ∧ ¬ P.DefinedUpTo t} with hBdef
  have hne : B.Nonempty := ⟨T, hT, hbad⟩
  have hbdd : BddBelow B := ⟨0, fun x hx => hx.1⟩
  have hs0 : 0 ≤ sInf B := le_csInf hne (fun x hx => hx.1)
  have hgood : ∀ S : ℝ, 0 ≤ S → S < sInf B → P.DefinedUpTo S := by
    intro S hS hSs
    by_contra h
    exact absurd (csInf_le hbdd (show S ∈ B from ⟨hS, h⟩)) (not_le.mpr hSs)
  have hsurg : (P.surgeryTimes ∩ Iic (sInf B)).Finite := by
    have h := P.budget.events_finite
    rw [P.budget_events] at h
    exact h.inter_of_left _
  have hdef : P.DefinedUpTo (sInf B) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; exact P.definedUpTo_zero
    · exact P.extend_limit (sInf B) h hgood hsurg
  obtain ⟨T', hlt, hT'⟩ := P.extend_forward (sInf B) hs0 hdef
  obtain ⟨b, hbB, hbT'⟩ := exists_lt_of_csInf_lt hne hlt
  exact hbB.2 (P.definedUpTo_mono hbB.1 hbT'.le hT')
