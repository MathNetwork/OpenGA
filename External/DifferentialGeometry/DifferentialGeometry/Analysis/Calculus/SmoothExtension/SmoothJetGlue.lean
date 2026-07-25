import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real






























noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace SmoothExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]












theorem contDiff_if_le_of_jet_match
    (fL fR : ℝ → F)
    (hL : ContDiffOn ℝ ∞ fL (Set.Iic (0:ℝ))) (hR : ContDiffOn ℝ ∞ fR (Set.Ici (0:ℝ)))
    (hjet : ∀ n : ℕ, iteratedDerivWithin n fL (Set.Iic 0) 0 = iteratedDerivWithin n fR (Set.Ici 0) 0) :
    ContDiff ℝ ∞ (fun t => if t ≤ 0 then fL t else fR t) := by

  set f : ℝ → F := fun t => if t ≤ 0 then fL t else fR t with hf_def
  set pL : ℝ → FormalMultilinearSeries ℝ ℝ F := ftaylorSeriesWithin ℝ fL (Set.Iic 0) with hpL_def
  set pR : ℝ → FormalMultilinearSeries ℝ ℝ F := ftaylorSeriesWithin ℝ fR (Set.Ici 0) with hpR_def
  set p : ℝ → FormalMultilinearSeries ℝ ℝ F :=
    fun t => if t ≤ 0 then pL t else pR t with hp_def

  have hTL : HasFTaylorSeriesUpToOn ∞ fL pL (Set.Iic (0:ℝ)) :=
    hL.ftaylorSeriesWithin (uniqueDiffOn_Iic 0)
  have hTR : HasFTaylorSeriesUpToOn ∞ fR pR (Set.Ici (0:ℝ)) :=
    hR.ftaylorSeriesWithin (uniqueDiffOn_Ici 0)


  have hjetF : ∀ n : ℕ, pL 0 n = pR 0 n := by
    intro n
    have heL := congrFun
      (iteratedFDerivWithin_eq_equiv_comp (𝕜 := ℝ) (n := n) (f := fL) (s := Set.Iic 0)) 0
    have heR := congrFun
      (iteratedFDerivWithin_eq_equiv_comp (𝕜 := ℝ) (n := n) (f := fR) (s := Set.Ici 0)) 0
    simp only [Function.comp_apply] at heL heR
    have hLR : iteratedFDerivWithin ℝ n fL (Set.Iic 0) 0
        = iteratedFDerivWithin ℝ n fR (Set.Ici 0) 0 := by
      rw [heL, heR, hjet n]
    simpa only [hpL_def, hpR_def, ftaylorSeriesWithin] using hLR

  have hEqL : ∀ m : ℕ, Set.EqOn (fun y => p y m) (fun y => pL y m) (Set.Iic (0:ℝ)) := by
    intro m y hy
    simp only [hp_def, if_pos (Set.mem_Iic.mp hy)]

  have hEqR : ∀ m : ℕ, Set.EqOn (fun y => p y m) (fun y => pR y m) (Set.Ici (0:ℝ)) := by
    intro m y hy
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with hy0 | hy0
    ·
      subst hy0
      simp only [hp_def, if_pos (le_refl (0:ℝ)), hjetF m]
    ·
      simp only [hp_def, if_neg (not_le.mpr hy0)]

  have hzero : ∀ x : ℝ, (p x 0).curry0 = f x := by
    intro x
    by_cases hx : x ≤ 0
    · have hval : (pL x 0).curry0 = fL x := hTL.zero_eq x (Set.mem_Iic.mpr hx)
      simp only [hp_def, hf_def, if_pos hx, hval]
    · have hx' : (0:ℝ) ≤ x := le_of_lt (not_le.mp hx)
      have hval : (pR x 0).curry0 = fR x := hTR.zero_eq x (Set.mem_Ici.mpr hx')
      simp only [hp_def, hf_def, if_neg hx, hval]


  have hm_lt : ∀ m : ℕ, (m : WithTop ℕ∞) < ∞ := fun m => by
    exact_mod_cast (Nat.cast_lt.mpr m.lt_succ_self).trans_le le_top
  have hderiv : ∀ m : ℕ, ∀ x : ℝ,
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft Set.univ x := by
    intro m x

    have hpL_succ : ∀ y : ℝ, y ≤ 0 → p y m.succ = pL y m.succ := by
      intro y hy; simp only [hp_def, if_pos hy]
    have hpR_succ : ∀ y : ℝ, (0:ℝ) ≤ y → p y m.succ = pR y m.succ := by
      intro y hy
      rcases eq_or_lt_of_le hy with hy0 | hy0
      · subst hy0; simp only [hp_def, if_pos (le_refl (0:ℝ)), hjetF]
      · simp only [hp_def, if_neg (not_le.mpr hy0)]
    rcases lt_trichotomy x 0 with hx | hx | hx
    ·
      have hxle : x ≤ 0 := le_of_lt hx
      have hdL : HasFDerivWithinAt (fun y => pL y m) (pL x m.succ).curryLeft (Set.Iic 0) x :=
        hTL.fderivWithin m (hm_lt m) x (Set.mem_Iic.mpr hxle)

      have hnhds : Set.Iio (0:ℝ) ∈ 𝓝 x := Iio_mem_nhds hx
      have hdL' : HasFDerivAt (fun y => pL y m) (pL x m.succ).curryLeft x :=
        (hdL.mono Iio_subset_Iic_self).hasFDerivAt hnhds

      have hee : (fun y => p y m) =ᶠ[𝓝 x] (fun y => pL y m) :=
        eventuallyEq_of_mem hnhds (fun y hy => hEqL m (Set.mem_Iic.mpr (le_of_lt hy)))
      have hfd : HasFDerivAt (fun y => p y m) (pL x m.succ).curryLeft x :=
        hdL'.congr_of_eventuallyEq hee
      rw [hpL_succ x hxle]
      exact hfd.hasFDerivWithinAt
    ·
      subst hx

      have hdL0 : HasFDerivWithinAt (fun y => pL y m) (pL 0 m.succ).curryLeft (Set.Iic 0) 0 :=
        hTL.fderivWithin m (hm_lt m) 0 Set.self_mem_Iic
      have hdL0' : HasFDerivWithinAt (fun y => p y m) (pL 0 m.succ).curryLeft (Set.Iic 0) 0 :=
        hdL0.congr (hEqL m) (hEqL m Set.self_mem_Iic)

      have hdR0 : HasFDerivWithinAt (fun y => pR y m) (pR 0 m.succ).curryLeft (Set.Ici 0) 0 :=
        hTR.fderivWithin m (hm_lt m) 0 Set.self_mem_Ici
      have hdR0' : HasFDerivWithinAt (fun y => p y m) (pL 0 m.succ).curryLeft (Set.Ici 0) 0 := by
        have hval : (pR 0 m.succ).curryLeft = (pL 0 m.succ).curryLeft := by rw [hjetF]
        rw [← hval]
        exact hdR0.congr (hEqR m) (hEqR m Set.self_mem_Ici)

      have hunion : HasFDerivWithinAt (fun y => p y m) (pL 0 m.succ).curryLeft
          (Set.Iic 0 ∪ Set.Ici 0) 0 := hdL0'.union hdR0'
      rw [Set.Iic_union_Ici] at hunion
      rw [hpL_succ 0 (le_refl 0)]
      exact hunion
    ·
      have hxge : (0:ℝ) ≤ x := le_of_lt hx
      have hdR : HasFDerivWithinAt (fun y => pR y m) (pR x m.succ).curryLeft (Set.Ici 0) x :=
        hTR.fderivWithin m (hm_lt m) x (Set.mem_Ici.mpr hxge)
      have hnhds : Set.Ioi (0:ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx
      have hdR' : HasFDerivAt (fun y => pR y m) (pR x m.succ).curryLeft x :=
        (hdR.mono Ioi_subset_Ici_self).hasFDerivAt hnhds
      have hee : (fun y => p y m) =ᶠ[𝓝 x] (fun y => pR y m) :=
        eventuallyEq_of_mem hnhds (fun y hy => hEqR m (Set.mem_Ici.mpr (le_of_lt hy)))
      have hfd : HasFDerivAt (fun y => p y m) (pR x m.succ).curryLeft x :=
        hdR'.congr_of_eventuallyEq hee
      rw [hpR_succ x hxge]
      exact hfd.hasFDerivWithinAt

  have hTaylor : HasFTaylorSeriesUpToOn ∞ f p Set.univ :=
    (hasFTaylorSeriesUpToOn_top_iff' (le_refl _)).mpr
      ⟨fun x _ => hzero x, fun m x _ => hderiv m x⟩

  rw [← contDiffOn_univ]
  exact hTaylor.contDiffOn

end SmoothExtension
end Analysis
end DifferentialGeometry

end
