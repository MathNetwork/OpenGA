import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter Topology Nat

namespace DifferentialGeometry
namespace Analysis

private lemma inter_Iic_eventuallyEq {s : Set ℝ} {a y : ℝ} (h : y < a) :
    (s ∩ Set.Iic a : Set ℝ) =ᶠ[𝓝 y] s := by
  rw [eventuallyEq_set]
  filter_upwards [Iio_mem_nhds h] with z hz
  simp only [Set.mem_Iio] at hz
  simp only [Set.mem_inter_iff, Set.mem_Iic]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, le_of_lt hz⟩⟩

private lemma inter_Ici_eventuallyEq {s : Set ℝ} {a y : ℝ} (h : a < y) :
    (s ∩ Set.Ici a : Set ℝ) =ᶠ[𝓝 y] s := by
  rw [eventuallyEq_set]
  filter_upwards [Ioi_mem_nhds h] with z hz
  simp only [Set.mem_Ioi] at hz
  simp only [Set.mem_inter_iff, Set.mem_Ici]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, le_of_lt hz⟩⟩

private lemma iteratedDerivWithin_congr_set {f : ℝ → ℝ} {s t : Set ℝ} {x : ℝ} (n : ℕ)
    (h : s =ᶠ[𝓝 x] t) : iteratedDerivWithin n f s x = iteratedDerivWithin n f t x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
  congr 1
  exact iteratedFDerivWithin_congr_set h n

private lemma iteratedDeriv_taylorWithinEval_eq (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (c : ℝ)
    {j : ℕ} (hj : j ≤ n) :
    iteratedDeriv j (fun x => taylorWithinEval f n s c x) c = iteratedDerivWithin j f s c := by
  have hgen : ∀ i : ℕ,
      iteratedDeriv j (fun x : ℝ => (x - c) ^ i) c = if j = i then (i ! : ℝ) else 0 := by
    intro i
    have h := congrFun (iteratedDeriv_comp_sub_const j (fun w : ℝ => w ^ i) c) c
    simp only [sub_self, iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero] at h
    exact h
  have hpoly : (fun x => taylorWithinEval f n s c x)
      = fun x => ∑ i ∈ Finset.range (n + 1),
          ((i ! : ℝ)⁻¹ * iteratedDerivWithin i f s c) * (x - c) ^ i := by
    funext x
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_mul]; ring
  rw [hpoly, iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  have hsummand : ∀ i ∈ Finset.range (n + 1),
      iteratedDeriv j (fun x : ℝ => ((i ! : ℝ)⁻¹ * iteratedDerivWithin i f s c) * (x - c) ^ i) c
        = ((i ! : ℝ)⁻¹ * iteratedDerivWithin i f s c) * (if j = i then (i ! : ℝ) else 0) := by
    intro i _
    rw [iteratedDeriv_const_mul _ (by fun_prop), hgen i]
  rw [Finset.sum_congr rfl hsummand, Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
  · have hfac : (j ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    rw [if_pos rfl, mul_right_comm, inv_mul_cancel₀ hfac, one_mul]
  · intro i _ hij
    rw [if_neg (Ne.symm hij), mul_zero]

private theorem contDiffOn_glue {a : ℝ} {s : Set ℝ} (ha : a ∈ s) (hs : UniqueDiffOn ℝ s)
    (hsL : UniqueDiffOn ℝ (s ∩ Set.Iic a)) (hsR : UniqueDiffOn ℝ (s ∩ Set.Ici a)) :
    ∀ (k : ℕ) (F : ℝ → ℝ),
      ContDiffOn ℝ (k : ℕ) F (s ∩ Set.Iic a) →
      ContDiffOn ℝ (k : ℕ) F (s ∩ Set.Ici a) →
      (∀ j, j ≤ k → iteratedDerivWithin j F (s ∩ Set.Iic a) a
                  = iteratedDerivWithin j F (s ∩ Set.Ici a) a) →
      ContDiffOn ℝ (k : ℕ) F s := by
  have hunion : (s ∩ Set.Iic a) ∪ (s ∩ Set.Ici a) = s := by
    rw [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]
  intro k
  induction k with
  | zero =>
    intro F h₁ h₂ _
    rw [Nat.cast_zero, contDiffOn_zero] at h₁ h₂ ⊢
    intro x hx
    rcases lt_trichotomy x a with hxa | hxa | hxa
    · have hmem : x ∈ s ∩ Set.Iic a := ⟨hx, le_of_lt hxa⟩
      exact (continuousWithinAt_congr_set (inter_Iic_eventuallyEq hxa)).mp (h₁ x hmem)
    · have h1a : ContinuousWithinAt F (s ∩ Set.Iic a) x := h₁ x ⟨hx, hxa.le⟩
      have h2a : ContinuousWithinAt F (s ∩ Set.Ici a) x := h₂ x ⟨hx, hxa.ge⟩
      have hu := h1a.union h2a
      rwa [hunion] at hu
    · have hmem : x ∈ s ∩ Set.Ici a := ⟨hx, le_of_lt hxa⟩
      exact (continuousWithinAt_congr_set (inter_Ici_eventuallyEq hxa)).mp (h₂ x hmem)
  | succ n IH =>
    intro F h₁ h₂ hm
    have hderiv_eq : derivWithin F (s ∩ Set.Iic a) a = derivWithin F (s ∩ Set.Ici a) a := by
      have h := hm 1 (by omega)
      rwa [iteratedDerivWithin_one, iteratedDerivWithin_one] at h
    have hdL : DifferentiableWithinAt ℝ F (s ∩ Set.Iic a) a :=
      (h₁.differentiableOn (by simp)) a ⟨ha, le_refl a⟩
    have hdR : DifferentiableWithinAt ℝ F (s ∩ Set.Ici a) a :=
      (h₂.differentiableOn (by simp)) a ⟨ha, le_refl a⟩
    have hU : HasDerivWithinAt F (derivWithin F (s ∩ Set.Iic a) a) s a := by
      have hHR : HasDerivWithinAt F (derivWithin F (s ∩ Set.Iic a) a) (s ∩ Set.Ici a) a := by
        rw [hderiv_eq]; exact hdR.hasDerivWithinAt
      have hu := hdL.hasDerivWithinAt.union hHR
      rwa [hunion] at hu
    have hderiv_s : derivWithin F s a = derivWithin F (s ∩ Set.Iic a) a := hU.derivWithin (hs a ha)
    have hEqL : Set.EqOn (derivWithin F s) (derivWithin F (s ∩ Set.Iic a)) (s ∩ Set.Iic a) := by
      intro y hy
      rcases eq_or_lt_of_le (Set.mem_Iic.mp hy.2) with hya | hya
      · rw [hya]; exact hderiv_s
      · exact derivWithin_congr_set (inter_Iic_eventuallyEq hya).symm
    have hEqR : Set.EqOn (derivWithin F s) (derivWithin F (s ∩ Set.Ici a)) (s ∩ Set.Ici a) := by
      intro y hy
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hy.2) with hya | hya
      · rw [← hya, hderiv_s]; exact hderiv_eq
      · exact derivWithin_congr_set (inter_Ici_eventuallyEq hya).symm
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hs]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases lt_trichotomy x a with hxa | hxa | hxa
      · have hd : DifferentiableWithinAt ℝ F (s ∩ Set.Iic a) x :=
          (h₁.differentiableOn (by simp)) x ⟨hx, le_of_lt hxa⟩
        exact (differentiableWithinAt_congr_set (inter_Iic_eventuallyEq hxa)).mp hd
      · rw [hxa]; exact hU.differentiableWithinAt
      · have hd : DifferentiableWithinAt ℝ F (s ∩ Set.Ici a) x :=
          (h₂.differentiableOn (by simp)) x ⟨hx, le_of_lt hxa⟩
        exact (differentiableWithinAt_congr_set (inter_Ici_eventuallyEq hxa)).mp hd
    · intro hω; exact absurd hω (by simp)
    · refine IH (derivWithin F s) ?_ ?_ ?_
      · exact ((h₁.derivWithin hsL (by norm_cast)).congr (fun y hy => hEqL hy))
      · exact ((h₂.derivWithin hsR (by norm_cast)).congr (fun y hy => hEqR hy))
      · intro j hj
        have hL : iteratedDerivWithin j (derivWithin F s) (s ∩ Set.Iic a) a
                = iteratedDerivWithin (j + 1) F (s ∩ Set.Iic a) a := by
          rw [iteratedDerivWithin_succ']
          exact iteratedDerivWithin_congr (fun y hy => hEqL hy) ⟨ha, le_refl a⟩
        have hR : iteratedDerivWithin j (derivWithin F s) (s ∩ Set.Ici a) a
                = iteratedDerivWithin (j + 1) F (s ∩ Set.Ici a) a := by
          rw [iteratedDerivWithin_succ']
          exact iteratedDerivWithin_congr (fun y hy => hEqR hy) ⟨ha, le_refl a⟩
        rw [hL, hR]
        exact hm (j + 1) (by omega)

private theorem contDiff_glue {a : ℝ} {k : ℕ} {F : ℝ → ℝ}
    (h₁ : ContDiffOn ℝ (k : ℕ) F (Set.Iic a)) (h₂ : ContDiffOn ℝ (k : ℕ) F (Set.Ici a))
    (hm : ∀ j, j ≤ k → iteratedDerivWithin j F (Set.Iic a) a
                     = iteratedDerivWithin j F (Set.Ici a) a) :
    ContDiff ℝ (k : ℕ) F := by
  rw [← contDiffOn_univ]
  have hL : Set.univ ∩ Set.Iic a = Set.Iic a := Set.univ_inter _
  have hR : Set.univ ∩ Set.Ici a = Set.Ici a := Set.univ_inter _
  refine contDiffOn_glue (Set.mem_univ a) uniqueDiffOn_univ ?_ ?_ k F ?_ ?_ ?_
  · rw [hL]; exact uniqueDiffOn_Iic a
  · rw [hR]; exact uniqueDiffOn_Ici a
  · rw [hL]; exact h₁
  · rw [hR]; exact h₂
  · intro j hj; rw [hL, hR]; exact hm j hj

theorem exists_contDiff_extend_of_contDiffOn_Icc
    {T : ℝ} (hT : 0 < T) (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ (k : ℕ) g (Set.Icc (0 : ℝ) T)) :
    ∃ G : ℝ → ℝ, ContDiff ℝ (k : ℕ) G ∧ Set.EqOn G g (Set.Icc (0 : ℝ) T) := by
  classical
  set P0 : ℝ → ℝ := fun x => taylorWithinEval g k (Set.Icc (0 : ℝ) T) 0 x with hP0
  set PT : ℝ → ℝ := fun x => taylorWithinEval g k (Set.Icc (0 : ℝ) T) T x with hPT
  have hP0sm : ContDiff ℝ (k : ℕ) P0 := by
    rw [hP0]
    have : (fun x => taylorWithinEval g k (Set.Icc (0 : ℝ) T) 0 x)
        = fun x => ∑ i ∈ Finset.range (k + 1),
            ((i ! : ℝ)⁻¹ * iteratedDerivWithin i g (Set.Icc (0 : ℝ) T) 0) * (x - 0) ^ i := by
      funext x; rw [taylor_within_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [smul_eq_mul]; ring
    rw [this]; fun_prop
  have hPTsm : ContDiff ℝ (k : ℕ) PT := by
    rw [hPT]
    have : (fun x => taylorWithinEval g k (Set.Icc (0 : ℝ) T) T x)
        = fun x => ∑ i ∈ Finset.range (k + 1),
            ((i ! : ℝ)⁻¹ * iteratedDerivWithin i g (Set.Icc (0 : ℝ) T) T) * (x - T) ^ i := by
      funext x; rw [taylor_within_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [smul_eq_mul]; ring
    rw [this]; fun_prop
  set GR : ℝ → ℝ := fun x => if x ≤ T then g x else PT x with hGR
  have hIciIic : Set.Ici (0 : ℝ) ∩ Set.Iic T = Set.Icc 0 T := Set.Ici_inter_Iic
  have hIciIci : Set.Ici (0 : ℝ) ∩ Set.Ici T = Set.Ici T :=
    Set.inter_eq_right.mpr (Set.Ici_subset_Ici.mpr hT.le)
  have hGR_Ici : ContDiffOn ℝ (k : ℕ) GR (Set.Ici 0) := by
    refine contDiffOn_glue (a := T) (s := Set.Ici 0) (Set.mem_Ici.mpr hT.le) (uniqueDiffOn_Ici 0)
      ?_ ?_ k GR ?_ ?_ ?_
    · rw [hIciIic]; exact uniqueDiffOn_Icc hT
    · rw [hIciIci]; exact uniqueDiffOn_Ici T
    · rw [hIciIic]
      refine hg.congr (fun y hy => ?_)
      simp only [hGR]; rw [if_pos hy.2]
    · rw [hIciIci]
      refine hPTsm.contDiffOn.congr (fun y hy => ?_)
      simp only [hGR]
      by_cases hyT : y ≤ T
      · rw [if_pos hyT, le_antisymm hyT (Set.mem_Ici.mp hy)]
        simp only [hPT, taylorWithinEval_self]
      · rw [if_neg hyT]
    · intro j hj
      rw [hIciIic, hIciIci]
      have hlhs : iteratedDerivWithin j GR (Set.Icc 0 T) T = iteratedDerivWithin j g (Set.Icc 0 T) T :=
        iteratedDerivWithin_congr (fun y hy => by simp only [hGR]; rw [if_pos hy.2])
          ⟨hT.le, le_refl T⟩
      have hrhs : iteratedDerivWithin j GR (Set.Ici T) T = iteratedDerivWithin j PT (Set.Ici T) T := by
        refine iteratedDerivWithin_congr (fun y hy => ?_) Set.self_mem_Ici
        simp only [hGR]
        by_cases hyT : y ≤ T
        · rw [if_pos hyT, le_antisymm hyT (Set.mem_Ici.mp hy)]
          simp only [hPT, taylorWithinEval_self]
        · rw [if_neg hyT]
      rw [hlhs, hrhs,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici T)
          (hPTsm.contDiffAt.of_le (by exact_mod_cast hj)) Set.self_mem_Ici,
        hPT]
      exact (iteratedDeriv_taylorWithinEval_eq g k (Set.Icc 0 T) T hj).symm
  set G : ℝ → ℝ := fun x => if x ≤ 0 then P0 x else GR x with hG
  have hGRzero : GR 0 = g 0 := by simp only [hGR]; rw [if_pos hT.le]
  have hP0zero : P0 0 = g 0 := by rw [hP0]; simp
  have hG_contDiff : ContDiff ℝ (k : ℕ) G := by
    refine contDiff_glue (a := 0) (F := G) ?_ ?_ ?_
    · refine hP0sm.contDiffOn.congr (fun y hy => ?_)
      simp only [hG]; rw [if_pos (Set.mem_Iic.mp hy)]
    · refine hGR_Ici.congr (fun y hy => ?_)
      simp only [hG]
      by_cases hy0 : y ≤ 0
      · rw [if_pos hy0, le_antisymm hy0 (Set.mem_Ici.mp hy), hGRzero, hP0zero]
      · rw [if_neg hy0]
    · intro j hj
      have hlhs : iteratedDerivWithin j G (Set.Iic 0) 0 = iteratedDerivWithin j P0 (Set.Iic 0) 0 :=
        iteratedDerivWithin_congr
          (fun y hy => by simp only [hG]; rw [if_pos (Set.mem_Iic.mp hy)]) Set.self_mem_Iic
      have hset : Set.Ici (0 : ℝ) =ᶠ[𝓝 (0 : ℝ)] Set.Icc 0 T := by
        rw [eventuallyEq_set]
        filter_upwards [Iio_mem_nhds hT] with y hy
        simp only [Set.mem_Iio] at hy
        simp only [Set.mem_Ici, Set.mem_Icc]
        exact ⟨fun h0 => ⟨h0, le_of_lt hy⟩, fun h => h.1⟩
      have hGRg : GR =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] g := by
        have hmem : Set.Iic T ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hT)
        filter_upwards [hmem] with y hy
        simp only [hGR]; rw [if_pos (Set.mem_Iic.mp hy)]
      have hrhs : iteratedDerivWithin j G (Set.Ici 0) 0 = iteratedDerivWithin j g (Set.Icc 0 T) 0 := by
        have hGGR : iteratedDerivWithin j G (Set.Ici 0) 0 = iteratedDerivWithin j GR (Set.Ici 0) 0 :=
          iteratedDerivWithin_congr (fun y hy => by
            simp only [hG]
            by_cases hy0 : y ≤ 0
            · rw [if_pos hy0, le_antisymm hy0 (Set.mem_Ici.mp hy), hGRzero, hP0zero]
            · rw [if_neg hy0]) Set.self_mem_Ici
        rw [hGGR, hGRg.iteratedDerivWithin_eq hGRzero, iteratedDerivWithin_congr_set j hset]
      rw [hlhs, hrhs,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0)
          (hP0sm.contDiffAt.of_le (by exact_mod_cast hj)) Set.self_mem_Iic,
        hP0]
      exact iteratedDeriv_taylorWithinEval_eq g k (Set.Icc 0 T) 0 hj
  refine ⟨G, hG_contDiff, fun y hy => ?_⟩
  simp only [hG]
  by_cases hy0 : y ≤ 0
  · rw [if_pos hy0, le_antisymm hy0 hy.1, hP0zero]
  · rw [if_neg hy0]
    simp only [hGR]; rw [if_pos hy.2]

end Analysis
end DifferentialGeometry
