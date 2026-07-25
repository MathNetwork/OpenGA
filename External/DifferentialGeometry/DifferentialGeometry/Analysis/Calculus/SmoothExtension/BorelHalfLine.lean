import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

def borelCutoff (s : ℝ) : ℝ := Real.smoothTransition (2 - s ^ 2)

theorem borelCutoff_contDiff {n : ℕ∞} : ContDiff ℝ n borelCutoff := by
  unfold borelCutoff
  have h : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => 2 - s ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  exact Real.smoothTransition.contDiff.comp h

theorem borelCutoff_eq_one {s : ℝ} (hs : s ^ 2 ≤ 1) : borelCutoff s = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  linarith

theorem borelCutoff_eq_zero {s : ℝ} (hs : 2 ≤ s ^ 2) : borelCutoff s = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  linarith

def borelBumpMono (n : ℕ) (s : ℝ) : ℝ := borelCutoff s * s ^ n / (Nat.factorial n : ℝ)

theorem borelBumpMono_contDiff {N : ℕ∞} (n : ℕ) :
    ContDiff ℝ N (borelBumpMono n) :=
  ((borelCutoff_contDiff.mul ((contDiff_id).pow n)).div_const _)

theorem borelBumpMono_comp_smul_contDiff {N : ℕ∞} (n : ℕ) (a : ℝ) :
    ContDiff ℝ N (fun s : ℝ => borelBumpMono n (a * s)) :=
  (borelBumpMono_contDiff n).comp (contDiff_const.mul contDiff_id)

theorem borelBumpMono_support_subset (n : ℕ) :
    Function.support (borelBumpMono n) ⊆ Icc (-2 : ℝ) 2 := by
  intro s hs
  by_contra hmem
  apply hs
  have h2 : (2 : ℝ) ≤ s ^ 2 := by
    rcases not_and_or.1 hmem with h | h
    · have : s < -2 := lt_of_not_ge h
      nlinarith
    · have : (2 : ℝ) < s := lt_of_not_ge h
      nlinarith
  simp [borelBumpMono, borelCutoff_eq_zero h2]

theorem borelBumpMono_hasCompactSupport (n : ℕ) :
    HasCompactSupport (borelBumpMono n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (borelBumpMono_support_subset n)

theorem borelBumpMono_deriv_bound (n : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ k ≤ n, ∀ s : ℝ,
      ‖iteratedDeriv k (borelBumpMono n) s‖ ≤ G := by
  have hbnd : ∀ k, ∃ C : ℝ, ∀ s : ℝ,
      ‖iteratedDeriv k (borelBumpMono n) s‖ ≤ C := by
    intro k
    have hcs : HasCompactSupport (iteratedFDeriv ℝ k (borelBumpMono n)) :=
      (borelBumpMono_hasCompactSupport n).iteratedFDeriv k
    have hcont : Continuous (iteratedFDeriv ℝ k (borelBumpMono n)) :=
      (borelBumpMono_contDiff (N := (⊤ : ℕ∞)) n).continuous_iteratedFDeriv
        (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    refine ⟨C, fun s => ?_⟩
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC s
  choose C hC using hbnd
  refine ⟨(Finset.range (n + 1)).sup' (by simp) (fun k => max (C k) 0), ?_, ?_⟩
  · exact le_trans (le_max_right _ _)
      (Finset.le_sup' (fun k => max (C k) 0) (by simp : (0 : ℕ) ∈ Finset.range (n + 1)))
  · intro k hk s
    refine le_trans (hC k s) ?_
    refine le_trans (le_max_left (C k) 0) ?_
    exact Finset.le_sup' (fun k => max (C k) 0)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def borelScale (c : ℕ → F) (n : ℕ) : ℝ :=
  max 1 (2 ^ n * Classical.choose (borelBumpMono_deriv_bound n) * (1 + ‖c n‖))

omit [NormedSpace ℝ F] in
private theorem one_le_borelScale (c : ℕ → F) (n : ℕ) : 1 ≤ borelScale c n :=
  le_max_left _ _

omit [NormedSpace ℝ F] in
private theorem borelScale_pos (c : ℕ → F) (n : ℕ) : 0 < borelScale c n :=
  lt_of_lt_of_le one_pos (one_le_borelScale c n)

private def borelTerm (c : ℕ → F) (n : ℕ) (t : ℝ) : F :=
  ((borelScale c n)⁻¹ ^ n * borelBumpMono n (borelScale c n * t)) • c n

private theorem borelTerm_contDiff {N : ℕ∞} (c : ℕ → F) (n : ℕ) :
    ContDiff ℝ N (borelTerm c n) := by
  refine ContDiff.smul ?_ contDiff_const
  exact contDiff_const.mul (borelBumpMono_comp_smul_contDiff n (borelScale c n))

private theorem borelTerm_hasCompactSupport (c : ℕ → F) (n : ℕ) :
    HasCompactSupport (borelTerm c n) := by
  apply HasCompactSupport.smul_right
    (f := fun t => (borelScale c n)⁻¹ ^ n * borelBumpMono n (borelScale c n * t))
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-(2 / borelScale c n)) (2 / borelScale c n)) isCompact_Icc
  intro t ht
  by_contra hmem
  apply ht
  have hL0 : 0 < borelScale c n := borelScale_pos c n
  have h2 : 2 ≤ (borelScale c n * t) ^ 2 := by
    rcases not_and_or.1 hmem with h | h
    · have ht' : t < -(2 / borelScale c n) := lt_of_not_ge h
      have hlt : borelScale c n * t < borelScale c n * (-(2 / borelScale c n)) :=
        mul_lt_mul_of_pos_left ht' hL0
      rw [mul_neg, mul_div_cancel₀ _ hL0.ne'] at hlt
      nlinarith
    · have ht' : 2 / borelScale c n < t := lt_of_not_ge h
      have hlt : borelScale c n * (2 / borelScale c n) < borelScale c n * t :=
        mul_lt_mul_of_pos_left ht' hL0
      rw [mul_div_cancel₀ _ hL0.ne'] at hlt
      nlinarith
  simp only [borelBumpMono, borelCutoff_eq_zero h2, zero_mul, zero_div, mul_zero]

private theorem borelTerm_iteratedDeriv_global_bound (c : ℕ → F) (n k : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, ‖iteratedDeriv k (borelTerm c n) t‖ ≤ B := by
  have hcs : HasCompactSupport (iteratedFDeriv ℝ k (borelTerm c n)) :=
    (borelTerm_hasCompactSupport c n).iteratedFDeriv k
  have hcont : Continuous (iteratedFDeriv ℝ k (borelTerm c n)) :=
    (borelTerm_contDiff (N := (⊤ : ℕ∞)) c n).continuous_iteratedFDeriv
      (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hcont
  refine ⟨B, fun t => ?_⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hB t

private theorem borelTerm_iteratedDeriv (c : ℕ → F) (n k : ℕ) (t : ℝ) :
    iteratedDeriv k (borelTerm c n) t =
      ((borelScale c n)⁻¹ ^ n *
        (borelScale c n) ^ k * iteratedDeriv k (borelBumpMono n) (borelScale c n * t))
        • c n := by
  have hcd : ContDiffAt ℝ k (fun s => borelBumpMono n (borelScale c n * s)) t :=
    (borelBumpMono_comp_smul_contDiff (N := (k : ℕ∞)) n (borelScale c n)).contDiffAt
  have hsmul : iteratedDeriv k (borelTerm c n) t =
      (iteratedDeriv k (fun s => (borelScale c n)⁻¹ ^ n *
        borelBumpMono n (borelScale c n * s)) t) • c n :=
    iteratedDeriv_smul_const (contDiff_const.contDiffAt.mul hcd) _
  rw [hsmul]
  congr 1
  have hconst : iteratedDeriv k (fun s => (borelScale c n)⁻¹ ^ n *
      borelBumpMono n (borelScale c n * s)) t =
      (borelScale c n)⁻¹ ^ n •
        iteratedDeriv k (fun s => borelBumpMono n (borelScale c n * s)) t := by
    have := iteratedDeriv_const_smul
      (𝕜 := ℝ) (R := ℝ) (n := k) (x := t)
      (f := fun s => borelBumpMono n (borelScale c n * s)) hcd ((borelScale c n)⁻¹ ^ n)
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  rw [hconst]
  have hcomp : iteratedDeriv k (fun s => borelBumpMono n (borelScale c n * s)) t =
      (borelScale c n) ^ k • iteratedDeriv k (borelBumpMono n) (borelScale c n * t) := by
    have h := iteratedDeriv_comp_const_smul
      (n := k) (f := borelBumpMono n)
      (borelBumpMono_contDiff (N := (k : ℕ∞)) n) (borelScale c n)
    exact congrFun h t
  rw [hcomp]
  simp only [smul_eq_mul]
  ring

private theorem borelTerm_iteratedDeriv_bound (c : ℕ → F) {n k : ℕ} (hkn : k < n) (t : ℝ) :
    ‖iteratedDeriv k (borelTerm c n) t‖ ≤ (2 : ℝ)⁻¹ ^ n := by
  set G : ℝ := Classical.choose (borelBumpMono_deriv_bound n) with hGdef
  have hGspec := Classical.choose_spec (borelBumpMono_deriv_bound n)
  rw [← hGdef] at hGspec
  obtain ⟨hGnn, hGbound⟩ := hGspec
  set L : ℝ := borelScale c n with hLdef
  have hL1 : 1 ≤ L := one_le_borelScale c n
  have hL0 : 0 < L := borelScale_pos c n
  have hLmax : 2 ^ n * G * (1 + ‖c n‖) ≤ L := le_max_right _ _
  rw [borelTerm_iteratedDeriv, norm_smul]
  have hcn0 : (0 : ℝ) ≤ ‖c n‖ := norm_nonneg _
  have hD : ‖iteratedDeriv k (borelBumpMono n) (L * t)‖ ≤ G :=
    hGbound k (le_of_lt hkn) (L * t)
  have hpow : L⁻¹ ^ n * L ^ k ≤ L⁻¹ := by
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    have hrw : L ^ n * L⁻¹ = L ^ (n - 1) := by
      have : L ^ n = L ^ (n - 1) * L := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [this, mul_assoc, mul_inv_cancel₀ hL0.ne', mul_one]
    rw [hrw]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hcoeff : ‖L⁻¹ ^ n * L ^ k * iteratedDeriv k (borelBumpMono n) (L * t)‖
      ≤ L⁻¹ * G := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_inv, abs_of_pos hL0]
    exact mul_le_mul hpow hD (norm_nonneg _) (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_right hcoeff hcn0) ?_
  rcases eq_or_lt_of_le hGnn with hG0 | hGpos
  · rw [← hG0]
    simp only [mul_zero, zero_mul]
    positivity
  · have hLinv : L⁻¹ ≤ (2 ^ n * G * (1 + ‖c n‖))⁻¹ :=
      inv_anti₀ (by positivity) hLmax
    have h2pos : (0 : ℝ) < 2 ^ n := by positivity
    have h1cn : (0 : ℝ) < 1 + ‖c n‖ := by positivity
    have hcnle : ‖c n‖ ≤ 1 + ‖c n‖ := by linarith
    calc L⁻¹ * G * ‖c n‖
        ≤ (2 ^ n * G * (1 + ‖c n‖))⁻¹ * G * ‖c n‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLinv hGnn) hcn0
      _ = ‖c n‖ / (2 ^ n * (1 + ‖c n‖)) := by
          field_simp
      _ ≤ (2 : ℝ)⁻¹ ^ n := by
          rw [div_le_iff₀ (by positivity), inv_pow, inv_mul_eq_div, le_div_iff₀ h2pos]
          calc ‖c n‖ * 2 ^ n ≤ (1 + ‖c n‖) * 2 ^ n :=
                mul_le_mul_of_nonneg_right hcnle h2pos.le
            _ = 2 ^ n * (1 + ‖c n‖) := by ring

private def borelDomBound (c : ℕ → F) (k n : ℕ) : ℝ :=
  if k < n then (2 : ℝ)⁻¹ ^ n
  else Classical.choose (borelTerm_iteratedDeriv_global_bound c n k)

private theorem borelDomBound_summable (c : ℕ → F) (k : ℕ) :
    Summable (borelDomBound c k) := by
  have hgeom : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) := by
    simpa only [one_div] using summable_geometric_two
  refine Summable.congr_cofinite hgeom ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop k] with n hn
  rw [borelDomBound, if_pos hn]

private theorem borelDomBound_bound (c : ℕ → F) (k n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (borelTerm c n) t‖ ≤ borelDomBound c k n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, borelDomBound]
  by_cases hkn : k < n
  · rw [if_pos hkn]
    exact borelTerm_iteratedDeriv_bound c hkn t
  · rw [if_neg hkn]
    exact Classical.choose_spec (borelTerm_iteratedDeriv_global_bound c n k) t

private theorem borelTerm_iteratedDeriv_zero (c : ℕ → F) (n k : ℕ) :
    iteratedDeriv k (borelTerm c n) 0 = (if n = k then (1 : ℝ) else 0) • c n := by
  have hL0 : 0 < borelScale c n := borelScale_pos c n
  have hev : borelTerm c n =ᶠ[𝓝 (0 : ℝ)]
      fun t => ((borelScale c n)⁻¹ ^ n * ((borelScale c n * t) ^ n / (Nat.factorial n : ℝ)))
        • c n := by
    refine eventuallyEq_of_mem (Ioo_mem_nhds (a := -(1 / borelScale c n))
      (b := 1 / borelScale c n) (by simpa using by positivity) (by positivity)) ?_
    intro t ht
    have h1 : (borelScale c n * t) ^ 2 ≤ 1 := by
      rw [mul_pow]
      have htabs : |t| < 1 / borelScale c n := by
        rw [abs_lt]; exact ⟨by simpa using ht.1, ht.2⟩
      have ht2 : t ^ 2 ≤ (1 / borelScale c n) ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) htabs.le 2
      calc borelScale c n ^ 2 * t ^ 2
          ≤ borelScale c n ^ 2 * (1 / borelScale c n) ^ 2 :=
            mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ = 1 := by field_simp
    simp only [borelTerm, borelBumpMono, borelCutoff_eq_one h1, one_mul]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev]
  have hcd : ContDiffAt ℝ k
      (fun t => (borelScale c n)⁻¹ ^ n * ((borelScale c n * t) ^ n / (Nat.factorial n : ℝ))) 0 := by
    fun_prop
  rw [iteratedDeriv_smul_const hcd]
  have hpow : iteratedDeriv k
      (fun t => (borelScale c n)⁻¹ ^ n * ((borelScale c n * t) ^ n / (Nat.factorial n : ℝ))) 0 =
      if n = k then (1 : ℝ) else 0 := by
    have hfun : (fun t => (borelScale c n)⁻¹ ^ n *
        ((borelScale c n * t) ^ n / (Nat.factorial n : ℝ))) =
        (fun t => ((borelScale c n)⁻¹ ^ n * (borelScale c n) ^ n / (Nat.factorial n : ℝ)) *
          t ^ n) := by
      funext t; rw [mul_pow]; ring
    rw [hfun]
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    have hLn : (borelScale c n)⁻¹ ^ n * borelScale c n ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hL0.ne', one_pow]
    rcases eq_or_ne n k with h | h
    · subst h
      rw [if_pos rfl, if_pos rfl]
      have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      rw [div_mul_cancel₀ _ hfac, hLn]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
      simp
  rw [hpow]

private theorem borel_jet_realize [CompleteSpace F] (c : ℕ → F) :
    ∃ h : ℝ → F, ContDiff ℝ ∞ h ∧ ∀ k : ℕ, iteratedDeriv k h 0 = c k := by
  refine ⟨fun t => ∑' n, borelTerm c n t, ?_, ?_⟩
  · exact contDiff_tsum (N := (⊤ : ℕ∞)) (v := borelDomBound c)
      (fun n => borelTerm_contDiff c n)
      (fun k _ => borelDomBound_summable c k)
      (fun k n t _ => borelDomBound_bound c k n t)
  · intro k
    have hFD : iteratedFDeriv ℝ k (fun t => ∑' n, borelTerm c n t) 0 =
        ∑' n, iteratedFDeriv ℝ k (borelTerm c n) 0 :=
      iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) (v := borelDomBound c)
        (fun n => borelTerm_contDiff c n)
        (fun k _ => borelDomBound_summable c k)
        (fun k n t _ => borelDomBound_bound c k n t)
        (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞)) 0
    rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply, hFD,
      ← LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm.toContinuousLinearEquiv.map_tsum]
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    have hterm : ∀ n, (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm
        (iteratedFDeriv ℝ k (borelTerm c n) 0) = (if n = k then (1 : ℝ) else 0) • c n := by
      intro n
      rw [← Function.comp_apply (f := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm),
        ← iteratedDeriv_eq_equiv_comp]
      exact borelTerm_iteratedDeriv_zero c n k
    rw [tsum_congr hterm]
    rw [tsum_eq_single k (fun n hn => by rw [if_neg hn, zero_smul])]
    rw [if_pos rfl, one_smul]

theorem borel_halfLine_extend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (g : ℝ → F) (_hg : ContDiffOn ℝ ∞ g (Set.Ici (0:ℝ))) :
    ∃ h : ℝ → F, ContDiff ℝ ∞ h ∧
      (∀ n : ℕ, iteratedDeriv n h 0 = iteratedDerivWithin n g (Set.Ici (0:ℝ)) 0) :=
  borel_jet_realize (fun n => iteratedDerivWithin n g (Set.Ici (0:ℝ)) 0)

end Analysis
end DifferentialGeometry
