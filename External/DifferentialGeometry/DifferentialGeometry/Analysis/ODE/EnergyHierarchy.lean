import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Real Filter

open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

theorem mul_sqrt_le_sq_div_four_add (s : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    s * Real.sqrt M ≤ s ^ 2 / 4 + M := by
  nlinarith [sq_nonneg (Real.sqrt M - s / 2), Real.sq_sqrt hM, Real.sqrt_nonneg M]

theorem energy_hierarchy_uniform_bound
    {T c C : ℝ} {M M' : ℕ → ℝ → ℝ} {s B0 : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hMnonneg : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ M k t)
    (hcont : ∀ k, ContinuousOn (M k) (Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt (M k) (M' k t) (Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Ico (0 : ℝ) T,
      M' k t ≤ -c * (M (k + 1) t) + C * (M k t) + s k * Real.sqrt (M k t))
    (hinit : ∀ k, M k 0 ≤ B0 k) :
    ∀ k, ∃ Bound : ℝ, ∀ t ∈ Icc (0 : ℝ) T, M k t ≤ Bound := by
  intro k
  set K : ℝ := C + 1 with hKdef
  set ε : ℝ := (s k) ^ 2 / 4 with hεdef
  refine ⟨gronwallBound (B0 k) K ε T, ?_⟩
  have hf' : ∀ t ∈ Ico (0 : ℝ) T, ∀ r, M' k t < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (M k z - M k t) < r := by
    intro t ht r hr
    have := (hderiv k t ht).liminf_right_slope_le hr
    refine this.mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, M' k t ≤ K * M k t + ε := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    have hMt : 0 ≤ M k t := hMnonneg k t htIcc
    have hMt1 : 0 ≤ M (k + 1) t := hMnonneg (k + 1) t htIcc
    have hneg : -c * (M (k + 1) t) ≤ 0 := by
      have : 0 ≤ c * (M (k + 1) t) := mul_nonneg hc.le hMt1
      linarith
    have hdiss' := hdiss k t ht
    have hyoung : s k * Real.sqrt (M k t) ≤ (s k) ^ 2 / 4 + M k t :=
      mul_sqrt_le_sq_div_four_add (s k) hMt
    rw [hKdef, hεdef]
    nlinarith [hneg, hdiss', hyoung]
  have ha : M k 0 ≤ B0 k := hinit k
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    (hcont k) hf' (by simpa using ha) hbound
  intro t htIcc
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  have hεnn : 0 ≤ ε := by rw [hεdef]; positivity
  have hB0nn : 0 ≤ B0 k := le_trans (hMnonneg k 0 (by
      refine ⟨le_refl 0, ?_⟩; exact htIcc.1.trans htIcc.2)) ha
  have hmono : gronwallBound (B0 k) K ε (t - 0) ≤ gronwallBound (B0 k) K ε T := by
    have := gronwallBound_mono (δ := B0 k) (K := K) (ε := ε) hB0nn hεnn hKnn
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    have := this hle
    simpa using this
  calc M k t ≤ gronwallBound (B0 k) K ε (t - 0) := hgron t htIcc
    _ ≤ gronwallBound (B0 k) K ε T := hmono

end DifferentialGeometry.Analysis.ODE
