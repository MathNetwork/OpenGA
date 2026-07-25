import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false


















namespace DifferentialGeometry

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





lemma gronwallBound_zero_mono_eps
    {K eps₁ eps₂ x : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) (heps : eps₁ ≤ eps₂) :
    gronwallBound 0 K eps₁ x ≤ gronwallBound 0 K eps₂ x := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · rw [← hK0]
    simp only [gronwallBound_K0, zero_add]
    exact mul_le_mul_of_nonneg_right heps hx
  · have hKne : K ≠ 0 := ne_of_gt hKpos
    have hKx_nonneg : 0 ≤ K * x := mul_nonneg hK hx
    have hexp_nonneg : 0 ≤ Real.exp (K * x) - 1 := by
      have hexp : 1 ≤ Real.exp (K * x) := Real.one_le_exp hKx_nonneg
      linarith
    have hcoef : 0 ≤ (Real.exp (K * x) - 1) / K :=
      div_nonneg hexp_nonneg hKpos.le
    simp only [gronwallBound_of_K_ne_0 hKne, zero_mul, zero_add]
    calc
      eps₁ / K * (Real.exp (K * x) - 1)
          = eps₁ * ((Real.exp (K * x) - 1) / K) := by
              field_simp [hKne]
      _ ≤ eps₂ * ((Real.exp (K * x) - 1) / K) :=
          mul_le_mul_of_nonneg_right heps hcoef
      _ = eps₂ / K * (Real.exp (K * x) - 1) := by
          field_simp [hKne]



lemma gronwallBound_zero_mul_eps
    {K eps x a : ℝ} :
    gronwallBound 0 K (a * eps) x = a * gronwallBound 0 K eps x := by
  rcases eq_or_ne K 0 with hK0 | hKne
  · rw [hK0]
    simp only [gronwallBound_K0, zero_add]
    ring
  · simp only [gronwallBound_of_K_ne_0 hKne, zero_mul, zero_add]
    field_simp [hKne]



lemma exists_gron_small
    {K D B₀ : ℝ} (hB₀ : 0 < B₀) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧
      B ≤ B₀ - gronwallBound 0 (max K 1) (K * (b * D)) 1 := by
  let L : ℝ := max K 1
  let C : ℝ := (Real.exp L - 1) / L
  let A : ℝ := K * D * C
  let b : ℝ := B₀ / (2 * (A + 1))
  let B : ℝ := B₀ / 2
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hL_nonneg : 0 ≤ L := hL_pos.le
  have hC_nonneg : 0 ≤ C := by
    have hexp : 1 ≤ Real.exp L := Real.one_le_exp hL_nonneg
    have hnum : 0 ≤ Real.exp L - 1 := by linarith
    exact div_nonneg hnum hL_pos.le
  have hA_nonneg : 0 ≤ A := by
    exact mul_nonneg (mul_nonneg hK hD) hC_nonneg
  have hA1_pos : 0 < A + 1 := by linarith
  have hden_pos : 0 < 2 * (A + 1) := by positivity
  refine ⟨b, B, div_pos hB₀ hden_pos, half_pos hB₀, ?_⟩
  have hgb :
      gronwallBound 0 L (K * (b * D)) 1 = b * A := by
    simp only [gronwallBound_of_K_ne_0 hL_ne, zero_mul, zero_add]
    dsimp [A, C]
    field_simp [hL_ne]
  have hfrac_le : A / (A + 1) ≤ 1 := by
    rw [div_le_iff₀ hA1_pos]
    linarith
  have hbA_le : b * A ≤ B₀ / 2 := by
    have hhalf_nonneg : 0 ≤ B₀ / 2 := by positivity
    calc
      b * A = (B₀ / 2) * (A / (A + 1)) := by
        dsimp [b]
        field_simp [hA1_pos.ne']
      _ ≤ (B₀ / 2) * 1 := mul_le_mul_of_nonneg_left hfrac_le hhalf_nonneg
      _ = B₀ / 2 := by ring
  dsimp [B]
  rw [hgb]
  linarith



lemma exists_gron_smallK
    {D B₀ : ℝ} (hB₀ : 0 < B₀) (hD : 0 ≤ D) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ {k : ℝ}, 0 ≤ k → k ≤ K →
        B ≤ B₀ - gronwallBound 0 (max k 1) (k * D) 1 := by
  let C : ℝ := Real.exp 1 - 1
  let A : ℝ := D * C
  let K : ℝ := min 1 (B₀ / (2 * (A + 1)))
  let B : ℝ := B₀ / 2
  have hC_nonneg : 0 ≤ C := by
    have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    dsimp [C]
    linarith
  have hA_nonneg : 0 ≤ A := mul_nonneg hD hC_nonneg
  have hA1_pos : 0 < A + 1 := by linarith
  have hden_pos : 0 < 2 * (A + 1) := by positivity
  refine ⟨K, B, lt_min zero_lt_one (div_pos hB₀ hden_pos), half_pos hB₀, ?_⟩
  intro k hk_nonneg hk_le
  have hk_le_one : k ≤ 1 := hk_le.trans (min_le_left _ _)
  have hmax : max k 1 = 1 := max_eq_right hk_le_one
  have hgb :
      gronwallBound 0 (max k 1) (k * D) 1 = k * A := by
    rw [hmax]
    simp only [gronwallBound_of_K_ne_0 one_ne_zero, zero_mul, zero_add]
    dsimp [A, C]
    ring_nf
  have hK_le :
      K ≤ B₀ / (2 * (A + 1)) := min_le_right _ _
  have hfrac_le : A / (A + 1) ≤ 1 := by
    rw [div_le_iff₀ hA1_pos]
    linarith
  have hhalf_nonneg : 0 ≤ B₀ / 2 := by positivity
  have hKA_le :
      (B₀ / (2 * (A + 1))) * A ≤ B₀ / 2 := by
    calc
      (B₀ / (2 * (A + 1))) * A = (B₀ / 2) * (A / (A + 1)) := by
        field_simp [hA1_pos.ne']
      _ ≤ (B₀ / 2) * 1 := mul_le_mul_of_nonneg_left hfrac_le hhalf_nonneg
      _ = B₀ / 2 := by ring
  have hkA_le : k * A ≤ B₀ / 2 := by
    calc
      k * A ≤ K * A := mul_le_mul_of_nonneg_right hk_le hA_nonneg
      _ ≤ (B₀ / (2 * (A + 1))) * A :=
        mul_le_mul_of_nonneg_right hK_le hA_nonneg
      _ ≤ B₀ / 2 := hKA_le
  dsimp [B]
  rw [hgb]
  linarith



theorem norm_le_gronwall_secondOrder
    {Y Y' Y'' : ℝ → E} {K eps δ b : ℝ}
    (hK : 0 ≤ K) (heps : 0 ≤ eps)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖ + eps)
    (h0 : ‖Y 0‖ ≤ δ) (h0' : ‖Y' 0‖ ≤ δ) :
    ∀ t ∈ Icc 0 b, ‖Y t‖ ≤ gronwallBound δ (max K 1) eps t := by
  set Z : ℝ → E × E := fun t => (Y t, Y' t) with hZdef
  have hcZ : ContinuousOn Z (Icc 0 b) := hcY.prodMk hcY'
  have hdZ : ∀ t ∈ Ico 0 b,
      HasDerivWithinAt Z (Y' t, Y'' t) (Ici t) t :=
    fun t ht => (hdY t ht).prodMk (hdY' t ht)
  have h0Z : ‖Z 0‖ ≤ δ := by
    rw [Prod.norm_def]
    exact max_le h0 h0'
  have hboundZ : ∀ t ∈ Ico 0 b,
      ‖(Y' t, Y'' t)‖ ≤ max K 1 * ‖Z t‖ + eps := by
    intro t ht
    rw [Prod.norm_def]
    have h1 : ‖Y' t‖ ≤ ‖Z t‖ := norm_snd_le (Z t)
    have h2 : ‖Y t‖ ≤ ‖Z t‖ := norm_fst_le (Z t)
    have hZ0 : 0 ≤ ‖Z t‖ := norm_nonneg _
    apply max_le
    · calc ‖Y' t‖ ≤ ‖Z t‖ := h1
        _ ≤ max K 1 * ‖Z t‖ := le_mul_of_one_le_left hZ0 (le_max_right K 1)
        _ ≤ max K 1 * ‖Z t‖ + eps := le_add_of_nonneg_right heps
    · calc ‖Y'' t‖ ≤ K * ‖Y t‖ + eps := hbound t ht
        _ ≤ max K 1 * ‖Z t‖ + eps := by
            have hmul : K * ‖Y t‖ ≤ max K 1 * ‖Z t‖ :=
              mul_le_mul (le_max_left K 1) h2 (norm_nonneg _)
                (hK.trans (le_max_left K 1))
            linarith
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcZ hdZ h0Z hboundZ
  intro t ht
  calc ‖Y t‖ ≤ ‖Z t‖ := norm_fst_le (Z t)
    _ ≤ gronwallBound δ (max K 1) eps (t - 0) := hmain t ht
    _ = gronwallBound δ (max K 1) eps t := by rw [sub_zero]






theorem gronwall_sub_linear
    {Y Y' Y'' : ℝ → E} {K b : ℝ} {w : E}
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖)
    (h0 : Y 0 = 0) (h0' : Y' 0 = w) :
    ∀ t ∈ Icc 0 b,
      ‖Y t - t • w‖ ≤ gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t := by
  set Z : ℝ → E := fun t => Y t - t • w with hZ
  set Z' : ℝ → E := fun t => Y' t - w with hZ'
  have heps : 0 ≤ K * (b * ‖w‖) :=
    mul_nonneg hK (mul_nonneg hb (norm_nonneg w))
  have hlin : ∀ (t : ℝ) (s : Set ℝ),
      HasDerivWithinAt (fun x : ℝ => x • w) w s t := by
    intro t s
    simpa using (hasDerivWithinAt_id t s).smul_const w
  have hcZ : ContinuousOn Z (Icc 0 b) :=
    hcY.sub ((continuous_id.smul continuous_const).continuousOn)
  have hcZ' : ContinuousOn Z' (Icc 0 b) := hcY'.sub continuousOn_const
  have hdZ : ∀ t ∈ Ico 0 b, HasDerivWithinAt Z (Z' t) (Ici t) t :=
    fun t ht => (hdY t ht).sub (hlin t (Ici t))
  have hdZ' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Z' (Y'' t) (Ici t) t :=
    fun t ht => (hdY' t ht).sub_const w
  have hZ0 : ‖Z 0‖ ≤ 0 := by simp [hZ, h0]
  have hZ'0 : ‖Z' 0‖ ≤ 0 := by simp [hZ', h0']
  have hboundZ : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Z t‖ + K * (b * ‖w‖) := by
    intro t ht
    have hYt : Y t = Z t + t • w := by simp [hZ]
    have htb : |t| ≤ b := by
      rw [abs_of_nonneg ht.1]; exact ht.2.le
    calc ‖Y'' t‖ ≤ K * ‖Y t‖ := hbound t ht
      _ = K * ‖Z t + t • w‖ := by rw [← hYt]
      _ ≤ K * (‖Z t‖ + ‖t • w‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hK
      _ = K * ‖Z t‖ + K * (|t| * ‖w‖) := by
          rw [norm_smul, Real.norm_eq_abs]; ring
      _ ≤ K * ‖Z t‖ + K * (b * ‖w‖) := by
          have := mul_le_mul_of_nonneg_right htb (norm_nonneg w)
          nlinarith
  exact norm_le_gronwall_secondOrder hK heps hcZ hcZ' hdZ hdZ' hboundZ hZ0 hZ'0




theorem gronwall_le_linear
    {Y Y' Y'' : ℝ → E} {K b : ℝ} {w : E}
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖)
    (h0 : Y 0 = 0) (h0' : Y' 0 = w) :
    ∀ t ∈ Icc 0 b,
      ‖Y t‖ ≤ t * ‖w‖ + gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t := by
  have hsub := gronwall_sub_linear hK hb hcY hcY' hdY hdY' hbound h0 h0'
  intro t ht
  have htw : ‖t • w‖ = t * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc
    ‖Y t‖ = ‖Y t - t • w + t • w‖ := by rw [sub_add_cancel]
    _ ≤ ‖Y t - t • w‖ + ‖t • w‖ := norm_add_le _ _
    _ ≤ gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t + t * ‖w‖ := by
      exact add_le_add (hsub t ht) (le_of_eq htw)
    _ = t * ‖w‖ + gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t := by ring



theorem gronwall_ge_linear
    {Y Y' Y'' : ℝ → E} {K b : ℝ} {w : E}
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖)
    (h0 : Y 0 = 0) (h0' : Y' 0 = w) :
    ∀ t ∈ Icc 0 b,
      t * ‖w‖ - gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t ≤ ‖Y t‖ := by
  have hsub := gronwall_sub_linear hK hb hcY hcY' hdY hdY' hbound h0 h0'
  intro t ht
  have htw : ‖t • w‖ = t * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hlin :
      t * ‖w‖ ≤ ‖Y t‖ + gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t := by
    calc
      t * ‖w‖ = ‖t • w‖ := htw.symm
      _ = ‖Y t - (Y t - t • w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Y t‖ + ‖Y t - t • w‖ := norm_sub_le _ _
      _ ≤ ‖Y t‖ + gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t := by
        exact add_le_add le_rfl (hsub t ht)
  linarith







theorem gronwall_ne_zero
    {Y Y' Y'' : ℝ → E} {K b : ℝ} {w : E}
    (hK : 0 ≤ K) (hb : 0 < b)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖)
    (h0 : Y 0 = 0) (h0' : Y' 0 = w)
    (hsmall : gronwallBound 0 (max K 1) (K * (b * ‖w‖)) b < b * ‖w‖) :
    Y b ≠ 0 := by
  intro hYb
  have h := gronwall_sub_linear hK hb.le hcY hcY' hdY hdY' hbound h0 h0' b
    ⟨hb.le, le_rfl⟩
  rw [hYb, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hb] at h
  exact absurd h (not_le.mpr hsmall)

end DifferentialGeometry
