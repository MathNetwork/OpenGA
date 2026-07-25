import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.Compact

set_option autoImplicit false










namespace DifferentialGeometry.Analysis.ODE

open Filter Metric Set Topology



theorem exists_first_hit_Icc
    {f : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (ha : f a < r)
    (hcross : ∃ t ∈ Icc a b, r ≤ f t) :
    ∃ τ ∈ Icc a b, f τ = r ∧ ∀ s ∈ Icc a τ, f s ≤ r := by
  have haIcc : a ∈ Icc a b := left_mem_Icc.mpr hab
  let S : Set ℝ := {t ∈ Icc a b | r ≤ f t}
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_Icc.isClosed_le continuousOn_const hf
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed (fun _ ht => ht.1)
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hrt⟩ := hcross
    exact ⟨t, ht, hrt⟩
  obtain ⟨τ, hτS, hτmin⟩ :=
    hScompact.exists_isMinOn hSne continuousOn_id
  have hτeq : f τ = r := by
    apply le_antisymm
    · by_contra hnot
      have hrτ : r < f τ := lt_of_not_ge hnot
      have hfτ : ContinuousOn f (Icc a τ) :=
        hf.mono (fun _ ht => ⟨haIcc.1.trans ht.1, ht.2.trans hτS.1.2⟩)
      obtain ⟨u, hu, hfu⟩ :=
        intermediate_value_Icc hτS.1.1 hfτ ⟨ha.le, hrτ.le⟩
      have hu_ne : u ≠ τ := by
        intro hut
        subst u
        exact (ne_of_gt hrτ) hfu
      have hu_lt : u < τ := lt_of_le_of_ne hu.2 hu_ne
      have huS : u ∈ S :=
        ⟨⟨hu.1, hu.2.trans hτS.1.2⟩, hfu.symm.le⟩
      exact (not_le_of_gt hu_lt) (hτmin huS)
    · exact hτS.2
  refine ⟨τ, hτS.1, hτeq, ?_⟩
  intro s hs
  by_contra hnot
  have hrs : r < f s := lt_of_not_ge hnot
  have hsS : s ∈ S :=
    ⟨⟨hs.1, hs.2.trans hτS.1.2⟩, hrs.le⟩
  have hτs : τ ≤ s := hτmin hsS
  have hst : s = τ := le_antisymm hs.2 hτs
  subst s
  exact (not_lt_of_ge hτeq.le) hrs



theorem tendsto_gronwallBound_zero_zero (L T : ℝ) :
    Tendsto
      (fun z : ℝ × ℝ => gronwallBound z.1 L z.2 T)
      (𝓝 (0, 0)) (𝓝 0) := by
  have hcont : Continuous (fun z : ℝ × ℝ => gronwallBound z.1 L z.2 T) := by
    by_cases hL : L = 0
    · subst L
      simp only [gronwallBound_K0]
      fun_prop
    · simp only [gronwallBound_of_K_ne_0 hL]
      fun_prop
  have hzero : ContinuousAt
      (fun z : ℝ × ℝ => gronwallBound z.1 L z.2 T) (0, 0) :=
    hcont.continuousAt
  simpa only [gronwallBound_ε0_δ0] using hzero.tendsto

private theorem exists_pos_gronwallBound_lt
    (L T R : ℝ) (hR : 0 < R) :
    ∃ θ : ℝ, 0 < θ ∧ θ < R ∧ gronwallBound θ L θ T < R := by
  let e : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hePair : Tendsto (fun n => (e n, e n)) atTop (𝓝 (0, 0)) :=
    he.prodMk_nhds he
  have hbound : Tendsto (fun n => gronwallBound (e n) L (e n) T) atTop (𝓝 0) :=
    (tendsto_gronwallBound_zero_zero L T).comp hePair
  have hev :=
    (Metric.tendsto_nhds.mp hbound R hR).and
      (Metric.tendsto_nhds.mp he R hR)
  obtain ⟨n, hnBound, hnSmall⟩ := hev.exists
  have hen : 0 < e n := by
    dsimp [e]
    positivity
  refine ⟨e n, hen, ?_, ?_⟩
  · simpa [Real.dist_eq, abs_of_pos hen] using hnSmall
  · exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hnBound)




theorem integralCurve_tendstoUniformlyOn_of_limit_tube
    {P X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set P} {t₀ t₁ r : ℝ}
    (ht₀₁ : t₀ ≤ t₁)
    (hr : 0 < r)
    {v : ℕ → ℝ → X → X}
    {vInf : ℝ → X → X}
    {γ : ℕ → P → ℝ → X}
    {γInf : P → ℝ → X}
    (hγ :
      ∀ n p, p ∈ K →
        IsIntegralCurveOn (γ n p) (v n) (Icc t₀ t₁))
    (hγInf :
      ∀ p, p ∈ K →
        IsIntegralCurveOn (γInf p) vInf (Icc t₀ t₁))
    (hinit :
      TendstoUniformlyOn
        (fun n p => γ n p t₀)
        (fun p => γInf p t₀)
        atTop K)
    (hfield :
      TendstoUniformlyOn
        (fun n (q : P × ℝ) => v n q.2 (γInf q.1 q.2))
        (fun q : P × ℝ => vInf q.2 (γInf q.1 q.2))
        atTop (K ×ˢ Icc t₀ t₁))
    (hLip :
      ∃ L : NNReal, ∀ᶠ n in atTop,
        ∀ p ∈ K, ∀ t ∈ Ico t₀ t₁,
          LipschitzOnWith L (v n t)
            (closedBall (γInf p t) r)) :
    TendstoUniformlyOn
      (fun n (q : P × ℝ) => γ n q.1 q.2)
      (fun q : P × ℝ => γInf q.1 q.2)
      atTop (K ×ˢ Icc t₀ t₁) := by
  rw [Metric.tendstoUniformlyOn_iff] at hinit hfield ⊢
  intro ε hε
  let R : ℝ := min r ε
  have hR : 0 < R := lt_min hr hε
  obtain ⟨L, hLip⟩ := hLip
  obtain ⟨θ, hθ, hθR, hgb⟩ :=
    exists_pos_gronwallBound_lt (L : ℝ) (t₁ - t₀) R hR
  filter_upwards [hinit θ hθ, hfield θ hθ, hLip] with n hnInit hnField hnLip
  intro q hq
  obtain ⟨hp, ht⟩ := hq
  let d : ℝ → ℝ := fun t => dist (γ n q.1 t) (γInf q.1 t)
  have hstageCont : ContinuousOn (γ n q.1) (Icc t₀ t₁) :=
    (hγ n q.1 hp).continuousOn
  have hlimitCont : ContinuousOn (γInf q.1) (Icc t₀ t₁) :=
    (hγInf q.1 hp).continuousOn
  have hdCont : ContinuousOn d (Icc t₀ t₁) := by
    dsimp [d]
    exact continuous_dist.comp_continuousOn (hstageCont.prodMk hlimitCont)
  have hdInit : d t₀ < R := by
    dsimp [d]
    rw [dist_comm]
    exact (hnInit q.1 hp).trans hθR
  have hdLt : ∀ t ∈ Icc t₀ t₁, d t < R := by
    intro t ht'
    by_contra hnot
    have hcross : ∃ s ∈ Icc t₀ t₁, R ≤ d s :=
      ⟨t, ht', le_of_not_gt hnot⟩
    obtain ⟨τ, hτ, hτeq, hτbefore⟩ :=
      exists_first_hit_Icc ht₀₁ hdCont hdInit hcross
    have hstageContτ : ContinuousOn (γ n q.1) (Icc t₀ τ) :=
      hstageCont.mono (fun _ hs => ⟨hs.1, hs.2.trans hτ.2⟩)
    have hlimitContτ : ContinuousOn (γInf q.1) (Icc t₀ τ) :=
      hlimitCont.mono (fun _ hs => ⟨hs.1, hs.2.trans hτ.2⟩)
    have hLipτ : ∀ s ∈ Ico t₀ τ,
        LipschitzOnWith L (v n s) (closedBall (γInf q.1 s) r) := by
      intro s hs
      exact hnLip q.1 hp s ⟨hs.1, hs.2.trans_le hτ.2⟩
    have hstageDeriv : ∀ s ∈ Ico t₀ τ,
        HasDerivWithinAt (γ n q.1) (v n s (γ n q.1 s)) (Ici s) s := by
      intro s hs
      have hsFull : s ∈ Ico t₀ t₁ := ⟨hs.1, hs.2.trans_le hτ.2⟩
      exact
        (hγ n q.1 hp s (Ico_subset_Icc_self hsFull)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hsFull)
    have hlimitDeriv : ∀ s ∈ Ico t₀ τ,
        HasDerivWithinAt (γInf q.1) (vInf s (γInf q.1 s)) (Ici s) s := by
      intro s hs
      have hsFull : s ∈ Ico t₀ t₁ := ⟨hs.1, hs.2.trans_le hτ.2⟩
      exact
        (hγInf q.1 hp s (Ico_subset_Icc_self hsFull)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hsFull)
    have hstageBound : ∀ s ∈ Ico t₀ τ,
        dist (v n s (γ n q.1 s)) (v n s (γ n q.1 s)) ≤ 0 := by
      intro s hs
      simp only [dist_self, le_refl]
    have hstageMem : ∀ s ∈ Ico t₀ τ,
        γ n q.1 s ∈ closedBall (γInf q.1 s) r := by
      intro s hs
      rw [mem_closedBall]
      exact (hτbefore s (Ico_subset_Icc_self hs)).trans (min_le_left r ε)
    have hlimitBound : ∀ s ∈ Ico t₀ τ,
        dist (vInf s (γInf q.1 s)) (v n s (γInf q.1 s)) ≤ θ := by
      intro s hs
      exact (hnField (q.1, s) ⟨hp, ⟨hs.1, (hs.2.trans_le hτ.2).le⟩⟩).le
    have hlimitMem : ∀ s ∈ Ico t₀ τ,
        γInf q.1 s ∈ closedBall (γInf q.1 s) r := by
      intro s hs
      simp only [mem_closedBall, dist_self]
      exact hr.le
    have hinitial : dist (γ n q.1 t₀) (γInf q.1 t₀) ≤ θ := by
      rw [dist_comm]
      exact (hnInit q.1 hp).le
    have hcompare :=
      dist_le_of_approx_trajectories_ODE_of_mem
        (v := v n) (s := fun s => closedBall (γInf q.1 s) r)
        (K := L) (f := γ n q.1) (g := γInf q.1)
        (f' := fun s => v n s (γ n q.1 s))
        (g' := fun s => vInf s (γInf q.1 s))
        (a := t₀) (b := τ) (εf := 0) (εg := θ) (δ := θ)
        hLipτ hstageContτ hstageDeriv hstageBound hstageMem
        hlimitContτ hlimitDeriv hlimitBound hlimitMem hinitial τ ⟨hτ.1, le_rfl⟩
    have hcompare' : d τ ≤ gronwallBound θ (L : ℝ) θ (τ - t₀) := by
      simpa only [zero_add, d] using hcompare
    have htime : τ - t₀ ≤ t₁ - t₀ := sub_le_sub_right hτ.2 t₀
    have hmono : gronwallBound θ (L : ℝ) θ (τ - t₀) ≤
        gronwallBound θ (L : ℝ) θ (t₁ - t₀) :=
      gronwallBound_mono hθ.le hθ.le L.coe_nonneg htime
    have : R < R := calc
      R = d τ := hτeq.symm
      _ ≤ gronwallBound θ (L : ℝ) θ (τ - t₀) := hcompare'
      _ ≤ gronwallBound θ (L : ℝ) θ (t₁ - t₀) := hmono
      _ < R := hgb
    exact (lt_irrefl R) this
  have hfinal := hdLt q.2 ht
  calc
    dist (γInf q.1 q.2) (γ n q.1 q.2) = d q.2 := by
      simp only [d, dist_comm]
    _ < R := hfinal
    _ ≤ ε := min_le_right r ε

end DifferentialGeometry.Analysis.ODE
