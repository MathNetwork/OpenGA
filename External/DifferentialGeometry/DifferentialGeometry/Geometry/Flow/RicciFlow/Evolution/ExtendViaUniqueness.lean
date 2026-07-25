import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds

set_option autoImplicit false
set_option linter.style.longLine false



























noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness









variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]















theorem ricci_flow_unif_existence (gBase : SmoothRiemannianMetric I M) :
    ∀ Λ : ℝ, 1 ≤ Λ → ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        (∀ x : M, ∀ v : TangentSpace I x,
          Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧ g₀.inner x v v ≤ Λ * gBase.inner x v v) →
        (∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Set.univ a g₀ gBase Λ) →
        ∃ rr : ℝ → SmoothRiemannianMetric I M, rr 0 = g₀ ∧
          (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
              (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
              (Set.Ioo (0 : ℝ) τ₀ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
          (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
            ContinuousOn
              (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
              (Set.Ico (0 : ℝ) τ₀ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
          (∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ x : M, ∀ v w : TangentSpace I x,
            HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
              ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Set.Ici 0) t) := by
  sorry










theorem ricci_flow_interior_restart
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (_hαω : α < omega)
    (hell : ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ t₁ ∈ Set.Ico α omega, ∀ s ∈ Set.Ico t₁ omega,
      ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (g_fam α).inner x v v ≤ (g_fam s).inner x v v ∧
          (g_fam s).inner x v v ≤ Λ * (g_fam α).inner x v v)
    (hcov : ∃ C : ℝ, 1 ≤ C ∧ ∃ t₂ ∈ Set.Ico α omega, ∀ s ∈ Set.Ico t₂ omega,
      ∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Set.univ a (g_fam s) (g_fam α) C) :
    ∃ t_star : ℝ, t_star ∈ Set.Ico α omega ∧ ∃ TT : ℝ, omega < t_star + TT ∧
      ∃ rr : ℝ → SmoothRiemannianMetric I M, rr 0 = g_fam t_star ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
            (Set.Ioo (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContinuousOn
            (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) TT, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
            ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Set.Ici 0) t) := by

  have hbox := ricci_flow_unif_existence (I := I) (g_fam α)
  obtain ⟨Λ₁, hΛ₁, t₁, ht₁, hell'⟩ := hell
  obtain ⟨Λ₂, hΛ₂, t₂, ht₂, hcov'⟩ := hcov

  set Λ : ℝ := max Λ₁ Λ₂ with hΛdef
  have hΛ₁le : Λ₁ ≤ Λ := by rw [hΛdef]; exact le_max_left _ _
  have hΛ₂le : Λ₂ ≤ Λ := by rw [hΛdef]; exact le_max_right _ _
  have hΛ : 1 ≤ Λ := le_trans hΛ₁ hΛ₁le
  have hΛ₁pos : 0 < Λ₁ := lt_of_lt_of_le zero_lt_one hΛ₁
  obtain ⟨τ₀, hτ₀, hexist⟩ := hbox Λ hΛ

  set t_star : ℝ := max (max t₁ t₂) (omega - τ₀ / 2) with hts_def
  have ht1_le : t₁ ≤ t_star := le_trans (le_max_left t₁ t₂) (le_max_left _ _)
  have ht2_le : t₂ ≤ t_star := le_trans (le_max_right t₁ t₂) (le_max_left _ _)
  have hstar_lt : t_star < omega := max_lt (max_lt ht₁.2 ht₂.2) (by linarith)
  have hstar_mem_αω : t_star ∈ Set.Ico α omega := ⟨le_trans ht₁.1 ht1_le, hstar_lt⟩
  have hstar_mem_1 : t_star ∈ Set.Ico t₁ omega := ⟨ht1_le, hstar_lt⟩
  have hstar_mem_2 : t_star ∈ Set.Ico t₂ omega := ⟨ht2_le, hstar_lt⟩
  have hreach : omega < t_star + τ₀ := by
    have hge : omega - τ₀ / 2 ≤ t_star := by rw [hts_def]; exact le_max_right _ _
    linarith

  have hell_star : ∀ x : M, ∀ v : TangentSpace I x,
      Λ⁻¹ * (g_fam α).inner x v v ≤ (g_fam t_star).inner x v v ∧
        (g_fam t_star).inner x v v ≤ Λ * (g_fam α).inner x v v := by
    intro x v
    have hA : 0 ≤ (g_fam α).inner x v v := by
      rcases eq_or_ne v 0 with rfl | hv
      · rw [((g_fam α).inner x).map_zero, ContinuousLinearMap.zero_apply]
      · exact ((g_fam α).pos x v hv).le
    obtain ⟨h1, h2⟩ := hell' t_star hstar_mem_1 x v
    exact ⟨le_trans (by gcongr) h1, le_trans h2 (by gcongr)⟩
  have hcov_star : ∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn Set.univ a (g_fam t_star) (g_fam α) Λ := by
    intro a ha x hx
    exact ((hcov' t_star hstar_mem_2 a ha) x hx).trans hΛ₂le

  obtain ⟨rr, hrr0, hrrS, hrrC, hrrP⟩ := hexist (g_fam t_star) hell_star hcov_star
  exact ⟨t_star, hstar_mem_αω, τ₀, hreach, rr, hrr0, hrrS, hrrC, hrrP⟩











theorem ricci_flow_forward_unique
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Set.Ici a) t)
    (h2pde : ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Set.Ici a) t)
    (h0 : g₁ a = g₂ a) :
    ∀ t ∈ Set.Ico a b, g₁ t = g₂ t := by
  sorry








omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem extend_construction_of_restart
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (_hαω : α < omega)
    (hleft : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici α) t)
    (hsmooth_left : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ioo α omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont_left : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ico α omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {t_star TT : ℝ} (ht1 : α ≤ t_star) (ht2 : t_star < omega) (hreach : omega < t_star + TT)
    (rr : ℝ → SmoothRiemannianMetric I M)
    (hrr_smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hrr_cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hrr_pde : ∀ t ∈ Set.Ico (0 : ℝ) TT, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Set.Ici 0) t)
    (hagree_overlap : ∀ s ∈ Set.Ico t_star omega, rr (s - t_star) = g_fam s) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ g_ext : ℝ → SmoothRiemannianMetric I M,
      (∀ s : ℝ, s < omega → g_ext s = g_fam s) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
          (Set.Ioo α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
          (Set.Ico α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico α (omega + ε), ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_ext s).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (g_ext t) x v w) (Set.Ici α) t) := by
  set ε : ℝ := t_star + TT - omega with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hωε : omega + ε = t_star + TT := by rw [hε_def]; ring
  set r : ℝ → SmoothRiemannianMetric I M := fun u => rr (u + (omega - t_star)) with hr_def
  set g_ext : ℝ → SmoothRiemannianMetric I M := gluedFamily (I := I) g_fam r omega with hgext_def

  have hext_eq_r : ∀ s : ℝ, t_star ≤ s → g_ext s = rr (s - t_star) := by
    intro s hs
    by_cases hso : s < omega
    · rw [hgext_def, gluedFamily_of_lt (I := I) g_fam r omega hso]
      exact (hagree_overlap s ⟨hs, hso⟩).symm
    · rw [hgext_def, gluedFamily_of_ge (I := I) g_fam r omega (not_lt.mp hso)]
      simp only [hr_def]
      congr 1
      ring

  have hagree : ∀ s : ℝ, s < omega → g_ext s = g_fam s := by
    intro s hs; rw [hgext_def]; exact gluedFamily_of_lt (I := I) g_fam r omega hs

  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => ((p.1 - t_star, p.2) : ℝ × M)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  refine ⟨ε, hε, g_ext, hagree, ?_, ?_, ?_⟩
  ·
    intro x₀ i j
    apply contMDiffOn_of_locally_contMDiffOn
    intro p hp
    by_cases hpo : p.1 < omega
    · refine ⟨Set.Ioo α omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet,
        isOpen_Ioo.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet,
        ⟨⟨hp.1.1, hpo⟩, hp.2⟩, ?_⟩
      refine ((hsmooth_left x₀ i j).mono Set.inter_subset_right).congr ?_
      intro q hq
      rw [hagree q.1 hq.2.1.2]
    · rw [not_lt] at hpo
      refine ⟨Set.Ioo t_star (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet,
        isOpen_Ioo.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet,
        ⟨⟨lt_of_lt_of_le ht2 hpo, hp.1.2⟩, hp.2⟩, ?_⟩
      have hmaps : Set.MapsTo (fun q : ℝ × M => ((q.1 - t_star, q.2) : ℝ × M))
          (Set.Ioo t_star (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
          (Set.Ioo (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
        intro q hq
        exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2, hωε]⟩, hq.2⟩
      have hcomp :
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun q : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr (q.1 - t_star)) x₀ q.2 i j)
            (Set.Ioo t_star (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
        (hrr_smooth x₀ i j).comp hshift.contMDiffOn hmaps
      refine (hcomp.mono Set.inter_subset_right).congr ?_
      intro q hq
      rw [hext_eq_r q.1 (le_of_lt hq.2.1.1)]
  ·
    intro x₀ i j
    set B := (trivializationAt E (TangentSpace I) x₀).baseSet with hB
    set m : ℝ := (t_star + omega) / 2 with hm
    have hm1 : t_star < m := by rw [hm]; linarith
    have hm2 : m < omega := by rw [hm]; linarith
    have hP1 : ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
        (Set.Icc α m ×ˢ B) := by
      refine ((hcont_left x₀ i j).mono ?_).congr ?_
      · intro q hq; exact ⟨⟨hq.1.1, lt_of_le_of_lt hq.1.2 hm2⟩, hq.2⟩
      · intro q hq
        exact congrArg (fun mm : SmoothRiemannianMetric I M =>
          Integral.Measure.chartGramMatrix (I := I) mm x₀ q.2 i j)
          (hagree q.1 (lt_of_le_of_lt hq.1.2 hm2))
    have hP2 : ContinuousOn
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
        (Set.Ico m (omega + ε) ×ˢ B) := by
      have hmapsc : Set.MapsTo (fun q : ℝ × M => ((q.1 - t_star, q.2) : ℝ × M))
          (Set.Ico m (omega + ε) ×ˢ B) (Set.Ico (0 : ℝ) TT ×ˢ B) := by
        intro q hq
        exact ⟨⟨by linarith [hq.1.1, hm1], by linarith [hq.1.2, hωε]⟩, hq.2⟩
      refine ((hrr_cont x₀ i j).comp (Continuous.continuousOn ?_) hmapsc).congr ?_
      · exact (continuous_fst.sub continuous_const).prodMk continuous_snd
      · intro q hq
        simp only [Function.comp_apply]
        rw [hext_eq_r q.1 (le_of_lt (lt_of_lt_of_le hm1 hq.1.1))]
    have hs_eq : Set.Ico α (omega + ε) ×ˢ B = (Set.Icc α m ×ˢ B) ∪ (Set.Ico m (omega + ε) ×ˢ B) := by
      ext q
      simp only [Set.mem_prod, Set.mem_union, Set.mem_Ico, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hq1, hq2⟩, hq3⟩
        rcases le_or_gt q.1 m with h | h
        · exact Or.inl ⟨⟨hq1, h⟩, hq3⟩
        · exact Or.inr ⟨⟨le_of_lt h, hq2⟩, hq3⟩
      · rintro (⟨⟨hq1, hq2⟩, hq3⟩ | ⟨⟨hq1, hq2⟩, hq3⟩)
        · exact ⟨⟨hq1, lt_of_le_of_lt hq2 (by linarith)⟩, hq3⟩
        · exact ⟨⟨le_trans (le_of_lt (lt_of_le_of_lt ht1 hm1)) hq1, hq2⟩, hq3⟩
    intro p hp
    have hp1 := hp.1
    have hp2 := hp.2
    rw [hs_eq]
    apply ContinuousWithinAt.union
    · by_cases h1 : p.1 ≤ m
      · exact hP1 p ⟨⟨hp1.1, h1⟩, hp2⟩
      · rw [not_le] at h1
        apply continuousWithinAt_of_notMem_closure
        rw [closure_prod_eq, isClosed_Icc.closure_eq]
        rintro ⟨hc1, _⟩
        exact absurd hc1.2 (not_le.mpr h1)
    · by_cases h2 : m ≤ p.1
      · exact hP2 p ⟨⟨h2, hp1.2⟩, hp2⟩
      · rw [not_le] at h2
        apply continuousWithinAt_of_notMem_closure
        rw [closure_prod_eq]
        rintro ⟨hc1, _⟩
        exact absurd (closure_minimal Set.Ico_subset_Icc_self isClosed_Icc hc1).1 (not_le.mpr h2)
  ·
    intro t ht x v w
    by_cases hto : t < omega
    · have hfun : (fun s : ℝ => (g_ext s).inner x v w) =ᶠ[𝓝[Set.Ici α] t]
          (fun s : ℝ => (g_fam s).inner x v w) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hto)] with s hs
        rw [hagree s hs]
      rw [show ricciTensor (I := I) (g_ext t) x v w = ricciTensor (I := I) (g_fam t) x v w from by
        rw [hagree t hto]]
      exact (hleft t ⟨ht.1, hto⟩ x v w).congr_of_eventuallyEq hfun (by rw [hagree t hto])
    · rw [not_lt] at hto
      have htts_pos : 0 < t - t_star := by linarith
      have htts_mem : t - t_star ∈ Set.Ico (0 : ℝ) TT :=
        ⟨le_of_lt htts_pos, by linarith [ht.2, hωε]⟩
      have hd0 : HasDerivAt (fun u : ℝ => (rr u).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (rr (t - t_star)) x v w) (t - t_star) :=
        (hrr_pde (t - t_star) htts_mem x v w).hasDerivAt (Ici_mem_nhds htts_pos)
      have hg : HasDerivAt (fun s : ℝ => s - t_star) 1 t := (hasDerivAt_id t).sub_const t_star
      have hcomp : HasDerivAt (fun s : ℝ => (rr (s - t_star)).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (rr (t - t_star)) x v w) t := by
        have h := hd0.comp t hg
        simpa using h
      have hext_t : g_ext t = rr (t - t_star) := hext_eq_r t (by linarith)
      rw [show ricciTensor (I := I) (g_ext t) x v w
          = ricciTensor (I := I) (rr (t - t_star)) x v w from by rw [hext_t]]
      refine hcomp.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show t_star < t by linarith))]
          with s hs
        rw [hext_eq_r s (le_of_lt hs)]
      · rw [hext_t]




private theorem expBounds_of_logDiff {fa fb R : ℝ}
    (hfa : 0 < fa) (hfb : 0 < fb) (hlog : |Real.log fb - Real.log fa| ≤ R) :
    Real.exp (-R) * fa ≤ fb ∧ fb ≤ Real.exp R * fa := by
  have hlow : -R ≤ Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhigh : Real.log fb - Real.log fa ≤ R := (abs_le.mp hlog).2
  refine ⟨?_, ?_⟩
  · have hlog_ratio : -R ≤ Real.log (fb / fa) := by
      rw [Real.log_div hfb.ne' hfa.ne']; exact hlow
    have hratio_lower : Real.exp (-R) ≤ fb / fa :=
      (Real.le_log_iff_exp_le (div_pos hfb hfa)).mp hlog_ratio
    calc Real.exp (-R) * fa ≤ (fb / fa) * fa :=
          mul_le_mul_of_nonneg_right hratio_lower hfa.le
      _ = fb := by field_simp
  · have hlog_ratio : Real.log (fb / fa) ≤ R := by
      rw [Real.log_div hfb.ne' hfa.ne']; exact hhigh
    have hratio_upper : fb / fa ≤ Real.exp R :=
      (Real.log_le_iff_le_exp (div_pos hfb hfa)).mp hlog_ratio
    calc fb = (fb / fa) * fa := by field_simp
      _ ≤ Real.exp R * fa := mul_le_mul_of_nonneg_right hratio_upper hfa.le








omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricEquiv_of_ricBound
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (hαω : α < omega)
    {K : ℝ} (hK : 0 ≤ K)
    (hpde : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici α) t)
    (hric : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (g_fam t) x v v| ≤ K * (g_fam t).inner x v v) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ t₁ ∈ Set.Ico α omega, ∀ s ∈ Set.Ico t₁ omega,
      ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (g_fam α).inner x v v ≤ (g_fam s).inner x v v ∧
          (g_fam s).inner x v v ≤ Λ * (g_fam α).inner x v v := by
  have hexp_arg : 0 ≤ 2 * K * (omega - α) :=
    mul_nonneg (mul_nonneg (by norm_num) hK) (by linarith)
  refine ⟨Real.exp (2 * K * (omega - α)), ?_, α, ⟨le_refl α, hαω⟩, ?_⟩
  · rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hexp_arg
  intro s hs x v
  rcases eq_or_ne v 0 with rfl | hv
  · have h0α : (g_fam α).inner x (0 : TangentSpace I x) 0 = 0 := by
      rw [((g_fam α).inner x).map_zero, ContinuousLinearMap.zero_apply]
    have h0s : (g_fam s).inner x (0 : TangentSpace I x) 0 = 0 := by
      rw [((g_fam s).inner x).map_zero, ContinuousLinearMap.zero_apply]
    rw [h0α, h0s, mul_zero, mul_zero]
    exact ⟨le_refl 0, le_refl 0⟩

  have hpos : ∀ t : ℝ, 0 < (g_fam t).inner x v v := fun t => (g_fam t).pos x v hv
  have hs_lt : s < omega := hs.2
  have hα_le_s : α ≤ s := hs.1
  have hsub : Set.Icc α s ⊆ Set.Ico α omega := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hs_lt⟩

  have hderiv : ∀ y ∈ Set.Icc α s,
      HasDerivWithinAt (fun t : ℝ => Real.log ((g_fam t).inner x v v))
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam y) x v v / (g_fam y).inner x v v)
        (Set.Icc α s) y := by
    intro y hy
    have hd : HasDerivWithinAt (fun t : ℝ => (g_fam t).inner x v v)
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam y) x v v) (Set.Ici α) y := hpde y (hsub hy) x v v
    exact (hd.mono fun z hz => hz.1).log (ne_of_gt (hpos y))
  have hbound : ∀ y ∈ Set.Icc α s,
      ‖(-2 : ℝ) * ricciTensor (I := I) (g_fam y) x v v / (g_fam y).inner x v v‖ ≤ 2 * K := by
    intro y hy
    have hfy : 0 < (g_fam y).inner x v v := hpos y
    have hric_y := hric y (hsub hy) x v
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hfy, div_le_iff₀ hfy]
    have habs2 : |(-2 : ℝ) * ricciTensor (I := I) (g_fam y) x v v|
        = 2 * |ricciTensor (I := I) (g_fam y) x v v| := by rw [abs_mul]; norm_num
    rw [habs2]
    nlinarith [hric_y]
  have hmvt := (convex_Icc α s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr hα_le_s) (Set.right_mem_Icc.mpr hα_le_s)
  have hlogdiff : |Real.log ((g_fam s).inner x v v) - Real.log ((g_fam α).inner x v v)|
      ≤ 2 * K * (s - α) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ s - α by linarith)] at hmvt
    exact hmvt
  obtain ⟨hlo, hhi⟩ := expBounds_of_logDiff (hpos α) (hpos s) hlogdiff
  have hfα_nn : 0 ≤ (g_fam α).inner x v v := (hpos α).le
  have hle_exp : 2 * K * (s - α) ≤ 2 * K * (omega - α) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hK)
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_neg]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hle_exp)) hfα_nn) hlo
  · exact le_trans hhi (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle_exp) hfα_nn)

end DifferentialGeometry.PDE.RicciFlow

end
