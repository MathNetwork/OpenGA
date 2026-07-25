import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSFirstDerivativeBound









namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma prod_sub_bnd
    {a₁ a₂ b₁ b₂ A B Cₐ Cb J : ℝ}
    (hA_nn : 0 ≤ A) (hCa_nn : 0 ≤ Cₐ) (hJ_nn : 0 ≤ J)
    (ha₂ : |a₂| ≤ A) (hb₁ : |b₁| ≤ B)
    (ha : |a₁ - a₂| ≤ Cₐ * J) (hb : |b₁ - b₂| ≤ Cb * J) :
    |a₁ * b₁ - a₂ * b₂| ≤ (Cₐ * B + A * Cb) * J := by
  rw [show a₁ * b₁ - a₂ * b₂ = (a₁ - a₂) * b₁ + a₂ * (b₁ - b₂) by ring]
  calc
    |(a₁ - a₂) * b₁ + a₂ * (b₁ - b₂)| ≤
        |(a₁ - a₂) * b₁| + |a₂ * (b₁ - b₂)| := abs_add_le _ _
    _ = |a₁ - a₂| * |b₁| + |a₂| * |b₁ - b₂| := by rw [abs_mul, abs_mul]
    _ ≤ (Cₐ * J) * B + A * (Cb * J) := add_le_add
      (mul_le_mul ha hb₁ (abs_nonneg _) (mul_nonneg hCa_nn hJ_nn))
      (mul_le_mul ha₂ hb (abs_nonneg _) hA_nn)
    _ = (Cₐ * B + A * Cb) * J := by ring

private lemma abs_sum2_bnd
    {n : ℕ} (F : Fin n → Fin n → ℝ) {C : ℝ}
    (hF : ∀ a b, |F a b| ≤ C) :
    |∑ a, ∑ b, F a b| ≤ (n : ℝ) ^ 2 * C := by
  classical
  calc
    |∑ a, ∑ b, F a b| ≤ ∑ a, |∑ b, F a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, ∑ _b : Fin n, C := by
      refine Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun b _ => hF a b
    _ = (n : ℝ) ^ 2 * C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private lemma abs_sum_bnd
    {n : ℕ} (F : Fin n → ℝ) {C : ℝ} (hF : ∀ a, |F a| ≤ C) :
    |∑ a, F a| ≤ (n : ℝ) * C := by
  classical
  calc
    |∑ a, F a| ≤ ∑ a, |F a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, C := Finset.sum_le_sum fun a _ => hF a
    _ = (n : ℝ) * C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma sum_pair_sub_bnd
    {n : ℕ} (A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Fin n → ℝ)
    {A B C D Cₐ Cb Cc Cd J : ℝ}
    (hA_nn : 0 ≤ A) (hCa_nn : 0 ≤ Cₐ) (hC_nn : 0 ≤ C)
    (hCc_nn : 0 ≤ Cc) (hJ_nn : 0 ≤ J)
    (hA₂ : ∀ k, |A₂ k| ≤ A) (hB₁ : ∀ k, |B₁ k| ≤ B)
    (hC₂ : ∀ k, |C₂ k| ≤ C) (hD₁ : ∀ k, |D₁ k| ≤ D)
    (hA : ∀ k, |A₁ k - A₂ k| ≤ Cₐ * J)
    (hB : ∀ k, |B₁ k - B₂ k| ≤ Cb * J)
    (hC : ∀ k, |C₁ k - C₂ k| ≤ Cc * J)
    (hD : ∀ k, |D₁ k - D₂ k| ≤ Cd * J) :
    |Finset.univ.sum (fun k : Fin n => A₁ k * B₁ k + C₁ k * D₁ k) -
      Finset.univ.sum (fun k : Fin n => A₂ k * B₂ k + C₂ k * D₂ k)| ≤
      (n : ℝ) * ((Cₐ * B + A * Cb) + (Cc * D + C * Cd)) * J := by
  classical
  rw [← Finset.sum_sub_distrib]
  let F : Fin n → ℝ := fun k =>
    (A₁ k * B₁ k + C₁ k * D₁ k) - (A₂ k * B₂ k + C₂ k * D₂ k)
  change |∑ k : Fin n, F k| ≤
    (n : ℝ) * ((Cₐ * B + A * Cb) + (Cc * D + C * Cd)) * J
  refine (abs_sum_bnd F (C := ((Cₐ * B + A * Cb) + (Cc * D + C * Cd)) * J) ?_).trans_eq ?_
  · intro k
    dsimp only [F]
    rw [show (A₁ k * B₁ k + C₁ k * D₁ k) - (A₂ k * B₂ k + C₂ k * D₂ k) =
      (A₁ k * B₁ k - A₂ k * B₂ k) + (C₁ k * D₁ k - C₂ k * D₂ k) by ring]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add
      (prod_sub_bnd hA_nn hCa_nn hJ_nn (hA₂ k) (hB₁ k) (hA k) (hB k))
      (prod_sub_bnd hC_nn hCc_nn hJ_nn (hC₂ k) (hD₁ k) (hC k) (hD k))).trans_eq ?_
    ring
  · ring




omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckVFD2_sub
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d m k : Fin (Module.finrank ℝ E))
    {M_b D T P R S C₀ C₁ C₂ G₀ G₁ G₂ : ℝ}
    (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D) (hT_nn : 0 ≤ T)
    (hC₀_nn : 0 ≤ C₀) (hC₁_nn : 0 ≤ C₁) (hC₂_nn : 0 ≤ C₂)
    (hMb₂ : ∀ a b, |chartInvGramOnE (I := I) g₂ α a b y| ≤ M_b)
    (hD₂ : ∀ e a b, |partialDeriv (E := E) e
      (chartInvGramOnE (I := I) g₂ α a b) y| ≤ D)
    (hT₂ : ∀ e r a b, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₂ α a b)) y| ≤ T)
    (hP₁ : ∀ a b, |chartChristoffel (I := I) g₁ α a b k y -
      chartChristoffel (I := I) g_bg α a b k y| ≤ P)
    (hR₁ : ∀ e a b, |partialDeriv (E := E) e
        (chartChristoffel (I := I) g₁ α a b k) y -
      partialDeriv (E := E) e (chartChristoffel (I := I) g_bg α a b k) y| ≤ R)
    (hS₁ : ∀ e r a b, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₁ α a b k)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g_bg α a b k)) y| ≤ S)
    (hInv : ∀ a b, |chartInvGramOnE (I := I) g₁ α a b y -
      chartInvGramOnE (I := I) g₂ α a b y| ≤
        C₀ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hInvD : ∀ e a b, |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) g₁ α a b) y -
      partialDeriv (E := E) e (chartInvGramOnE (I := I) g₂ α a b) y| ≤
        C₁ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hInvD2 : ∀ e r a b, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₁ α a b)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₂ α a b)) y| ≤
        C₂ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓ : ∀ a b q, |chartChristoffel (I := I) g₁ α a b q y -
      chartChristoffel (I := I) g₂ α a b q y| ≤
        G₀ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓD : ∀ e a b q, |partialDeriv (E := E) e
        (chartChristoffel (I := I) g₁ α a b q) y -
      partialDeriv (E := E) e (chartChristoffel (I := I) g₂ α a b q) y| ≤
        G₁ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓD2 : ∀ e r a b q, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₁ α a b q)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₂ α a b q)) y| ≤
        G₂ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y) :
    |partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k)) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k)) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        ((C₂ * P + T * G₀) + 2 * (C₁ * R + D * G₁) + (C₀ * S + M_b * G₂)) *
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  set J : ℝ := metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y with hJ_def
  have hJ_nn : 0 ≤ J := metricJet3_nonneg (I := I) (M := M) g₁ g₂ α y
  let K : ℝ := (C₂ * P + T * G₀) + 2 * (C₁ * R + D * G₁) + (C₀ * S + M_b * G₂)
  rw [partial2_deTurckVF (I := I) g₁ g_bg α d m k hy,
    partial2_deTurckVF (I := I) g₂ g_bg α d m k hy,
    ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  let F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    (partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b)) y *
        (chartChristoffel (I := I) g₁ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y) +
      partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y *
        (partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α a b k) y -
          partialDeriv (E := E) d (chartChristoffel (I := I) g_bg α a b k) y) +
      partialDeriv (E := E) d (chartInvGramOnE (I := I) g₁ α a b) y *
        (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y) +
      chartInvGramOnE (I := I) g₁ α a b y *
        (partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y)) -
    (partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b)) y *
        (chartChristoffel (I := I) g₂ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y) +
      partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y *
        (partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α a b k) y -
          partialDeriv (E := E) d (chartChristoffel (I := I) g_bg α a b k) y) +
      partialDeriv (E := E) d (chartInvGramOnE (I := I) g₂ α a b) y *
        (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y) +
      chartInvGramOnE (I := I) g₂ α a b y *
        (partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y))
  change |∑ a, ∑ b, F a b| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K * J
  refine (abs_sum2_bnd F (C := K * J) ?_).trans_eq ?_
  · intro a b
    dsimp only [F]
    let A₁ : ℝ := partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b)) y *
      (chartChristoffel (I := I) g₁ α a b k y -
        chartChristoffel (I := I) g_bg α a b k y)
    let A₂ : ℝ := partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b)) y *
      (chartChristoffel (I := I) g₂ α a b k y -
        chartChristoffel (I := I) g_bg α a b k y)
    let B₁ : ℝ := partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y *
      (partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α a b k) y -
        partialDeriv (E := E) d (chartChristoffel (I := I) g_bg α a b k) y)
    let B₂ : ℝ := partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y *
      (partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α a b k) y -
        partialDeriv (E := E) d (chartChristoffel (I := I) g_bg α a b k) y)
    let C₁' : ℝ := partialDeriv (E := E) d (chartInvGramOnE (I := I) g₁ α a b) y *
      (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y)
    let C₂' : ℝ := partialDeriv (E := E) d (chartInvGramOnE (I := I) g₂ α a b) y *
      (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y)
    let L₁ : ℝ := chartInvGramOnE (I := I) g₁ α a b y *
      (partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k)) y -
        partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y)
    let L₂ : ℝ := chartInvGramOnE (I := I) g₂ α a b y *
      (partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k)) y -
        partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y)
    change |(A₁ + B₁ + C₁' + L₁) - (A₂ + B₂ + C₂' + L₂)| ≤ K * J
    have hΓ0 : |(chartChristoffel (I := I) g₁ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y) -
        (chartChristoffel (I := I) g₂ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y)| ≤ G₀ * J := by
      rw [show (chartChristoffel (I := I) g₁ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y) -
        (chartChristoffel (I := I) g₂ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y) =
        chartChristoffel (I := I) g₁ α a b k y -
          chartChristoffel (I := I) g₂ α a b k y by ring]
      exact hΓ a b k
    have hΓ1 : ∀ e, |(partialDeriv (E := E) e
            (chartChristoffel (I := I) g₁ α a b k) y -
          partialDeriv (E := E) e (chartChristoffel (I := I) g_bg α a b k) y) -
        (partialDeriv (E := E) e (chartChristoffel (I := I) g₂ α a b k) y -
          partialDeriv (E := E) e (chartChristoffel (I := I) g_bg α a b k) y)| ≤
        G₁ * J := by
      intro e
      rw [show (partialDeriv (E := E) e (chartChristoffel (I := I) g₁ α a b k) y -
          partialDeriv (E := E) e (chartChristoffel (I := I) g_bg α a b k) y) -
        (partialDeriv (E := E) e (chartChristoffel (I := I) g₂ α a b k) y -
          partialDeriv (E := E) e (chartChristoffel (I := I) g_bg α a b k) y) =
        partialDeriv (E := E) e (chartChristoffel (I := I) g₁ α a b k) y -
          partialDeriv (E := E) e (chartChristoffel (I := I) g₂ α a b k) y by ring]
      exact hΓD e a b k
    have hΓ2 : |(partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y) -
        (partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y)| ≤
        G₂ * J := by
      rw [show (partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y) -
        (partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y) =
        partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k)) y -
          partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k)) y by ring]
      exact hΓD2 d m a b k
    have hA : |A₁ - A₂| ≤ (C₂ * P + T * G₀) * J := by
      dsimp only [A₁, A₂]
      exact prod_sub_bnd hT_nn hC₂_nn hJ_nn (hT₂ d m a b) (hP₁ a b)
        (hInvD2 d m a b) hΓ0
    have hB : |B₁ - B₂| ≤ (C₁ * R + D * G₁) * J := by
      dsimp only [B₁, B₂]
      exact prod_sub_bnd hD_nn hC₁_nn hJ_nn (hD₂ m a b) (hR₁ d a b)
        (hInvD m a b) (hΓ1 d)
    have hC : |C₁' - C₂'| ≤ (C₁ * R + D * G₁) * J := by
      dsimp only [C₁', C₂']
      exact prod_sub_bnd hD_nn hC₁_nn hJ_nn (hD₂ d a b) (hR₁ m a b)
        (hInvD d a b) (hΓ1 m)
    have hL : |L₁ - L₂| ≤ (C₀ * S + M_b * G₂) * J := by
      dsimp only [L₁, L₂]
      exact prod_sub_bnd hMb_nn hC₀_nn hJ_nn (hMb₂ a b) (hS₁ d m a b)
        (hInv a b) hΓ2
    rw [show (A₁ + B₁ + C₁' + L₁) - (A₂ + B₂ + C₂' + L₂) =
      (A₁ - A₂) + (B₁ - B₂) + (C₁' - C₂') + (L₁ - L₂) by ring]
    calc
      |(A₁ - A₂) + (B₁ - B₂) + (C₁' - C₂') + (L₁ - L₂)| ≤
          ((|A₁ - A₂| + |B₁ - B₂|) + |C₁' - C₂'|) + |L₁ - L₂| := by
        exact (abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (((C₂ * P + T * G₀) * J + (C₁ * R + D * G₁) * J) +
          (C₁ * R + D * G₁) * J) + (C₀ * S + M_b * G₂) * J :=
        add_le_add (add_le_add (add_le_add hA hB) hC) hL
      _ = K * J := by dsimp [K]; ring
  · ring



omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannD_sub
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d i j k l : Fin (Module.finrank ℝ E))
    {CΓ CdΓ G₀ G₁ G₂ : ℝ} (hCdΓ_nn : 0 ≤ CdΓ) (hG₁_nn : 0 ≤ G₁)
    (hΓ₁ : ∀ a b c, |chartChristoffel (I := I) g₁ α a b c y| ≤ CΓ)
    (hΓD₂ : ∀ e a b c, |partialDeriv (E := E) e
      (chartChristoffel (I := I) g₂ α a b c) y| ≤ CdΓ)
    (hΓ : ∀ a b c, |chartChristoffel (I := I) g₁ α a b c y -
      chartChristoffel (I := I) g₂ α a b c y| ≤
        G₀ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓD : ∀ e a b c, |partialDeriv (E := E) e
        (chartChristoffel (I := I) g₁ α a b c) y -
      partialDeriv (E := E) e (chartChristoffel (I := I) g₂ α a b c) y| ≤
        G₁ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓD2 : ∀ e r a b c, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₁ α a b c)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₂ α a b c)) y| ≤
        G₂ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y) :
    |partialDeriv (E := E) d (chartRiemannTensor (I := I) g₁ α i j k l) y -
      partialDeriv (E := E) d (chartRiemannTensor (I := I) g₂ α i j k l) y| ≤
      (2 * G₂ + 4 * (Module.finrank ℝ E : ℝ) * (G₁ * CΓ + CdΓ * G₀)) *
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  set J : ℝ := metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y with hJ_def
  have hJ_nn : 0 ≤ J := metricJet3_nonneg (I := I) (M := M) g₁ g₂ α y
  let K : ℝ := G₁ * CΓ + CdΓ * G₀
  rw [partial_chartRiemann (I := I) g₁ α d i j k l hy,
    partial_chartRiemann (I := I) g₂ α d i j k l hy]
  let A₁ : ℝ := partialDeriv (E := E) d
    (partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k l)) y
  let A₂ : ℝ := partialDeriv (E := E) d
    (partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k l)) y
  let B₁ : ℝ := partialDeriv (E := E) d
    (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j l)) y
  let B₂ : ℝ := partialDeriv (E := E) d
    (partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j l)) y
  let Q₁ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α j q l) y *
          chartChristoffel (I := I) g₁ α i k q y +
        chartChristoffel (I := I) g₁ α j q l y *
          partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i k q) y -
      (partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α k q l) y *
          chartChristoffel (I := I) g₁ α i j q y +
        chartChristoffel (I := I) g₁ α k q l y *
          partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i j q) y))
  let Q₂ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α j q l) y *
          chartChristoffel (I := I) g₂ α i k q y +
        chartChristoffel (I := I) g₂ α j q l y *
          partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i k q) y -
      (partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α k q l) y *
          chartChristoffel (I := I) g₂ α i j q y +
        chartChristoffel (I := I) g₂ α k q l y *
          partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i j q) y))
  change |(A₁ - B₁ + Q₁) - (A₂ - B₂ + Q₂)| ≤ _
  have hQ : |Q₁ - Q₂| ≤ 4 * (Module.finrank ℝ E : ℝ) * K * J := by
    dsimp only [Q₁, Q₂]
    rw [← Finset.sum_sub_distrib]
    let F : Fin (Module.finrank ℝ E) → ℝ := fun q =>
      (partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α j q l) y *
            chartChristoffel (I := I) g₁ α i k q y +
          chartChristoffel (I := I) g₁ α j q l y *
            partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i k q) y -
        (partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α k q l) y *
            chartChristoffel (I := I) g₁ α i j q y +
          chartChristoffel (I := I) g₁ α k q l y *
            partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i j q) y)) -
      (partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α j q l) y *
            chartChristoffel (I := I) g₂ α i k q y +
          chartChristoffel (I := I) g₂ α j q l y *
            partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i k q) y -
        (partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α k q l) y *
            chartChristoffel (I := I) g₂ α i j q y +
          chartChristoffel (I := I) g₂ α k q l y *
            partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i j q) y))
    change |∑ q, F q| ≤ 4 * (Module.finrank ℝ E : ℝ) * K * J
    refine (abs_sum_bnd F (C := 4 * K * J) ?_).trans_eq ?_
    · intro q
      dsimp only [F]
      let U₁ : ℝ := partialDeriv (E := E) d
          (chartChristoffel (I := I) g₁ α j q l) y *
        chartChristoffel (I := I) g₁ α i k q y
      let U₂ : ℝ := partialDeriv (E := E) d
          (chartChristoffel (I := I) g₂ α j q l) y *
        chartChristoffel (I := I) g₂ α i k q y
      let V₁ : ℝ := chartChristoffel (I := I) g₁ α j q l y *
        partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i k q) y
      let V₂ : ℝ := chartChristoffel (I := I) g₂ α j q l y *
        partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i k q) y
      let W₁ : ℝ := partialDeriv (E := E) d
          (chartChristoffel (I := I) g₁ α k q l) y *
        chartChristoffel (I := I) g₁ α i j q y
      let W₂ : ℝ := partialDeriv (E := E) d
          (chartChristoffel (I := I) g₂ α k q l) y *
        chartChristoffel (I := I) g₂ α i j q y
      let Z₁ : ℝ := chartChristoffel (I := I) g₁ α k q l y *
        partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i j q) y
      let Z₂ : ℝ := chartChristoffel (I := I) g₂ α k q l y *
        partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i j q) y
      change |(U₁ + V₁ - (W₁ + Z₁)) - (U₂ + V₂ - (W₂ + Z₂))| ≤ 4 * K * J
      have hU : |U₁ - U₂| ≤ K * J := by
        dsimp only [U₁, U₂]
        exact prod_sub_bnd hCdΓ_nn hG₁_nn hJ_nn (hΓD₂ d j q l) (hΓ₁ i k q)
          (hΓD d j q l) (hΓ i k q)
      have hV : |V₁ - V₂| ≤ K * J := by
        dsimp only [V₁, V₂]
        rw [show chartChristoffel (I := I) g₁ α j q l y *
              partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i k q) y -
            chartChristoffel (I := I) g₂ α j q l y *
              partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i k q) y =
            partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i k q) y *
              chartChristoffel (I := I) g₁ α j q l y -
            partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i k q) y *
              chartChristoffel (I := I) g₂ α j q l y by ring]
        refine (prod_sub_bnd hCdΓ_nn hG₁_nn hJ_nn
          (hΓD₂ d i k q) (hΓ₁ j q l) (hΓD d i k q) (hΓ j q l)).trans_eq ?_
        dsimp [K]
      have hW : |W₁ - W₂| ≤ K * J := by
        dsimp only [W₁, W₂]
        exact prod_sub_bnd hCdΓ_nn hG₁_nn hJ_nn (hΓD₂ d k q l) (hΓ₁ i j q)
          (hΓD d k q l) (hΓ i j q)
      have hZ : |Z₁ - Z₂| ≤ K * J := by
        dsimp only [Z₁, Z₂]
        rw [show chartChristoffel (I := I) g₁ α k q l y *
              partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i j q) y -
            chartChristoffel (I := I) g₂ α k q l y *
              partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i j q) y =
            partialDeriv (E := E) d (chartChristoffel (I := I) g₁ α i j q) y *
              chartChristoffel (I := I) g₁ α k q l y -
            partialDeriv (E := E) d (chartChristoffel (I := I) g₂ α i j q) y *
              chartChristoffel (I := I) g₂ α k q l y by ring]
        refine (prod_sub_bnd hCdΓ_nn hG₁_nn hJ_nn
          (hΓD₂ d i j q) (hΓ₁ k q l) (hΓD d i j q) (hΓ k q l)).trans_eq ?_
        dsimp [K]
      rw [show (U₁ + V₁ - (W₁ + Z₁)) - (U₂ + V₂ - (W₂ + Z₂)) =
        (U₁ - U₂) + (V₁ - V₂) - ((W₁ - W₂) + (Z₁ - Z₂)) by ring]
      calc
        |(U₁ - U₂) + (V₁ - V₂) - ((W₁ - W₂) + (Z₁ - Z₂))| ≤
            (|U₁ - U₂| + |V₁ - V₂|) + (|W₁ - W₂| + |Z₁ - Z₂|) := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
        _ ≤ (K * J + K * J) + (K * J + K * J) :=
          add_le_add (add_le_add hU hV) (add_le_add hW hZ)
        _ = 4 * K * J := by ring
    · ring
  rw [show (A₁ - B₁ + Q₁) - (A₂ - B₂ + Q₂) =
    (A₁ - A₂) - (B₁ - B₂) + (Q₁ - Q₂) by ring]
  calc
    |(A₁ - A₂) - (B₁ - B₂) + (Q₁ - Q₂)| ≤
        (|A₁ - A₂| + |B₁ - B₂|) + |Q₁ - Q₂| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (G₂ * J + G₂ * J) + 4 * (Module.finrank ℝ E : ℝ) * K * J :=
      add_le_add (add_le_add (hΓD2 d j i k l) (hΓD2 d k i j l)) hQ
    _ = (2 * G₂ + 4 * (Module.finrank ℝ E : ℝ) *
        (G₁ * CΓ + CdΓ * G₀)) * J := by
      dsimp [K]
      ring


omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciD_sub
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d i k : Fin (Module.finrank ℝ E))
    {CΓ CdΓ G₀ G₁ G₂ : ℝ} (hCdΓ_nn : 0 ≤ CdΓ) (hG₁_nn : 0 ≤ G₁)
    (hΓ₁ : ∀ a b c, |chartChristoffel (I := I) g₁ α a b c y| ≤ CΓ)
    (hΓD₂ : ∀ e a b c, |partialDeriv (E := E) e
      (chartChristoffel (I := I) g₂ α a b c) y| ≤ CdΓ)
    (hΓ : ∀ a b c, |chartChristoffel (I := I) g₁ α a b c y -
      chartChristoffel (I := I) g₂ α a b c y| ≤
        G₀ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓD : ∀ e a b c, |partialDeriv (E := E) e
        (chartChristoffel (I := I) g₁ α a b c) y -
      partialDeriv (E := E) e (chartChristoffel (I := I) g₂ α a b c) y| ≤
        G₁ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hΓD2 : ∀ e r a b c, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₁ α a b c)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g₂ α a b c)) y| ≤
        G₂ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y) :
    |partialDeriv (E := E) d (chartRicciTensor (I := I) g₁ α i k) y -
      partialDeriv (E := E) d (chartRicciTensor (I := I) g₂ α i k) y| ≤
      (Module.finrank ℝ E : ℝ) *
        (2 * G₂ + 4 * (Module.finrank ℝ E : ℝ) * (G₁ * CΓ + CdΓ * G₀)) *
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [partial_chartRicci (I := I) g₁ α d i k hy,
    partial_chartRicci (I := I) g₂ α d i k hy,
    ← Finset.sum_sub_distrib]
  set J : ℝ := metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y with hJ_def
  let K : ℝ := 2 * G₂ + 4 * (Module.finrank ℝ E : ℝ) * (G₁ * CΓ + CdΓ * G₀)
  let F : Fin (Module.finrank ℝ E) → ℝ := fun j =>
    partialDeriv (E := E) d (chartRiemannTensor (I := I) g₁ α i j k j) y -
      partialDeriv (E := E) d (chartRiemannTensor (I := I) g₂ α i j k j) y
  change |∑ j, F j| ≤ (Module.finrank ℝ E : ℝ) * K * J
  refine (abs_sum_bnd F (C := K * J) ?_).trans_eq ?_
  · intro j
    dsimp only [F, K]
    exact chartRiemannD_sub (I := I) (M := M) g₁ g₂ α hy d i j k j
      hCdΓ_nn hG₁_nn hΓ₁ hΓD₂ hΓ hΓD hΓD2
  · ring



omit [NeZero (Module.finrank ℝ E)] in
theorem chartLieD_sub
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d i j : Fin (Module.finrank ℝ E))
    {Q₀ Q₁ Q₂ V DV D2V W₀ W₁ W₂ : ℝ}
    (hV_nn : 0 ≤ V) (hDV_nn : 0 ≤ DV) (hD2V_nn : 0 ≤ D2V)
    (hW₀_nn : 0 ≤ W₀) (hW₁_nn : 0 ≤ W₁) (hW₂_nn : 0 ≤ W₂)
    (hG₁ : ∀ a b, |chartGramOnE (I := I) g₁ α a b y| ≤ Q₀)
    (hGD₁ : ∀ e a b, |partialDeriv (E := E) e
      (chartGramOnE (I := I) g₁ α a b) y| ≤ Q₁)
    (hGD2₁ : ∀ e r a b, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartGramOnE (I := I) g₁ α a b)) y| ≤ Q₂)
    (hV₂ : ∀ q, |chartDeTurckVFComp (I := I) g₂ g_bg α q y| ≤ V)
    (hVD₂ : ∀ e q, |partialDeriv (E := E) e
      (chartDeTurckVFComp (I := I) g₂ g_bg α q) y| ≤ DV)
    (hVD2₂ : ∀ e r q, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y| ≤ D2V)
    (hVsub : ∀ q, |chartDeTurckVFComp (I := I) g₁ g_bg α q y -
      chartDeTurckVFComp (I := I) g₂ g_bg α q y| ≤
        W₀ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hVDsub : ∀ e q, |partialDeriv (E := E) e
        (chartDeTurckVFComp (I := I) g₁ g_bg α q) y -
      partialDeriv (E := E) e (chartDeTurckVFComp (I := I) g₂ g_bg α q) y| ≤
        W₁ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hVD2sub : ∀ e r q, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y| ≤
        W₂ * metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y) :
    |partialDeriv (E := E) d (chartLieDeTurckComp (I := I) g₁ g_bg α i j) y -
      partialDeriv (E := E) d (chartLieDeTurckComp (I := I) g₂ g_bg α i j) y| ≤
      (Module.finrank ℝ E : ℝ) *
        (((W₁ * Q₁ + DV) + (W₀ * Q₂ + V)) +
          2 * ((W₁ * Q₁ + DV) + (W₂ * Q₀ + D2V))) *
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  set J : ℝ := metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y with hJ_def
  have hJ_nn : 0 ≤ J := metricJet3_nonneg (I := I) (M := M) g₁ g₂ α y
  have hJ₂_le : chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y ≤ J :=
    metricJet2_le_jet3 (I := I) (M := M) g₁ g₂ α y
  have hJ₁_le : chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y ≤ J :=
    (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y).trans hJ₂_le
  have hGram : ∀ a b, |chartGramOnE (I := I) g₁ α a b y -
      chartGramOnE (I := I) g₂ α a b y| ≤ 1 * J := by
    intro a b
    rw [one_mul, chartGramOnE_def, chartGramOnE_def]
    exact (chartGramMatrix_sub_entry_abs_le_gramDiffSup (I := I) (M := M)
      g₁ g₂ α ((extChartAt I α).symm y) a b).trans
        ((chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans hJ₁_le)
  have hGramD : ∀ e a b, |partialDeriv (E := E) e
        (chartGramOnE (I := I) g₁ α a b) y -
      partialDeriv (E := E) e (chartGramOnE (I := I) g₂ α a b) y| ≤ 1 * J := by
    intro e a b
    rw [one_mul]
    exact (partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup
      (I := I) (M := M) g₁ g₂ α y e a b).trans
        ((chartGramPartialDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans hJ₁_le)
  have hGramD2 : ∀ e r a b, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartGramOnE (I := I) g₁ α a b)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartGramOnE (I := I) g₂ α a b)) y| ≤ 1 * J := by
    intro e r a b
    rw [one_mul]
    exact (partialDeriv2_chartGramOnE_sub_abs_le_partial2DiffSup
      (I := I) (M := M) g₁ g₂ α y e r a b).trans
        ((chartGramPartial2DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y).trans hJ₂_le)
  let K_A : ℝ := (W₁ * Q₁ + DV) + (W₀ * Q₂ + V)
  let K_B : ℝ := (W₁ * Q₁ + DV) + (W₂ * Q₀ + D2V)
  rw [partial_chartLie (I := I) g₁ g_bg α d i j hy,
    partial_chartLie (I := I) g₂ g_bg α d i j hy]
  let A₁ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartDeTurckVFComp (I := I) g₁ g_bg α q) y *
        partialDeriv (E := E) q (chartGramOnE (I := I) g₁ α i j) y +
      chartDeTurckVFComp (I := I) g₁ g_bg α q y *
        partialDeriv (E := E) d
          (partialDeriv (E := E) q (chartGramOnE (I := I) g₁ α i j)) y)
  let A₂ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartDeTurckVFComp (I := I) g₂ g_bg α q) y *
        partialDeriv (E := E) q (chartGramOnE (I := I) g₂ α i j) y +
      chartDeTurckVFComp (I := I) g₂ g_bg α q y *
        partialDeriv (E := E) d
          (partialDeriv (E := E) q (chartGramOnE (I := I) g₂ α i j)) y)
  let B₁ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α q j) y *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α q) y +
      chartGramOnE (I := I) g₁ α q j y *
        partialDeriv (E := E) d
          (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y)
  let B₂ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α q j) y *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α q) y +
      chartGramOnE (I := I) g₂ α q j y *
        partialDeriv (E := E) d
          (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y)
  let C₁ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α i q) y *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α q) y +
      chartGramOnE (I := I) g₁ α i q y *
        partialDeriv (E := E) d
          (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y)
  let C₂ : ℝ := ∑ q : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α i q) y *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α q) y +
      chartGramOnE (I := I) g₂ α i q y *
        partialDeriv (E := E) d
          (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y)
  change |(A₁ + B₁ + C₁) - (A₂ + B₂ + C₂)| ≤
    (Module.finrank ℝ E : ℝ) * (K_A + 2 * K_B) * J
  have hA : |A₁ - A₂| ≤ (Module.finrank ℝ E : ℝ) * K_A * J := by
    dsimp only [A₁, A₂]
    refine (sum_pair_sub_bnd
      (A₁ := fun q => partialDeriv (E := E) d
        (chartDeTurckVFComp (I := I) g₁ g_bg α q) y)
      (A₂ := fun q => partialDeriv (E := E) d
        (chartDeTurckVFComp (I := I) g₂ g_bg α q) y)
      (B₁ := fun q => partialDeriv (E := E) q (chartGramOnE (I := I) g₁ α i j) y)
      (B₂ := fun q => partialDeriv (E := E) q (chartGramOnE (I := I) g₂ α i j) y)
      (C₁ := fun q => chartDeTurckVFComp (I := I) g₁ g_bg α q y)
      (C₂ := fun q => chartDeTurckVFComp (I := I) g₂ g_bg α q y)
      (D₁ := fun q => partialDeriv (E := E) d
        (partialDeriv (E := E) q (chartGramOnE (I := I) g₁ α i j)) y)
      (D₂ := fun q => partialDeriv (E := E) d
        (partialDeriv (E := E) q (chartGramOnE (I := I) g₂ α i j)) y)
      hDV_nn hW₁_nn hV_nn hW₀_nn hJ_nn
      (fun q => hVD₂ d q) (fun q => hGD₁ q i j) hV₂ (fun q => hGD2₁ d q i j)
      (fun q => hVDsub d q) (fun q => hGramD q i j) hVsub
      (fun q => hGramD2 d q i j)).trans_eq ?_
    dsimp [K_A]
    ring
  have hB : |B₁ - B₂| ≤ (Module.finrank ℝ E : ℝ) * K_B * J := by
    dsimp only [B₁, B₂]
    rw [show (∑ q : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α q j) y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α q) y +
            chartGramOnE (I := I) g₁ α q j y * partialDeriv (E := E) d
              (partialDeriv (E := E) i
                (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y)) =
        ∑ q, (partialDeriv (E := E) i
              (chartDeTurckVFComp (I := I) g₁ g_bg α q) y *
            partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α q j) y +
          partialDeriv (E := E) d
              (partialDeriv (E := E) i
                (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y *
            chartGramOnE (I := I) g₁ α q j y) by
          apply Finset.sum_congr rfl
          intro q _
          ring,
      show (∑ q : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α q j) y *
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α q) y +
            chartGramOnE (I := I) g₂ α q j y * partialDeriv (E := E) d
              (partialDeriv (E := E) i
                (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y)) =
        ∑ q, (partialDeriv (E := E) i
              (chartDeTurckVFComp (I := I) g₂ g_bg α q) y *
            partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α q j) y +
          partialDeriv (E := E) d
              (partialDeriv (E := E) i
                (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y *
            chartGramOnE (I := I) g₂ α q j y) by
          apply Finset.sum_congr rfl
          intro q _
          ring]
    refine (sum_pair_sub_bnd
      (A₁ := fun q => partialDeriv (E := E) i
        (chartDeTurckVFComp (I := I) g₁ g_bg α q) y)
      (A₂ := fun q => partialDeriv (E := E) i
        (chartDeTurckVFComp (I := I) g₂ g_bg α q) y)
      (B₁ := fun q => partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α q j) y)
      (B₂ := fun q => partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α q j) y)
      (C₁ := fun q => partialDeriv (E := E) d
        (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y)
      (C₂ := fun q => partialDeriv (E := E) d
        (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y)
      (D₁ := fun q => chartGramOnE (I := I) g₁ α q j y)
      (D₂ := fun q => chartGramOnE (I := I) g₂ α q j y)
      hDV_nn hW₁_nn hD2V_nn hW₂_nn hJ_nn
      (fun q => hVD₂ i q) (fun q => hGD₁ d q j) (fun q => hVD2₂ d i q)
      (fun q => hG₁ q j) (fun q => hVDsub i q) (fun q => hGramD d q j)
      (fun q => hVD2sub d i q) (fun q => hGram q j)).trans_eq ?_
    dsimp [K_B]
    ring
  have hC : |C₁ - C₂| ≤ (Module.finrank ℝ E : ℝ) * K_B * J := by
    dsimp only [C₁, C₂]
    rw [show (∑ q : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α i q) y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α q) y +
            chartGramOnE (I := I) g₁ α i q y * partialDeriv (E := E) d
              (partialDeriv (E := E) j
                (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y)) =
        ∑ q, (partialDeriv (E := E) j
              (chartDeTurckVFComp (I := I) g₁ g_bg α q) y *
            partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α i q) y +
          partialDeriv (E := E) d
              (partialDeriv (E := E) j
                (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y *
            chartGramOnE (I := I) g₁ α i q y) by
          apply Finset.sum_congr rfl
          intro q _
          ring,
      show (∑ q : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α i q) y *
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α q) y +
            chartGramOnE (I := I) g₂ α i q y * partialDeriv (E := E) d
              (partialDeriv (E := E) j
                (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y)) =
        ∑ q, (partialDeriv (E := E) j
              (chartDeTurckVFComp (I := I) g₂ g_bg α q) y *
            partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α i q) y +
          partialDeriv (E := E) d
              (partialDeriv (E := E) j
                (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y *
            chartGramOnE (I := I) g₂ α i q y) by
          apply Finset.sum_congr rfl
          intro q _
          ring]
    refine (sum_pair_sub_bnd
      (A₁ := fun q => partialDeriv (E := E) j
        (chartDeTurckVFComp (I := I) g₁ g_bg α q) y)
      (A₂ := fun q => partialDeriv (E := E) j
        (chartDeTurckVFComp (I := I) g₂ g_bg α q) y)
      (B₁ := fun q => partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α i q) y)
      (B₂ := fun q => partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α i q) y)
      (C₁ := fun q => partialDeriv (E := E) d
        (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α q)) y)
      (C₂ := fun q => partialDeriv (E := E) d
        (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α q)) y)
      (D₁ := fun q => chartGramOnE (I := I) g₁ α i q y)
      (D₂ := fun q => chartGramOnE (I := I) g₂ α i q y)
      hDV_nn hW₁_nn hD2V_nn hW₂_nn hJ_nn
      (fun q => hVD₂ j q) (fun q => hGD₁ d i q) (fun q => hVD2₂ d j q)
      (fun q => hG₁ i q) (fun q => hVDsub j q) (fun q => hGramD d i q)
      (fun q => hVD2sub d j q) (fun q => hGram i q)).trans_eq ?_
    dsimp [K_B]
    ring
  rw [show (A₁ + B₁ + C₁) - (A₂ + B₂ + C₂) =
    (A₁ - A₂) + (B₁ - B₂) + (C₁ - C₂) by ring]
  calc
    |(A₁ - A₂) + (B₁ - B₂) + (C₁ - C₂)| ≤
        (|A₁ - A₂| + |B₁ - B₂|) + |C₁ - C₂| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((Module.finrank ℝ E : ℝ) * K_A * J +
          (Module.finrank ℝ E : ℝ) * K_B * J) +
        (Module.finrank ℝ E : ℝ) * K_B * J := add_le_add (add_le_add hA hB) hC
    _ = (Module.finrank ℝ E : ℝ) * (K_A + 2 * K_B) * J := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
