import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation










namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma abs_mul3_le {a b c A B C : ℝ}
    (hA_nn : 0 ≤ A) (hB_nn : 0 ≤ B)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hA_nn) hc
    (abs_nonneg _) (mul_nonneg hA_nn hB_nn)

private lemma abs_mul5_le {a b c d e A B C D F : ℝ}
    (hA_nn : 0 ≤ A) (hB_nn : 0 ≤ B) (hC_nn : 0 ≤ C) (hD_nn : 0 ≤ D)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (he : |e| ≤ F) :
    |a * b * c * d * e| ≤ A * B * C * D * F := by
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  have hab := mul_le_mul ha hb (abs_nonneg _) hA_nn
  have habc := mul_le_mul hab hc (abs_nonneg _) (mul_nonneg hA_nn hB_nn)
  have habcd := mul_le_mul habc hd (abs_nonneg _)
    (mul_nonneg (mul_nonneg hA_nn hB_nn) hC_nn)
  exact mul_le_mul habcd he (abs_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg hA_nn hB_nn) hC_nn) hD_nn)

private lemma abs_sum_le_card {J : Type*} [Fintype J]
    (f : J → ℝ) {C : ℝ} (h : ∀ j, |f j| ≤ C) :
    |∑ j, f j| ≤ (Fintype.card J : ℝ) * C := by
  classical
  calc
    |∑ j, f j| ≤ ∑ j, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, C := Finset.sum_le_sum fun j _ => h j
    _ = (Fintype.card J : ℝ) * C := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma abs_sum2_le {J : Type*} [Fintype J]
    (f : J → J → ℝ) {C : ℝ} (h : ∀ i j, |f i j| ≤ C) :
    |∑ i, ∑ j, f i j| ≤ (Fintype.card J : ℝ) ^ 2 * C := by
  have hraw := abs_sum_le_card (fun i => ∑ j, f i j)
    (fun i => abs_sum_le_card (f i) (h i))
  calc
    _ ≤ (Fintype.card J : ℝ) * ((Fintype.card J : ℝ) * C) := hraw
    _ = (Fintype.card J : ℝ) ^ 2 * C := by ring

private lemma abs_sum4_le {J : Type*} [Fintype J]
    (f : J → J → J → J → ℝ) {C : ℝ}
    (h : ∀ i j k l, |f i j k l| ≤ C) :
    |∑ i, ∑ j, ∑ k, ∑ l, f i j k l| ≤ (Fintype.card J : ℝ) ^ 4 * C := by
  have hraw := abs_sum_le_card (fun i => ∑ j, ∑ k, ∑ l, f i j k l)
    (fun i => abs_sum_le_card (fun j => ∑ k, ∑ l, f i j k l)
      (fun j => abs_sum_le_card (fun k => ∑ l, f i j k l)
        (fun k => abs_sum_le_card (f i j k) (h i j k))))
  calc
    _ ≤ (Fintype.card J : ℝ) * ((Fintype.card J : ℝ) *
        ((Fintype.card J : ℝ) * ((Fintype.card J : ℝ) * C))) := hraw
    _ = (Fintype.card J : ℝ) ^ 4 * C := by ring

private lemma abs_prod5_lip
    {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ M_b Q C J : ℝ}
    (hM : 0 ≤ M_b) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (ha₂ : |a₂| ≤ M_b)
    (hb₁ : |b₁| ≤ M_b) (hb₂ : |b₂| ≤ M_b)
    (hc₁ : |c₁| ≤ M_b) (hc₂ : |c₂| ≤ M_b)
    (hd₁ : |d₁| ≤ Q) (hd₂ : |d₂| ≤ Q)
    (he₁ : |e₁| ≤ Q)
    (ha : |a₁ - a₂| ≤ C * J) (hb : |b₁ - b₂| ≤ C * J)
    (hc : |c₁ - c₂| ≤ C * J) (hd : |d₁ - d₂| ≤ J)
    (he : |e₁ - e₂| ≤ J) :
    |a₁ * b₁ * c₁ * d₁ * e₁ - a₂ * b₂ * c₂ * d₂ * e₂| ≤
      (3 * C * M_b ^ 2 * Q ^ 2 + 2 * M_b ^ 3 * Q) * J := by
  have hsplit :
      a₁ * b₁ * c₁ * d₁ * e₁ - a₂ * b₂ * c₂ * d₂ * e₂ =
        (a₁ - a₂) * b₁ * c₁ * d₁ * e₁ +
          (a₂ * (b₁ - b₂) * c₁ * d₁ * e₁ +
            (a₂ * b₂ * (c₁ - c₂) * d₁ * e₁ +
              (a₂ * b₂ * c₂ * (d₁ - d₂) * e₁ +
                a₂ * b₂ * c₂ * d₂ * (e₁ - e₂)))) := by
    ring
  rw [hsplit]
  calc
    |_ + (_ + (_ + (_ + _)))| ≤
        |_| + (|_| + (|_| + (|_| + |_|))) := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      exact abs_add_le _ _
    _ = |a₁ - a₂| * |b₁| * |c₁| * |d₁| * |e₁| +
          (|a₂| * |b₁ - b₂| * |c₁| * |d₁| * |e₁| +
            (|a₂| * |b₂| * |c₁ - c₂| * |d₁| * |e₁| +
              (|a₂| * |b₂| * |c₂| * |d₁ - d₂| * |e₁| +
                |a₂| * |b₂| * |c₂| * |d₂| * |e₁ - e₂|))) := by
      simp only [abs_mul]
    _ ≤ (C * J) * M_b * M_b * Q * Q +
          (M_b * (C * J) * M_b * Q * Q +
            (M_b * M_b * (C * J) * Q * Q +
              (M_b * M_b * M_b * J * Q + M_b * M_b * M_b * Q * J))) := by
      gcongr
    _ = (3 * C * M_b ^ 2 * Q ^ 2 + 2 * M_b ^ 3 * Q) * J := by ring

private lemma abs_prod3_lip
    {a₁ a₂ b₁ b₂ c₁ c₂ M_b Q C J : ℝ}
    (hM : 0 ≤ M_b) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (ha₂ : |a₂| ≤ M_b)
    (hb₁ : |b₁| ≤ M_b) (hb₂ : |b₂| ≤ M_b)
    (hc₁ : |c₁| ≤ Q)
    (ha : |a₁ - a₂| ≤ C * J) (hb : |b₁ - b₂| ≤ C * J)
    (hc : |c₁ - c₂| ≤ J) :
    |a₁ * b₁ * c₁ - a₂ * b₂ * c₂| ≤
      (2 * C * M_b * Q + M_b ^ 2) * J := by
  have hsplit : a₁ * b₁ * c₁ - a₂ * b₂ * c₂ =
      (a₁ - a₂) * b₁ * c₁ +
        (a₂ * (b₁ - b₂) * c₁ + a₂ * b₂ * (c₁ - c₂)) := by
    ring
  rw [hsplit]
  calc
    |_ + (_ + _)| ≤ |_| + (|_| + |_|) := by
      exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ = |a₁ - a₂| * |b₁| * |c₁| +
          (|a₂| * |b₁ - b₂| * |c₁| + |a₂| * |b₂| * |c₁ - c₂|) := by
      simp only [abs_mul]
    _ ≤ (C * J) * M_b * Q + (M_b * (C * J) * Q + M_b * M_b * J) := by
      gcongr
    _ = (2 * C * M_b * Q + M_b ^ 2) * J := by ring



omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD2_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {M_b Q₁ Q₂ : ℝ} (hMb_nn : 0 ≤ M_b)
    (hQ₁_nn : 0 ≤ Q₁)
    (hMb : ∀ a c, |chartInvGramOnE (I := I) g α a c y| ≤ M_b)
    (hQ₁ : ∀ m a c, |partialDeriv (E := E) m
      (chartGramOnE (I := I) g α a c) y| ≤ Q₁)
    (hQ₂ : ∀ d m a c, |partialDeriv (E := E) d
      (partialDeriv (E := E) m (chartGramOnE (I := I) g α a c)) y| ≤ Q₂)
    (d m p q : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) d
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α p q)) y| ≤
        2 * (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) +
          (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂) := by
  classical
  let A : ℝ := ∑ a, ∑ c, ∑ r, ∑ s,
    chartInvGramOnE (I := I) g α p r y * chartInvGramOnE (I := I) g α a s y *
      chartInvGramOnE (I := I) g α c q y *
      partialDeriv (E := E) d (chartGramOnE (I := I) g α r s) y *
      partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y
  let B : ℝ := ∑ a, ∑ c, ∑ r, ∑ s,
    chartInvGramOnE (I := I) g α p a y * chartInvGramOnE (I := I) g α c r y *
      chartInvGramOnE (I := I) g α q s y *
      partialDeriv (E := E) d (chartGramOnE (I := I) g α r s) y *
      partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y
  let C : ℝ := ∑ a, ∑ c,
    chartInvGramOnE (I := I) g α p a y * chartInvGramOnE (I := I) g α c q y *
      partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartGramOnE (I := I) g α a c)) y
  have hA : |A| ≤ (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) := by
    dsimp only [A]
    simpa only [Fintype.card_fin] using
      (abs_sum4_le (J := Fin (Module.finrank ℝ E))
        (C := M_b ^ 3 * Q₁ ^ 2)
        (fun a c r s => chartInvGramOnE (I := I) g α p r y *
          chartInvGramOnE (I := I) g α a s y * chartInvGramOnE (I := I) g α c q y *
          partialDeriv (E := E) d (chartGramOnE (I := I) g α r s) y *
          partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y) (by
            intro a c r s
            calc
              _ ≤ M_b * M_b * M_b * Q₁ * Q₁ :=
                abs_mul5_le hMb_nn hMb_nn hMb_nn hQ₁_nn
                  (hMb p r) (hMb a s) (hMb c q) (hQ₁ d r s) (hQ₁ m a c)
              _ = M_b ^ 3 * Q₁ ^ 2 := by ring))
  have hB : |B| ≤ (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) := by
    dsimp only [B]
    simpa only [Fintype.card_fin] using
      (abs_sum4_le (J := Fin (Module.finrank ℝ E))
        (C := M_b ^ 3 * Q₁ ^ 2)
        (fun a c r s => chartInvGramOnE (I := I) g α p a y *
          chartInvGramOnE (I := I) g α c r y * chartInvGramOnE (I := I) g α q s y *
          partialDeriv (E := E) d (chartGramOnE (I := I) g α r s) y *
          partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y) (by
            intro a c r s
            calc
              _ ≤ M_b * M_b * M_b * Q₁ * Q₁ :=
                abs_mul5_le hMb_nn hMb_nn hMb_nn hQ₁_nn
                  (hMb p a) (hMb c r) (hMb q s) (hQ₁ d r s) (hQ₁ m a c)
              _ = M_b ^ 3 * Q₁ ^ 2 := by ring))
  have hC : |C| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂) := by
    dsimp only [C]
    simpa only [Fintype.card_fin] using
      (abs_sum2_le (J := Fin (Module.finrank ℝ E)) (C := M_b ^ 2 * Q₂)
        (fun a c => chartInvGramOnE (I := I) g α p a y *
          chartInvGramOnE (I := I) g α c q y * partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartGramOnE (I := I) g α a c)) y) (by
              intro a c
              calc
                _ ≤ M_b * M_b * Q₂ :=
                  abs_mul3_le hMb_nn hMb_nn (hMb p a) (hMb c q) (hQ₂ d m a c)
                _ = M_b ^ 2 * Q₂ := by ring))
  rw [partialDeriv2_chartInvGramOnE_eq (I := I) g α y d m p q hy]
  change |A + B - C| ≤ _
  calc
    |A + B - C| ≤ (|A| + |B|) + |C| := by
      exact (abs_sub (A + B) C).trans (add_le_add (abs_add_le A B) le_rfl)
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) +
          (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2)) +
        (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂) :=
      add_le_add (add_le_add hA hB) hC
    _ = 2 * (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) +
          (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂) := by ring



omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD2_sub_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {Cinv M_b Q₁ Q₂ : ℝ} (hCinv_nn : 0 ≤ Cinv) (hMb_nn : 0 ≤ M_b)
    (hQ₁_nn : 0 ≤ Q₁)
    (hMb1 : ∀ a c, |chartInvGramOnE (I := I) g₁ α a c y| ≤ M_b)
    (hMb2 : ∀ a c, |chartInvGramOnE (I := I) g₂ α a c y| ≤ M_b)
    (hQ₁1 : ∀ m a c, |partialDeriv (E := E) m
      (chartGramOnE (I := I) g₁ α a c) y| ≤ Q₁)
    (hQ₁2 : ∀ m a c, |partialDeriv (E := E) m
      (chartGramOnE (I := I) g₂ α a c) y| ≤ Q₁)
    (hQ₂1 : ∀ d m a c, |partialDeriv (E := E) d
      (partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c)) y| ≤ Q₂)
    (hCinv : ∀ a c, |chartInvGramOnE (I := I) g₁ α a c y -
      chartInvGramOnE (I := I) g₂ α a c y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (d m p q : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α p q)) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α p q)) y| ≤
      (2 * (Module.finrank ℝ E : ℝ) ^ 4 *
          (3 * Cinv * M_b ^ 2 * Q₁ ^ 2 + 2 * M_b ^ 3 * Q₁) +
        (Module.finrank ℝ E : ℝ) ^ 2 *
          (2 * Cinv * M_b * Q₂ + M_b ^ 2)) *
        chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  set J : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hJ_def
  have hJ_nn : 0 ≤ J := chartMetricJet2DiffSup_nonneg _ _ _ _
  have hgd_le : chartGramDiffSup (I := I) (M := M) g₁ g₂ α
        ((extChartAt I α).symm y) ≤ J :=
    (chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans
      (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y)
  have hinv : ∀ a c, |chartInvGramOnE (I := I) g₁ α a c y -
      chartInvGramOnE (I := I) g₂ α a c y| ≤ Cinv * J := by
    intro a c
    exact (hCinv a c).trans (mul_le_mul_of_nonneg_left hgd_le hCinv_nn)
  have hD1 : ∀ e a c, |partialDeriv (E := E) e
      (chartGramOnE (I := I) g₁ α a c) y -
        partialDeriv (E := E) e (chartGramOnE (I := I) g₂ α a c) y| ≤ J := by
    intro e a c
    exact (partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup
      (I := I) (M := M) g₁ g₂ α y e a c).trans
        ((chartGramPartialDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans
          (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y))
  have hD2 : ∀ e f a c, |partialDeriv (E := E) e
      (partialDeriv (E := E) f (chartGramOnE (I := I) g₁ α a c)) y -
        partialDeriv (E := E) e
          (partialDeriv (E := E) f (chartGramOnE (I := I) g₂ α a c)) y| ≤ J := by
    intro e f a c
    exact (partialDeriv2_chartGramOnE_sub_abs_le_partial2DiffSup
      (I := I) (M := M) g₁ g₂ α y e f a c).trans
        (chartGramPartial2DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y)
  let A₁ : ℝ := ∑ a, ∑ c, ∑ r, ∑ s,
    chartInvGramOnE (I := I) g₁ α p r y * chartInvGramOnE (I := I) g₁ α a s y *
      chartInvGramOnE (I := I) g₁ α c q y *
      partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α r s) y *
      partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c) y
  let A₂ : ℝ := ∑ a, ∑ c, ∑ r, ∑ s,
    chartInvGramOnE (I := I) g₂ α p r y * chartInvGramOnE (I := I) g₂ α a s y *
      chartInvGramOnE (I := I) g₂ α c q y *
      partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α r s) y *
      partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a c) y
  let B₁ : ℝ := ∑ a, ∑ c, ∑ r, ∑ s,
    chartInvGramOnE (I := I) g₁ α p a y * chartInvGramOnE (I := I) g₁ α c r y *
      chartInvGramOnE (I := I) g₁ α q s y *
      partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α r s) y *
      partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c) y
  let B₂ : ℝ := ∑ a, ∑ c, ∑ r, ∑ s,
    chartInvGramOnE (I := I) g₂ α p a y * chartInvGramOnE (I := I) g₂ α c r y *
      chartInvGramOnE (I := I) g₂ α q s y *
      partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α r s) y *
      partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a c) y
  let C₁ : ℝ := ∑ a, ∑ c,
    chartInvGramOnE (I := I) g₁ α p a y * chartInvGramOnE (I := I) g₁ α c q y *
      partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c)) y
  let C₂ : ℝ := ∑ a, ∑ c,
    chartInvGramOnE (I := I) g₂ α p a y * chartInvGramOnE (I := I) g₂ α c q y *
      partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a c)) y
  let K₅ : ℝ := 3 * Cinv * M_b ^ 2 * Q₁ ^ 2 + 2 * M_b ^ 3 * Q₁
  let K₃ : ℝ := 2 * Cinv * M_b * Q₂ + M_b ^ 2
  have hA : |A₁ - A₂| ≤ (Module.finrank ℝ E : ℝ) ^ 4 * (K₅ * J) := by
    dsimp only [A₁, A₂]
    simp_rw [← Finset.sum_sub_distrib]
    simpa only [Fintype.card_fin, K₅] using
      (abs_sum4_le (J := Fin (Module.finrank ℝ E)) (C := K₅ * J)
        (fun a c r s =>
          chartInvGramOnE (I := I) g₁ α p r y * chartInvGramOnE (I := I) g₁ α a s y *
              chartInvGramOnE (I := I) g₁ α c q y *
              partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α r s) y *
              partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c) y -
            chartInvGramOnE (I := I) g₂ α p r y * chartInvGramOnE (I := I) g₂ α a s y *
              chartInvGramOnE (I := I) g₂ α c q y *
              partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α r s) y *
              partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a c) y)
        (fun a c r s => abs_prod5_lip hMb_nn hQ₁_nn hCinv_nn hJ_nn
          (hMb2 p r) (hMb1 a s) (hMb2 a s) (hMb1 c q) (hMb2 c q)
          (hQ₁1 d r s) (hQ₁2 d r s) (hQ₁1 m a c)
          (hinv p r) (hinv a s) (hinv c q) (hD1 d r s) (hD1 m a c)))
  have hB : |B₁ - B₂| ≤ (Module.finrank ℝ E : ℝ) ^ 4 * (K₅ * J) := by
    dsimp only [B₁, B₂]
    simp_rw [← Finset.sum_sub_distrib]
    simpa only [Fintype.card_fin, K₅] using
      (abs_sum4_le (J := Fin (Module.finrank ℝ E)) (C := K₅ * J)
        (fun a c r s =>
          chartInvGramOnE (I := I) g₁ α p a y * chartInvGramOnE (I := I) g₁ α c r y *
              chartInvGramOnE (I := I) g₁ α q s y *
              partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α r s) y *
              partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c) y -
            chartInvGramOnE (I := I) g₂ α p a y * chartInvGramOnE (I := I) g₂ α c r y *
              chartInvGramOnE (I := I) g₂ α q s y *
              partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α r s) y *
              partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a c) y)
        (fun a c r s => abs_prod5_lip hMb_nn hQ₁_nn hCinv_nn hJ_nn
          (hMb2 p a) (hMb1 c r) (hMb2 c r) (hMb1 q s) (hMb2 q s)
          (hQ₁1 d r s) (hQ₁2 d r s) (hQ₁1 m a c)
          (hinv p a) (hinv c r) (hinv q s) (hD1 d r s) (hD1 m a c)))
  have hC : |C₁ - C₂| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (K₃ * J) := by
    dsimp only [C₁, C₂]
    simp_rw [← Finset.sum_sub_distrib]
    simpa only [Fintype.card_fin, K₃] using
      (abs_sum2_le (J := Fin (Module.finrank ℝ E)) (C := K₃ * J)
        (fun a c =>
          chartInvGramOnE (I := I) g₁ α p a y * chartInvGramOnE (I := I) g₁ α c q y *
              partialDeriv (E := E) d
                (partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a c)) y -
            chartInvGramOnE (I := I) g₂ α p a y * chartInvGramOnE (I := I) g₂ α c q y *
              partialDeriv (E := E) d
                (partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a c)) y)
        (fun a c => abs_prod3_lip hMb_nn hCinv_nn hJ_nn
          (hMb2 p a) (hMb1 c q) (hMb2 c q)
          (hQ₂1 d m a c) (hinv p a) (hinv c q) (hD2 d m a c)))
  rw [partialDeriv2_chartInvGramOnE_eq (I := I) g₁ α y d m p q hy,
    partialDeriv2_chartInvGramOnE_eq (I := I) g₂ α y d m p q hy]
  change |(A₁ + B₁ - C₁) - (A₂ + B₂ - C₂)| ≤ _
  rw [show (A₁ + B₁ - C₁) - (A₂ + B₂ - C₂) =
      (A₁ - A₂) + (B₁ - B₂) - (C₁ - C₂) by ring]
  calc
    |(A₁ - A₂) + (B₁ - B₂) - (C₁ - C₂)| ≤
        (|A₁ - A₂| + |B₁ - B₂|) + |C₁ - C₂| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 4 * (K₅ * J) +
          (Module.finrank ℝ E : ℝ) ^ 4 * (K₅ * J)) +
        (Module.finrank ℝ E : ℝ) ^ 2 * (K₃ * J) :=
      add_le_add (add_le_add hA hB) hC
    _ = (2 * (Module.finrank ℝ E : ℝ) ^ 4 *
          (3 * Cinv * M_b ^ 2 * Q₁ ^ 2 + 2 * M_b ^ 3 * Q₁) +
        (Module.finrank ℝ E : ℝ) ^ 2 *
          (2 * Cinv * M_b * Q₂ + M_b ^ 2)) * J := by
      dsimp [K₅, K₃]
      ring



omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD2_pou_bnd
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ Q₂ : ℝ) (hQ₁_nn : 0 ≤ Q₁) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d m p q : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartInvGramOnE (I := I) (gSeq k) α p q)) (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := 2 * (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) +
    (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂)
  have hC_nn : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb d m p q
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMbOnE : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k b hb a c
  exact invGramD2_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le hQ₁_nn
    hMbOnE (hQ₁ α hα k b hb) (hQ₂ α hα k b hb) d m p q




omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD2_pou_lip
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ Q₂ : ℝ) (hQ₁_nn : 0 ≤ Q₁) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d m p q : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
                (partialDeriv (E := E) m
                  (chartInvGramOnE (I := I) (gSeq k₁) α p q)) (extChartAt I α b) -
              partialDeriv (E := E) d
                (partialDeriv (E := E) m
                  (chartInvGramOnE (I := I) (gSeq k₂) α p q)) (extChartAt I α b)| ≤
              C * chartMetricJet2DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C₀ : ℝ :=
    2 * (Module.finrank ℝ E : ℝ) ^ 4 *
        (3 * Cinv * M_b ^ 2 * Q₁ ^ 2 + 2 * M_b ^ 3 * Q₁) +
      (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q₂ + M_b ^ 2)
  let C : ℝ := C₀ + 1
  have hC_pos : 0 < C := by
    dsimp [C, C₀]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb d m p q
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMb₁ : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₁ b hb a c
  have hMb₂ : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₂ b hb a c
  have hInv : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * chartGramDiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α ((extChartAt I α).symm (extChartAt I α b)) := by
    intro a c
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hleft]
    exact hInvLip α hα k₁ k₂ b hb a c
  have hpoint := invGramD2_sub_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy hCinv.le hM_b.le hQ₁_nn
      hMb₁ hMb₂ (hQ₁ α hα k₁ b hb) (hQ₁ α hα k₂ b hb)
      (hQ₂ α hα k₁ b hb) hInv d m p q
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C, C₀]; linarith)
    (chartMetricJet2DiffSup_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
