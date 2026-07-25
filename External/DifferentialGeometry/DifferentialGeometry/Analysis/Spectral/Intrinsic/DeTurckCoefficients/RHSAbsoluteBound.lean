import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz









namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
      [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in


omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicci_abs_le
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E)
    {CΓ CdΓ : ℝ} (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α a b c y| ≤ CΓ)
    (hdΓ : ∀ m a b c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g α a b c) y| ≤ CdΓ) :
    |chartRicciTensor (I := I) g α i k y| ≤
      (Module.finrank ℝ E : ℝ) *
        (2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2) := by
  classical
  have hprod : ∀ a b c d e f : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α a b c y *
          chartChristoffel (I := I) g α d e f y| ≤ CΓ ^ 2 := by
    intro a b c d e f
    rw [abs_mul]
    calc
      |chartChristoffel (I := I) g α a b c y| *
          |chartChristoffel (I := I) g α d e f y|
          ≤ CΓ * CΓ := mul_le_mul (hΓ a b c) (hΓ d e f) (abs_nonneg _) hCΓ
      _ = CΓ ^ 2 := by ring
  have hRiem : ∀ j l : Fin (Module.finrank ℝ E),
      |chartRiemannTensor (I := I) g α i j k l y| ≤
        2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 := by
    intro j l
    rw [chartRiemannTensor_def]
    have hderiv :
        |partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y| ≤
          2 * CdΓ := by
      rw [sub_eq_add_neg]
      calc
        |partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y +
            -partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y|
            ≤ |partialDeriv (E := E) j
                  (chartChristoffel (I := I) g α i k l) y| +
                |-partialDeriv (E := E) k
                  (chartChristoffel (I := I) g α i j l) y| := abs_add_le _ _
        _ = |partialDeriv (E := E) j
                  (chartChristoffel (I := I) g α i k l) y| +
                |partialDeriv (E := E) k
                  (chartChristoffel (I := I) g α i j l) y| := by rw [abs_neg]
        _ ≤ CdΓ + CdΓ := add_le_add (hdΓ j i k l) (hdΓ k i j l)
        _ = 2 * CdΓ := by ring
    have hquad :
        |∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)| ≤
          2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 := by
      calc
        |∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)|
            ≤ ∑ m : Fin (Module.finrank ℝ E),
                |chartChristoffel (I := I) g α j m l y *
                    chartChristoffel (I := I) g α i k m y -
                  chartChristoffel (I := I) g α k m l y *
                    chartChristoffel (I := I) g α i j m y| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m : Fin (Module.finrank ℝ E), (2 * CΓ ^ 2) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [sub_eq_add_neg]
          calc
            |chartChristoffel (I := I) g α j m l y *
                  chartChristoffel (I := I) g α i k m y +
                -(chartChristoffel (I := I) g α k m l y *
                  chartChristoffel (I := I) g α i j m y)|
                ≤ |chartChristoffel (I := I) g α j m l y *
                    chartChristoffel (I := I) g α i k m y| +
                  |-(chartChristoffel (I := I) g α k m l y *
                    chartChristoffel (I := I) g α i j m y)| := abs_add_le _ _
            _ = |chartChristoffel (I := I) g α j m l y *
                    chartChristoffel (I := I) g α i k m y| +
                  |chartChristoffel (I := I) g α k m l y *
                    chartChristoffel (I := I) g α i j m y| := by rw [abs_neg]
            _ ≤ CΓ ^ 2 + CΓ ^ 2 := add_le_add
                  (hprod j m l i k m) (hprod k m l i j m)
            _ = 2 * CΓ ^ 2 := by ring
        _ = 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    calc
      |partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m l y *
                chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m l y *
                chartChristoffel (I := I) g α i j m y)|
          ≤ |partialDeriv (E := E) j
                (chartChristoffel (I := I) g α i k l) y -
              partialDeriv (E := E) k
                (chartChristoffel (I := I) g α i j l) y| +
            |∑ m : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) g α j m l y *
                  chartChristoffel (I := I) g α i k m y -
                chartChristoffel (I := I) g α k m l y *
                  chartChristoffel (I := I) g α i j m y)| := abs_add_le _ _
      _ ≤ 2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 :=
        add_le_add hderiv hquad
  rw [chartRicciTensor_def]
  calc
    |∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α i j k j y|
        ≤ ∑ j : Fin (Module.finrank ℝ E),
          |chartRiemannTensor (I := I) g α i j k j y| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (Module.finrank ℝ E),
        (2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2) := by
          exact Finset.sum_le_sum fun j _ => hRiem j j
    _ = (Module.finrank ℝ E : ℝ) *
        (2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in


theorem chartLie_abs_le
    (g gBase : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E)
    {Q₀ Q₁ V DV : ℝ}
    (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁) (hV : 0 ≤ V) (hDV : 0 ≤ DV)
    (hgram : ∀ a c : Fin (Module.finrank ℝ E),
      |chartGramOnE (I := I) g α a c y| ≤ Q₀)
    (hdgram : ∀ m a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y| ≤ Q₁)
    (hvf : ∀ k : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) g gBase α k y| ≤ V)
    (hdvf : ∀ m k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g gBase α k) y| ≤ DV) :
    |chartLieDeTurckComp (I := I) g gBase α i j y| ≤
      (Module.finrank ℝ E : ℝ) * (V * Q₁ + 2 * Q₀ * DV) := by
  classical
  have hsum_prod : ∀ (A B : Fin (Module.finrank ℝ E) → ℝ)
      (CA CB : ℝ), 0 ≤ CA → 0 ≤ CB →
      (∀ k, |A k| ≤ CA) → (∀ k, |B k| ≤ CB) →
      |∑ k, A k * B k| ≤ (Module.finrank ℝ E : ℝ) * (CA * CB) := by
    intro A B CA CB hCA hCB hA hB
    calc
      |∑ k, A k * B k| ≤ ∑ k, |A k * B k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin (Module.finrank ℝ E), CA * CB := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hA k) (hB k) (abs_nonneg _) hCA
      _ = (Module.finrank ℝ E : ℝ) * (CA * CB) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hfirst := hsum_prod
    (fun k => chartDeTurckVFComp (I := I) g gBase α k y)
    (fun k => partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
    V Q₁ hV hQ₁ hvf (fun k => hdgram k i j)
  have hsecond := hsum_prod
    (fun k => chartGramOnE (I := I) g α k j y)
    (fun k => partialDeriv (E := E) i
      (chartDeTurckVFComp (I := I) g gBase α k) y)
    Q₀ DV hQ₀ hDV (fun k => hgram k j) (fun k => hdvf i k)
  have hthird := hsum_prod
    (fun k => chartGramOnE (I := I) g α i k y)
    (fun k => partialDeriv (E := E) j
      (chartDeTurckVFComp (I := I) g gBase α k) y)
    Q₀ DV hQ₀ hDV (fun k => hgram i k) (fun k => hdvf j k)
  rw [chartLieDeTurckComp_def]
  calc
    |(∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g gBase α k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (chartDeTurckVFComp (I := I) g gBase α k) y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (chartDeTurckVFComp (I := I) g gBase α k) y)|
        ≤ |(∑ k : Fin (Module.finrank ℝ E),
              chartDeTurckVFComp (I := I) g gBase α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y) +
            (∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α k j y *
                partialDeriv (E := E) i
                  (chartDeTurckVFComp (I := I) g gBase α k) y)| +
          |∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α i k y *
                partialDeriv (E := E) j
                  (chartDeTurckVFComp (I := I) g gBase α k) y| := abs_add_le _ _
    _ ≤ (|(∑ k : Fin (Module.finrank ℝ E),
              chartDeTurckVFComp (I := I) g gBase α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)| +
            |∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α k j y *
                partialDeriv (E := E) i
                  (chartDeTurckVFComp (I := I) g gBase α k) y|) +
          |∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α i k y *
                partialDeriv (E := E) j
                  (chartDeTurckVFComp (I := I) g gBase α k) y| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ ((Module.finrank ℝ E : ℝ) * (V * Q₁) +
          (Module.finrank ℝ E : ℝ) * (Q₀ * DV)) +
        (Module.finrank ℝ E : ℝ) * (Q₀ * DV) :=
          add_le_add (add_le_add hfirst hsecond) hthird
    _ = (Module.finrank ℝ E : ℝ) * (V * Q₁ + 2 * Q₀ * DV) := by ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartRHS_abs_le
    (gBase g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E)
    {CRic CLie : ℝ}
    (hRic : |chartRicciTensor (I := I) g α i j y| ≤ CRic)
    (hLie : |chartLieDeTurckComp (I := I) g gBase α i j y| ≤ CLie) :
    |chartDeTurckRHSComp (I := I) gBase g α i j y| ≤ 2 * CRic + CLie := by
  rw [chartDeTurckRHSComp_def]
  calc
    |(-2 : ℝ) * chartRicciTensor (I := I) g α i j y +
        chartLieDeTurckComp (I := I) g gBase α i j y|
        ≤ |(-2 : ℝ) * chartRicciTensor (I := I) g α i j y| +
          |chartLieDeTurckComp (I := I) g gBase α i j y| := abs_add_le _ _
    _ ≤ 2 * CRic + CLie := by
      apply add_le_add
      · rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left hRic (by norm_num)
      · exact hLie

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
