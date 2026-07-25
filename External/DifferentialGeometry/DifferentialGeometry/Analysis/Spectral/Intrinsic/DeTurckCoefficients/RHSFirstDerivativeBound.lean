import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelSecondDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSAbsoluteBound









namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma abs_mul_le {a b A B : ℝ} (hA_nn : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA_nn

private lemma abs_add4_le (a b c d : ℝ) :
    |a + b + c + d| ≤ ((|a| + |b|) + |c|) + |d| := by
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

private lemma abs_sum2_mul_le {n : ℕ} (A B C D : Fin n → ℝ)
    {CA CB CC CD : ℝ} (hCA_nn : 0 ≤ CA) (hCC_nn : 0 ≤ CC)
    (hA : ∀ k, |A k| ≤ CA) (hB : ∀ k, |B k| ≤ CB)
    (hC : ∀ k, |C k| ≤ CC) (hD : ∀ k, |D k| ≤ CD) :
    |∑ k, (A k * B k + C k * D k)| ≤ (n : ℝ) * (CA * CB + CC * CD) := by
  classical
  calc
    |∑ k, (A k * B k + C k * D k)| ≤
        ∑ k, |A k * B k + C k * D k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (CA * CB + CC * CD) := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact (abs_add_le _ _).trans
        (add_le_add (abs_mul_le hCA_nn (hA k) (hB k))
          (abs_mul_le hCC_nn (hC k) (hD k)))
    _ = (n : ℝ) * (CA * CB + CC * CD) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
private lemma christ_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) y := by
  exact ((chartChristoffel_contDiffOn_interior (I := I) g α i j k).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma christD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (d i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) d (chartChristoffel (I := I) g α i j k)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    (chartChristoffel_contDiffOn_interior (I := I) g α i j k) d
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma inv_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y := by
  have h := (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma invD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (d a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) d
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma riemann_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartRiemannTensor (I := I) g α i j k l) y := by
  have h1 := christD_diffAt (I := I) g α j i k l hy
  have h2 := christD_diffAt (I := I) g α k i j l hy
  have hquad : ∀ m : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartChristoffel (I := I) g α j m l z *
          chartChristoffel (I := I) g α i k m z -
        chartChristoffel (I := I) g α k m l z *
          chartChristoffel (I := I) g α i j m z) y := by
    intro m
    exact ((christ_diffAt (I := I) g α j m l hy).mul
      (christ_diffAt (I := I) g α i k m hy)).sub
        ((christ_diffAt (I := I) g α k m l hy).mul
          (christ_diffAt (I := I) g α i j m hy))
  rw [show chartRiemannTensor (I := I) g α i j k l = fun z =>
      partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) z -
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) z +
        ∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l z *
              chartChristoffel (I := I) g α i k m z -
            chartChristoffel (I := I) g α k m l z *
              chartChristoffel (I := I) g α i j m z) by
        funext z; rw [chartRiemannTensor_def]]
  exact (h1.sub h2).add (DifferentiableAt.fun_sum fun m _ => hquad m)



omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRiemann
    (g : SmoothRiemannianMetric I M) (α : M)
    (d i j k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d (chartRiemannTensor (I := I) g α i j k l) y =
      partialDeriv (E := E) d
          (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)) y -
        partialDeriv (E := E) d
          (partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l)) y +
        ∑ m : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartChristoffel (I := I) g α j m l) y *
                chartChristoffel (I := I) g α i k m y +
              chartChristoffel (I := I) g α j m l y *
                partialDeriv (E := E) d (chartChristoffel (I := I) g α i k m) y -
            (partialDeriv (E := E) d (chartChristoffel (I := I) g α k m l) y *
                chartChristoffel (I := I) g α i j m y +
              chartChristoffel (I := I) g α k m l y *
                partialDeriv (E := E) d (chartChristoffel (I := I) g α i j m) y)) := by
  classical
  have h1 := christD_diffAt (I := I) g α j i k l hy
  have h2 := christD_diffAt (I := I) g α k i j l hy
  have hA : ∀ m, DifferentiableAt ℝ
      (fun z => chartChristoffel (I := I) g α j m l z *
        chartChristoffel (I := I) g α i k m z) y := by
    intro m
    exact (christ_diffAt (I := I) g α j m l hy).mul
      (christ_diffAt (I := I) g α i k m hy)
  have hB : ∀ m, DifferentiableAt ℝ
      (fun z => chartChristoffel (I := I) g α k m l z *
        chartChristoffel (I := I) g α i j m z) y := by
    intro m
    exact (christ_diffAt (I := I) g α k m l hy).mul
      (christ_diffAt (I := I) g α i j m hy)
  have hquad : ∀ m, DifferentiableAt ℝ
      (fun z => chartChristoffel (I := I) g α j m l z *
          chartChristoffel (I := I) g α i k m z -
        chartChristoffel (I := I) g α k m l z *
          chartChristoffel (I := I) g α i j m z) y := fun m => (hA m).sub (hB m)
  rw [show chartRiemannTensor (I := I) g α i j k l = fun z =>
      partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) z -
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) z +
        ∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l z *
              chartChristoffel (I := I) g α i k m z -
            chartChristoffel (I := I) g α k m l z *
              chartChristoffel (I := I) g α i j m z) by
        funext z; rw [chartRiemannTensor_def],
    partialDeriv_add (i := d)
      (fun z => partialDeriv (E := E) j
          (chartChristoffel (I := I) g α i k l) z -
        partialDeriv (E := E) k
          (chartChristoffel (I := I) g α i j l) z)
      (fun z => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l z *
              chartChristoffel (I := I) g α i k m z -
            chartChristoffel (I := I) g α k m l z *
              chartChristoffel (I := I) g α i j m z)) (h1.sub h2)
      (DifferentiableAt.fun_sum fun m _ => hquad m),
    partialDeriv_sub (i := d)
      (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l))
      (partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l)) h1 h2,
    partialDeriv_sum (i := d) Finset.univ
      (fun m z => chartChristoffel (I := I) g α j m l z *
          chartChristoffel (I := I) g α i k m z -
        chartChristoffel (I := I) g α k m l z *
          chartChristoffel (I := I) g α i j m z)
      (fun m _ => hquad m)]
  apply congrArg (fun z =>
    partialDeriv (E := E) d
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l)) y + z)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [partialDeriv_sub (i := d) _ _ (hA m) (hB m),
    partialDeriv_mul (i := d) _ _
      (christ_diffAt (I := I) g α j m l hy)
      (christ_diffAt (I := I) g α i k m hy),
    partialDeriv_mul (i := d) _ _
      (christ_diffAt (I := I) g α k m l hy)
      (christ_diffAt (I := I) g α i j m hy)]



omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRicci
    (g : SmoothRiemannianMetric I M) (α : M)
    (d i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d (chartRicciTensor (I := I) g α i k) y =
      ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartRiemannTensor (I := I) g α i j k j) y := by
  classical
  rw [show chartRicciTensor (I := I) g α i k = fun z =>
      ∑ j : Fin (Module.finrank ℝ E), chartRiemannTensor (I := I) g α i j k j z by
        funext z; rw [chartRicciTensor_def],
    partialDeriv_sum (i := d) Finset.univ _
      (fun j _ => riemann_diffAt (I := I) g α i j k j hy)]



omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannD_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d i j k l : Fin (Module.finrank ℝ E))
    {CΓ CdΓ Cd2Γ : ℝ} (hCΓ_nn : 0 ≤ CΓ) (hCdΓ_nn : 0 ≤ CdΓ)
    (hΓ : ∀ a b c, |chartChristoffel (I := I) g α a b c y| ≤ CΓ)
    (hdΓ : ∀ e a b c, |partialDeriv (E := E) e
      (chartChristoffel (I := I) g α a b c) y| ≤ CdΓ)
    (hd2Γ : ∀ e r a b c, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartChristoffel (I := I) g α a b c)) y| ≤ Cd2Γ) :
    |partialDeriv (E := E) d (chartRiemannTensor (I := I) g α i j k l) y| ≤
      2 * Cd2Γ + 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ) := by
  classical
  rw [partial_chartRiemann (I := I) g α d i j k l hy]
  have hquad : |∑ m : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) d (chartChristoffel (I := I) g α j m l) y *
            chartChristoffel (I := I) g α i k m y +
          chartChristoffel (I := I) g α j m l y *
            partialDeriv (E := E) d (chartChristoffel (I := I) g α i k m) y -
        (partialDeriv (E := E) d (chartChristoffel (I := I) g α k m l) y *
            chartChristoffel (I := I) g α i j m y +
          chartChristoffel (I := I) g α k m l y *
            partialDeriv (E := E) d (chartChristoffel (I := I) g α i j m) y))| ≤
      4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ m : Fin (Module.finrank ℝ E), |_| ≤
          ∑ _m : Fin (Module.finrank ℝ E), 4 * (CΓ * CdΓ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        calc
          |_ + _ - (_ + _)| ≤ (|_| + |_|) + (|_| + |_|) := by
            exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
          _ ≤ (CdΓ * CΓ + CΓ * CdΓ) +
              (CdΓ * CΓ + CΓ * CdΓ) := by
            exact add_le_add
              (add_le_add (abs_mul_le hCdΓ_nn (hdΓ d j m l) (hΓ i k m))
                (abs_mul_le hCΓ_nn (hΓ j m l) (hdΓ d i k m)))
              (add_le_add (abs_mul_le hCdΓ_nn (hdΓ d k m l) (hΓ i j m))
                (abs_mul_le hCΓ_nn (hΓ k m l) (hdΓ d i j m)))
          _ = 4 * (CΓ * CdΓ) := by ring
      _ = 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    |_ - _ + _| ≤ (|_| + |_|) + |_| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (Cd2Γ + Cd2Γ) + 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ) :=
      add_le_add (add_le_add (hd2Γ d j i k l) (hd2Γ d k i j l)) hquad
    _ = 2 * Cd2Γ + 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ) := by ring



omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciD_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d i k : Fin (Module.finrank ℝ E))
    {CΓ CdΓ Cd2Γ : ℝ} (hCΓ_nn : 0 ≤ CΓ) (hCdΓ_nn : 0 ≤ CdΓ)
    (hΓ : ∀ a b c, |chartChristoffel (I := I) g α a b c y| ≤ CΓ)
    (hdΓ : ∀ e a b c, |partialDeriv (E := E) e
      (chartChristoffel (I := I) g α a b c) y| ≤ CdΓ)
    (hd2Γ : ∀ e r a b c, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartChristoffel (I := I) g α a b c)) y| ≤ Cd2Γ) :
    |partialDeriv (E := E) d (chartRicciTensor (I := I) g α i k) y| ≤
      (Module.finrank ℝ E : ℝ) *
        (2 * Cd2Γ + 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ)) := by
  classical
  rw [partial_chartRicci (I := I) g α d i k hy]
  calc
    |∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartRiemannTensor (I := I) g α i j k j) y| ≤
      ∑ j : Fin (Module.finrank ℝ E),
        |partialDeriv (E := E) d (chartRiemannTensor (I := I) g α i j k j) y| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (Module.finrank ℝ E),
        (2 * Cd2Γ + 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ)) := by
      exact Finset.sum_le_sum fun j _ =>
        chartRiemannD_le (I := I) (M := M) g α hy d i j k j hCΓ_nn hCdΓ_nn hΓ hdΓ hd2Γ
    _ = (Module.finrank ℝ E : ℝ) *
        (2 * Cd2Γ + 4 * (Module.finrank ℝ E : ℝ) * (CΓ * CdΓ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]



omit [NeZero (Module.finrank ℝ E)] in
theorem partial2_deTurckVF
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (d m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k)) y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b)) y *
            (chartChristoffel (I := I) g α a b k y -
              chartChristoffel (I := I) g_bg α a b k y) +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) y *
            (partialDeriv (E := E) d (chartChristoffel (I := I) g α a b k) y -
              partialDeriv (E := E) d (chartChristoffel (I := I) g_bg α a b k) y) +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) y -
              partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y) +
          chartInvGramOnE (I := I) g α a b y *
            (partialDeriv (E := E) d
                (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k)) y -
              partialDeriv (E := E) d
                (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y)) := by
  classical
  let s : Set E := interior (extChartAt I α).target
  have hs_open : IsOpen s := isOpen_interior
  have hEqOn : Set.EqOn
      (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k))
      (fun z => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) z *
            (chartChristoffel (I := I) g α a b k z -
              chartChristoffel (I := I) g_bg α a b k z) +
          chartInvGramOnE (I := I) g α a b z *
            (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) z -
              partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) z))) s := by
    intro z hz
    exact partialDeriv_chartDeTurckVFComp_eq (I := I) g g_bg α m k hz
  have hCongr := partialDerivWithin_congr_of_eqOn_of_mem
    (E := E) (i := d) hEqOn hy
  rw [partialDerivWithin_eq_partialDeriv_of_isOpen hs_open hy,
    partialDerivWithin_eq_partialDeriv_of_isOpen hs_open hy] at hCongr
  rw [hCongr]
  have hSummand : ∀ a b : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z) +
        chartInvGramOnE (I := I) g α a b z *
          (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) z -
            partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) z)) y := by
    intro a b
    exact ((invD_diffAt (I := I) g α m a b hy).mul
      ((christ_diffAt (I := I) g α a b k hy).sub
        (christ_diffAt (I := I) g_bg α a b k hy))).add
      ((inv_diffAt (I := I) g α a b hy).mul
        ((christD_diffAt (I := I) g α m a b k hy).sub
          (christD_diffAt (I := I) g_bg α m a b k hy)))
  rw [partialDeriv_sum (i := d) Finset.univ _
      (fun a _ => DifferentiableAt.fun_sum fun b _ => hSummand a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [partialDeriv_sum (i := d) Finset.univ _ (fun b _ => hSummand a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hInvD := invD_diffAt (I := I) g α m a b hy
  have hΓdiff := (christ_diffAt (I := I) g α a b k hy).sub
    (christ_diffAt (I := I) g_bg α a b k hy)
  have hInv := inv_diffAt (I := I) g α a b hy
  have hΓDdiff := (christD_diffAt (I := I) g α m a b k hy).sub
    (christD_diffAt (I := I) g_bg α m a b k hy)
  rw [partialDeriv_add (i := d)
      (fun z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z))
      (fun z => chartInvGramOnE (I := I) g α a b z *
        (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) z -
          partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) z))
      (hInvD.mul hΓdiff) (hInv.mul hΓDdiff),
    partialDeriv_mul (i := d)
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b))
      (fun z => chartChristoffel (I := I) g α a b k z -
        chartChristoffel (I := I) g_bg α a b k z) hInvD hΓdiff,
    partialDeriv_mul (i := d) (chartInvGramOnE (I := I) g α a b)
      (fun z => partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) z -
        partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) z)
      hInv hΓDdiff,
    partialDeriv_sub (i := d) (chartChristoffel (I := I) g α a b k)
      (chartChristoffel (I := I) g_bg α a b k)
      (christ_diffAt (I := I) g α a b k hy)
      (christ_diffAt (I := I) g_bg α a b k hy),
    partialDeriv_sub (i := d)
      (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k))
      (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k))
      (christD_diffAt (I := I) g α m a b k hy)
      (christD_diffAt (I := I) g_bg α m a b k hy)]
  ring



omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckVFD2_le
    (g g_bg : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d m k : Fin (Module.finrank ℝ E))
    {M_b D T P R S : ℝ} (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D) (hT_nn : 0 ≤ T)
    (hMb : ∀ a b, |chartInvGramOnE (I := I) g α a b y| ≤ M_b)
    (hD : ∀ e a b, |partialDeriv (E := E) e
      (chartInvGramOnE (I := I) g α a b) y| ≤ D)
    (hT : ∀ e r a b, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartInvGramOnE (I := I) g α a b)) y| ≤ T)
    (hP : ∀ a b, |chartChristoffel (I := I) g α a b k y -
      chartChristoffel (I := I) g_bg α a b k y| ≤ P)
    (hR : ∀ e a b, |partialDeriv (E := E) e
        (chartChristoffel (I := I) g α a b k) y -
      partialDeriv (E := E) e (chartChristoffel (I := I) g_bg α a b k) y| ≤ R)
    (hS : ∀ e r a b, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g α a b k)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartChristoffel (I := I) g_bg α a b k)) y| ≤ S) :
    |partialDeriv (E := E) d
      (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k)) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (T * P + 2 * D * R + M_b * S) := by
  classical
  rw [partial2_deTurckVF (I := I) g g_bg α d m k hy]
  have hterm : ∀ a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b)) y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g_bg α a b k y) +
        partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) y *
          (partialDeriv (E := E) d (chartChristoffel (I := I) g α a b k) y -
            partialDeriv (E := E) d (chartChristoffel (I := I) g_bg α a b k) y) +
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
          (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) y -
            partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y) +
        chartInvGramOnE (I := I) g α a b y *
          (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k)) y -
            partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k)) y)| ≤
        T * P + 2 * D * R + M_b * S := by
    intro a b
    calc
      |_ + _ + _ + _| ≤ ((|_| + |_|) + |_|) + |_| := abs_add4_le _ _ _ _
      _ ≤ ((T * P + D * R) + D * R) + M_b * S := by
        exact add_le_add
          (add_le_add
            (add_le_add (abs_mul_le hT_nn (hT d m a b) (hP a b))
              (abs_mul_le hD_nn (hD m a b) (hR d a b)))
            (abs_mul_le hD_nn (hD d a b) (hR m a b)))
          (abs_mul_le hMb_nn (hMb a b) (hS d m a b))
      _ = T * P + 2 * D * R + M_b * S := by ring
  calc
    |∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), _| ≤
        ∑ a : Fin (Module.finrank ℝ E), |∑ b : Fin (Module.finrank ℝ E), _| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin (Module.finrank ℝ E),
        ∑ _b : Fin (Module.finrank ℝ E), (T * P + 2 * D * R + M_b * S) := by
      refine Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun b _ => hterm a b
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * (T * P + 2 * D * R + M_b * S) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma gram_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  exact (((chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (d i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) d (chartGramOnE (I := I) g α i j)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset) d
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma vf_diffAt
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartDeTurckVFComp (I := I) g g_bg α k) y := by
  rw [show chartDeTurckVFComp (I := I) g g_bg α k = fun z =>
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z) from rfl]
  exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
    (inv_diffAt (I := I) g α a b hy).mul
      ((christ_diffAt (I := I) g α a b k hy).sub
        (christ_diffAt (I := I) g_bg α a b k hy))

omit [NeZero (Module.finrank ℝ E)] in
private lemma vfD_diffAt
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k)) y := by
  classical
  let F : E → ℝ := fun z =>
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b) z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z) +
        chartInvGramOnE (I := I) g α a b z *
          (partialDeriv (E := E) m (chartChristoffel (I := I) g α a b k) z -
            partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) z))
  have hF : DifferentiableAt ℝ F y := by
    dsimp [F]
    exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      ((invD_diffAt (I := I) g α m a b hy).mul
        ((christ_diffAt (I := I) g α a b k hy).sub
          (christ_diffAt (I := I) g_bg α a b k hy))).add
        ((inv_diffAt (I := I) g α a b hy).mul
          ((christD_diffAt (I := I) g α m a b k hy).sub
            (christD_diffAt (I := I) g_bg α m a b k hy)))
  have hEq : F =ᶠ[𝓝 y]
      partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g g_bg α k) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact (partialDeriv_chartDeTurckVFComp_eq (I := I) g g_bg α m k hz).symm
  exact hF.congr_of_eventuallyEq hEq.symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma ricci_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartRicciTensor (I := I) g α i j) y := by
  classical
  rw [show chartRicciTensor (I := I) g α i j = fun z =>
      ∑ k : Fin (Module.finrank ℝ E), chartRiemannTensor (I := I) g α i k j k z by
        funext z; rw [chartRicciTensor_def]]
  exact DifferentiableAt.fun_sum fun k _ => riemann_diffAt (I := I) g α i k j k hy

omit [NeZero (Module.finrank ℝ E)] in
private lemma lie_diffAt
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartLieDeTurckComp (I := I) g g_bg α i j) y := by
  classical
  have hA : ∀ k : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartDeTurckVFComp (I := I) g g_bg α k z *
        partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z) y := fun k =>
    (vf_diffAt (I := I) g g_bg α k hy).mul (gramD_diffAt (I := I) g α k i j hy)
  have hB : ∀ k : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartGramOnE (I := I) g α k j z *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z) y :=
    fun k => (gram_diffAt (I := I) g α k j hy).mul
      (vfD_diffAt (I := I) g g_bg α i k hy)
  have hC : ∀ k : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartGramOnE (I := I) g α i k z *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) z) y :=
    fun k => (gram_diffAt (I := I) g α i k hy).mul
      (vfD_diffAt (I := I) g g_bg α j k hy)
  rw [show chartLieDeTurckComp (I := I) g g_bg α i j = fun z =>
      (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g g_bg α k z *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z) +
      (∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α k j z *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z) +
      (∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α i k z *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) z) from rfl]
  exact ((DifferentiableAt.fun_sum fun k _ => hA k).add
    (DifferentiableAt.fun_sum fun k _ => hB k)).add
      (DifferentiableAt.fun_sum fun k _ => hC k)



omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartLie
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (d i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d (chartLieDeTurckComp (I := I) g g_bg α i j) y =
      (∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartDeTurckVFComp (I := I) g g_bg α k) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y +
          chartDeTurckVFComp (I := I) g g_bg α k y *
            partialDeriv (E := E) d
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)) y)) +
      (∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartGramOnE (I := I) g α k j) y *
            partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) y +
          chartGramOnE (I := I) g α k j y *
            partialDeriv (E := E) d
              (partialDeriv (E := E) i
                (chartDeTurckVFComp (I := I) g g_bg α k)) y)) +
      (∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartGramOnE (I := I) g α i k) y *
            partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) y +
          chartGramOnE (I := I) g α i k y *
            partialDeriv (E := E) d
              (partialDeriv (E := E) j
                (chartDeTurckVFComp (I := I) g g_bg α k)) y)) := by
  classical
  have hA : ∀ k : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartDeTurckVFComp (I := I) g g_bg α k z *
        partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z) y := fun k =>
    (vf_diffAt (I := I) g g_bg α k hy).mul (gramD_diffAt (I := I) g α k i j hy)
  have hB : ∀ k : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartGramOnE (I := I) g α k j z *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z) y :=
    fun k => (gram_diffAt (I := I) g α k j hy).mul
      (vfD_diffAt (I := I) g g_bg α i k hy)
  have hC : ∀ k : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => chartGramOnE (I := I) g α i k z *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) z) y :=
    fun k => (gram_diffAt (I := I) g α i k hy).mul
      (vfD_diffAt (I := I) g g_bg α j k hy)
  have hAsum : DifferentiableAt ℝ
      (fun z => ∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g g_bg α k z *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z) y :=
    DifferentiableAt.fun_sum fun k _ => hA k
  have hBsum : DifferentiableAt ℝ
      (fun z => ∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α k j z *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z) y :=
    DifferentiableAt.fun_sum fun k _ => hB k
  have hCsum : DifferentiableAt ℝ
      (fun z => ∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α i k z *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) z) y :=
    DifferentiableAt.fun_sum fun k _ => hC k
  rw [show chartLieDeTurckComp (I := I) g g_bg α i j = fun z =>
      (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g g_bg α k z *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z) +
      (∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α k j z *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z) +
      (∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α i k z *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) z) from rfl,
    partialDeriv_add (i := d)
      (fun z =>
        (∑ k : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) g g_bg α k z *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z) +
        (∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α k j z *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z))
      (fun z => ∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α i k z *
        partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k) z)
      (hAsum.add hBsum) hCsum,
    partialDeriv_add (i := d)
      (fun z => ∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g g_bg α k z *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) z)
      (fun z => ∑ k : Fin (Module.finrank ℝ E), chartGramOnE (I := I) g α k j z *
        partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k) z)
      hAsum hBsum,
    partialDeriv_sum (i := d) Finset.univ _ (fun k _ => hA k),
    partialDeriv_sum (i := d) Finset.univ _ (fun k _ => hB k),
    partialDeriv_sum (i := d) Finset.univ _ (fun k _ => hC k)]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply congrArg₂ (fun a b : ℝ => a + b)
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [partialDeriv_mul (i := d)
        (chartDeTurckVFComp (I := I) g g_bg α k)
        (partialDeriv (E := E) k (chartGramOnE (I := I) g α i j))
        (vf_diffAt (I := I) g g_bg α k hy)
        (gramD_diffAt (I := I) g α k i j hy)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [partialDeriv_mul (i := d)
        (chartGramOnE (I := I) g α k j)
        (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k))
        (gram_diffAt (I := I) g α k j hy)
        (vfD_diffAt (I := I) g g_bg α i k hy)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialDeriv_mul (i := d)
      (chartGramOnE (I := I) g α i k)
      (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k))
      (gram_diffAt (I := I) g α i k hy)
      (vfD_diffAt (I := I) g g_bg α j k hy)]



omit [NeZero (Module.finrank ℝ E)] in
theorem chartLieD_abs_le
    (g g_bg : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d i j : Fin (Module.finrank ℝ E))
    {Q₀ Q₁ Q₂ V DV D2V : ℝ}
    (hQ₀_nn : 0 ≤ Q₀) (hQ₁_nn : 0 ≤ Q₁) (hV_nn : 0 ≤ V) (hDV_nn : 0 ≤ DV)
    (hgram : ∀ a c, |chartGramOnE (I := I) g α a c y| ≤ Q₀)
    (hdgram : ∀ e a c, |partialDeriv (E := E) e
      (chartGramOnE (I := I) g α a c) y| ≤ Q₁)
    (hd2gram : ∀ e r a c, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartGramOnE (I := I) g α a c)) y| ≤ Q₂)
    (hvf : ∀ k, |chartDeTurckVFComp (I := I) g g_bg α k y| ≤ V)
    (hdvf : ∀ e k, |partialDeriv (E := E) e
      (chartDeTurckVFComp (I := I) g g_bg α k) y| ≤ DV)
    (hd2vf : ∀ e r k, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartDeTurckVFComp (I := I) g g_bg α k)) y| ≤ D2V) :
    |partialDeriv (E := E) d (chartLieDeTurckComp (I := I) g g_bg α i j) y| ≤
      (Module.finrank ℝ E : ℝ) *
        (3 * DV * Q₁ + V * Q₂ + 2 * Q₀ * D2V) := by
  rw [partial_chartLie (I := I) g g_bg α d i j hy]
  have hA := abs_sum2_mul_le
    (CA := DV) (CB := Q₁) (CC := V) (CD := Q₂)
    (fun k => partialDeriv (E := E) d
      (chartDeTurckVFComp (I := I) g g_bg α k) y)
    (fun k => partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
    (fun k => chartDeTurckVFComp (I := I) g g_bg α k y)
    (fun k => partialDeriv (E := E) d
      (partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)) y)
    hDV_nn hV_nn (fun k => hdvf d k) (fun k => hdgram k i j)
      (fun k => hvf k) (fun k => hd2gram d k i j)
  have hB := abs_sum2_mul_le
    (CA := Q₁) (CB := DV) (CC := Q₀) (CD := D2V)
    (fun k => partialDeriv (E := E) d (chartGramOnE (I := I) g α k j) y)
    (fun k => partialDeriv (E := E) i
      (chartDeTurckVFComp (I := I) g g_bg α k) y)
    (fun k => chartGramOnE (I := I) g α k j y)
    (fun k => partialDeriv (E := E) d
      (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg α k)) y)
    hQ₁_nn hQ₀_nn (fun k => hdgram d k j) (fun k => hdvf i k)
      (fun k => hgram k j) (fun k => hd2vf d i k)
  have hC := abs_sum2_mul_le
    (CA := Q₁) (CB := DV) (CC := Q₀) (CD := D2V)
    (fun k => partialDeriv (E := E) d (chartGramOnE (I := I) g α i k) y)
    (fun k => partialDeriv (E := E) j
      (chartDeTurckVFComp (I := I) g g_bg α k) y)
    (fun k => chartGramOnE (I := I) g α i k y)
    (fun k => partialDeriv (E := E) d
      (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg α k)) y)
    hQ₁_nn hQ₀_nn (fun k => hdgram d i k) (fun k => hdvf j k)
      (fun k => hgram i k) (fun k => hd2vf d j k)
  calc
    |_ + _ + _| ≤ (|_| + |_|) + |_| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (Module.finrank ℝ E : ℝ) * (DV * Q₁ + V * Q₂) +
          (Module.finrank ℝ E : ℝ) * (Q₁ * DV + Q₀ * D2V) +
          (Module.finrank ℝ E : ℝ) * (Q₁ * DV + Q₀ * D2V) :=
      add_le_add (add_le_add hA hB) hC
    _ = (Module.finrank ℝ E : ℝ) *
        (3 * DV * Q₁ + V * Q₂ + 2 * Q₀ * D2V) := by ring



omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRHS
    (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (d i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d (chartDeTurckRHSComp (I := I) g_bg g α i j) y =
      (-2 : ℝ) * partialDeriv (E := E) d (chartRicciTensor (I := I) g α i j) y +
        partialDeriv (E := E) d (chartLieDeTurckComp (I := I) g g_bg α i j) y := by
  have hRic := ricci_diffAt (I := I) g α i j hy
  have hLie := lie_diffAt (I := I) g g_bg α i j hy
  rw [show chartDeTurckRHSComp (I := I) g_bg g α i j = fun z =>
      (-2 : ℝ) * chartRicciTensor (I := I) g α i j z +
        chartLieDeTurckComp (I := I) g g_bg α i j z from rfl,
    partialDeriv_add (i := d)
      (fun z => (-2 : ℝ) * chartRicciTensor (I := I) g α i j z)
      (chartLieDeTurckComp (I := I) g g_bg α i j)
      (hRic.const_mul (-2 : ℝ)) hLie,
    partialDeriv_const_mul (i := d) (-2 : ℝ)
      (chartRicciTensor (I := I) g α i j) hRic]



omit [NeZero (Module.finrank ℝ E)] in
theorem chartRHSD_abs_le
    (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (d i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {CRicD CLieD : ℝ}
    (hRic : |partialDeriv (E := E) d (chartRicciTensor (I := I) g α i j) y| ≤ CRicD)
    (hLie : |partialDeriv (E := E) d
      (chartLieDeTurckComp (I := I) g g_bg α i j) y| ≤ CLieD) :
    |partialDeriv (E := E) d (chartDeTurckRHSComp (I := I) g_bg g α i j) y| ≤
      2 * CRicD + CLieD := by
  rw [partial_chartRHS (I := I) g_bg g α d i j hy]
  calc
    |(-2 : ℝ) * partialDeriv (E := E) d (chartRicciTensor (I := I) g α i j) y +
        partialDeriv (E := E) d (chartLieDeTurckComp (I := I) g g_bg α i j) y| ≤
      |(-2 : ℝ) * partialDeriv (E := E) d
        (chartRicciTensor (I := I) g α i j) y| +
        |partialDeriv (E := E) d
          (chartLieDeTurckComp (I := I) g g_bg α i j) y| := abs_add_le _ _
    _ ≤ 2 * CRicD + CLieD := by
      apply add_le_add
      · rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left hRic (by norm_num)
      · exact hLie

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
