import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.InverseGramSecondDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.MetricJet3Difference
import DifferentialGeometry.Analysis.Calculus.PartialDerivIteratedFDerivOrderBridge
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin









namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


noncomputable def gramBracketDeriv2 (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))) y +
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))) y -
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))) y

omit [NeZero (Module.finrank ℝ E)] in


theorem gramBracketD2_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E) {Q : ℝ}
    (hQ : ∀ d m c a b, |partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) c (chartGramOnE (I := I) g α a b))) y| ≤ Q)
    (d m i j l : Fin (Module.finrank ℝ E)) :
    |gramBracketDeriv2 (I := I) g α d m i j l y| ≤ 3 * Q := by
  unfold gramBracketDeriv2
  calc
    |_ + _ - _| ≤ |_| + |_| + |_| := by
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Q + Q + Q := add_le_add
      (add_le_add (hQ d m i l j) (hQ d m j l i)) (hQ d m l i j)
    _ = 3 * Q := by ring

omit [NeZero (Module.finrank ℝ E)] in


theorem gramBracketD2_sub
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (d m i j l : Fin (Module.finrank ℝ E)) :
    |gramBracketDeriv2 (I := I) g₁ α d m i j l y -
        gramBracketDeriv2 (I := I) g₂ α d m i j l y| ≤
      3 * gramD3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  have h₁ := gramD3_sub_le (I := I) (M := M) g₁ g₂ α y d m i l j
  have h₂ := gramD3_sub_le (I := I) (M := M) g₁ g₂ α y d m j l i
  have h₃ := gramD3_sub_le (I := I) (M := M) g₁ g₂ α y d m l i j
  set e₁ : ℝ := partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j))) y -
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j))) y with he₁
  set e₂ : ℝ := partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i))) y -
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i))) y with he₂
  set e₃ : ℝ := partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j))) y -
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j))) y with he₃
  have heq : gramBracketDeriv2 (I := I) g₁ α d m i j l y -
      gramBracketDeriv2 (I := I) g₂ α d m i j l y = e₁ + e₂ - e₃ := by
    simp only [he₁, he₂, he₃, gramBracketDeriv2]
    ring
  rw [heq]
  calc
    |e₁ + e₂ - e₃| ≤ (|e₁| + |e₂|) + |e₃| := by
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ gramD3DiffSup (I := I) (M := M) g₁ g₂ α y +
          gramD3DiffSup (I := I) (M := M) g₁ g₂ α y +
          gramD3DiffSup (I := I) (M := M) g₁ g₂ α y :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = 3 * gramD3DiffSup (I := I) (M := M) g₁ g₂ α y := by ring

private lemma abs_prod_sub_lip
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

omit [NeZero (Module.finrank ℝ E)] in
private lemma invD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) m
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
private lemma gramD1_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m (chartGramOnE (I := I) g α a b)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) m
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramD2_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (d m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartGramOnE (I := I) g α a b))) y := by
  have h1 := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) m
  have h2 := partialDeriv_contDiffOn_of_isOpen isOpen_interior h1 d
  exact (h2.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma bracket_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (gramBracket (I := I) g α i j l) y := by
  exact ((gramD1_diffAt (I := I) g α i l j hy).add
    (gramD1_diffAt (I := I) g α j l i hy)).sub
      (gramD1_diffAt (I := I) g α l i j hy)

omit [NeZero (Module.finrank ℝ E)] in
private lemma bracketD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (gramBracketDeriv (I := I) g α m i j l) y := by
  exact ((gramD2_diffAt (I := I) g α m i l j hy).add
    (gramD2_diffAt (I := I) g α m j l i hy)).sub
      (gramD2_diffAt (I := I) g α m l i j hy)


omit [NeZero (Module.finrank ℝ E)] in
lemma partial_gramBracketD
    (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d (gramBracketDeriv (I := I) g α m i j l) y =
      gramBracketDeriv2 (I := I) g α d m i j l y := by
  have h1 := gramD2_diffAt (I := I) g α m i l j hy
  have h2 := gramD2_diffAt (I := I) g α m j l i hy
  have h3 := gramD2_diffAt (I := I) g α m l i j hy
  unfold gramBracketDeriv gramBracketDeriv2
  rw [partialDeriv_sub (i := d)
      (fun z => partialDeriv (E := E) m
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) z +
        partialDeriv (E := E) m
          (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) z)
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)))
      (h1.add h2) h3,
    partialDeriv_add (i := d)
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)))
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))) h1 h2]



omit [NeZero (Module.finrank ℝ E)] in
theorem partial2_christ_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k)) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l)) y *
            gramBracket (I := I) g α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α d i j l y +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α m i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv2 (I := I) g α d m i j l y) := by
  classical
  let s : Set E := interior (extChartAt I α).target
  have hs_open : IsOpen s := isOpen_interior
  have hEqOn : Set.EqOn
      (partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k))
      (fun z => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
            gramBracket (I := I) g α i j l z +
          chartInvGramOnE (I := I) g α k l z *
            gramBracketDeriv (I := I) g α m i j l z)) s := by
    intro z hz
    exact partialDeriv_chartChristoffel_eq (I := I) g α m i j k hz
  have hCongr := partialDerivWithin_congr_of_eqOn_of_mem
    (E := E) (i := d) hEqOn hy
  rw [partialDerivWithin_eq_partialDeriv_of_isOpen hs_open hy,
    partialDerivWithin_eq_partialDeriv_of_isOpen hs_open hy] at hCongr
  rw [hCongr]
  have hSummand : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
          gramBracket (I := I) g α i j l z +
        chartInvGramOnE (I := I) g α k l z *
          gramBracketDeriv (I := I) g α m i j l z) y := by
    intro l
    exact ((invD_diffAt (I := I) g α m k l hy).mul
      (bracket_diffAt (I := I) g α i j l hy)).add
        ((inv_diffAt (I := I) g α k l hy).mul
          (bracketD_diffAt (I := I) g α m i j l hy))
  rw [partialDeriv_const_mul (i := d) (1 / 2 : ℝ) _
    (DifferentiableAt.fun_sum fun l _ => hSummand l)]
  congr 1
  rw [partialDeriv_sum (i := d) Finset.univ
    (fun l z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
        gramBracket (I := I) g α i j l z +
      chartInvGramOnE (I := I) g α k l z *
        gramBracketDeriv (I := I) g α m i j l z)
    (fun l _ => hSummand l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hInvD := invD_diffAt (I := I) g α m k l hy
  have hBracket := bracket_diffAt (I := I) g α i j l hy
  have hInv := inv_diffAt (I := I) g α k l hy
  have hBracketD := bracketD_diffAt (I := I) g α m i j l hy
  rw [partialDeriv_add (i := d)
      (fun z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
        gramBracket (I := I) g α i j l z)
      (fun z => chartInvGramOnE (I := I) g α k l z *
        gramBracketDeriv (I := I) g α m i j l z)
      (hInvD.mul hBracket) (hInv.mul hBracketD),
    partialDeriv_mul (i := d)
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l))
      (gramBracket (I := I) g α i j l) hInvD hBracket,
    partialDeriv_mul (i := d) (chartInvGramOnE (I := I) g α k l)
      (gramBracketDeriv (I := I) g α m i j l) hInv hBracketD,
    partialDeriv_gramBracket_eq (I := I) g α d i j l hy,
    partial_gramBracketD (I := I) g α d m i j l hy]
  ring



omit [NeZero (Module.finrank ℝ E)] in
theorem christD2_sub_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d m i j k : Fin (Module.finrank ℝ E))
    {M_b D T Q₁ Q₂ Q₃ Cinv CD CT : ℝ}
    (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D) (hT_nn : 0 ≤ T)
    (hCinv_nn : 0 ≤ Cinv) (hCD_nn : 0 ≤ CD) (hCT_nn : 0 ≤ CT)
    (hMb₂ : ∀ a c, |chartInvGramOnE (I := I) g₂ α a c y| ≤ M_b)
    (hD₂ : ∀ e a c, |partialDeriv (E := E) e
      (chartInvGramOnE (I := I) g₂ α a c) y| ≤ D)
    (hT₂ : ∀ e r a c, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₂ α a c)) y| ≤ T)
    (hQ₁ : ∀ e a c, |partialDeriv (E := E) e
      (chartGramOnE (I := I) g₁ α a c) y| ≤ Q₁)
    (hQ₂ : ∀ e r a c, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartGramOnE (I := I) g₁ α a c)) y| ≤ Q₂)
    (hQ₃ : ∀ e r s a c, |partialDeriv (E := E) e
      (partialDeriv (E := E) r
        (partialDeriv (E := E) s (chartGramOnE (I := I) g₁ α a c))) y| ≤ Q₃)
    (hInv : ∀ a c, |chartInvGramOnE (I := I) g₁ α a c y -
      chartInvGramOnE (I := I) g₂ α a c y| ≤
        Cinv * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hInvD : ∀ e a c, |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) g₁ α a c) y -
      partialDeriv (E := E) e (chartInvGramOnE (I := I) g₂ α a c) y| ≤
        CD * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hInvD2 : ∀ e r a c, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₁ α a c)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₂ α a c)) y| ≤
        CT * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y) :
    |partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k)) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k)) y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        ((CT * (3 * Q₁) + 3 * T) + 2 * (CD * (3 * Q₂) + 3 * D) +
          (Cinv * (3 * Q₃) + 3 * M_b)) *
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  set J₃ : ℝ := metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y with hJ₃_def
  have hJ₃_nn : 0 ≤ J₃ := metricJet3_nonneg (I := I) (M := M) g₁ g₂ α y
  have hJ₂_le : chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y ≤ J₃ :=
    metricJet2_le_jet3 (I := I) (M := M) g₁ g₂ α y
  have hP₁_le : chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y ≤ J₃ :=
    ((chartGramPartialDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y).trans
      (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y)).trans hJ₂_le
  have hP₂_le : chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y ≤ J₃ :=
    (chartGramPartial2DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y).trans hJ₂_le
  have hP₃_le : gramD3DiffSup (I := I) (M := M) g₁ g₂ α y ≤ J₃ :=
    gramD3_le_jet3 (I := I) (M := M) g₁ g₂ α y
  have hInv₃ : ∀ a c, |chartInvGramOnE (I := I) g₁ α a c y -
      chartInvGramOnE (I := I) g₂ α a c y| ≤ Cinv * J₃ := by
    intro a c
    exact (hInv a c).trans (mul_le_mul_of_nonneg_left hJ₂_le hCinv_nn)
  have hInvD₃ : ∀ e a c, |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) g₁ α a c) y -
      partialDeriv (E := E) e (chartInvGramOnE (I := I) g₂ α a c) y| ≤ CD * J₃ := by
    intro e a c
    exact (hInvD e a c).trans (mul_le_mul_of_nonneg_left hJ₂_le hCD_nn)
  have hInvD2₃ : ∀ e r a c, |partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₁ α a c)) y -
      partialDeriv (E := E) e
        (partialDeriv (E := E) r (chartInvGramOnE (I := I) g₂ α a c)) y| ≤ CT * J₃ := by
    intro e r a c
    exact (hInvD2 e r a c).trans (mul_le_mul_of_nonneg_left hJ₂_le hCT_nn)
  let K : ℝ := (CT * (3 * Q₁) + 3 * T) + 2 * (CD * (3 * Q₂) + 3 * D) +
    (Cinv * (3 * Q₃) + 3 * M_b)
  rw [partial2_christ_eq (I := I) g₁ α d m i j k hy,
    partial2_christ_eq (I := I) g₂ α d m i j k hy,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  let F : Fin (Module.finrank ℝ E) → ℝ := fun l =>
    ((partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l)) y *
        gramBracket (I := I) g₁ α i j l y +
      partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y *
        gramBracketDeriv (I := I) g₁ α d i j l y +
      partialDeriv (E := E) d (chartInvGramOnE (I := I) g₁ α k l) y *
        gramBracketDeriv (I := I) g₁ α m i j l y +
      chartInvGramOnE (I := I) g₁ α k l y *
        gramBracketDeriv2 (I := I) g₁ α d m i j l y) -
     (partialDeriv (E := E) d
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l)) y *
        gramBracket (I := I) g₂ α i j l y +
      partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
        gramBracketDeriv (I := I) g₂ α d i j l y +
      partialDeriv (E := E) d (chartInvGramOnE (I := I) g₂ α k l) y *
        gramBracketDeriv (I := I) g₂ α m i j l y +
      chartInvGramOnE (I := I) g₂ α k l y *
        gramBracketDeriv2 (I := I) g₂ α d m i j l y))
  change (1 / 2 : ℝ) * abs (∑ l, F l) ≤ _
  rw [show (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
      ((CT * (3 * Q₁) + 3 * T) + 2 * (CD * (3 * Q₂) + 3 * D) +
        (Cinv * (3 * Q₃) + 3 * M_b)) * J₃ =
      (1 / 2 : ℝ) * ((Module.finrank ℝ E : ℝ) * K * J₃) by
    dsimp [K]
    ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hAbs : abs (∑ l, F l) ≤ ∑ l, |F l| := Finset.abs_sum_le_sum_abs _ _
  refine hAbs.trans ?_
  calc
    ∑ l, |F l| ≤ ∑ _l : Fin (Module.finrank ℝ E), K * J₃ := by
        refine Finset.sum_le_sum fun l _ => ?_
        dsimp only [F]
        let A₁ : ℝ := partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l)) y *
          gramBracket (I := I) g₁ α i j l y
        let A₂ : ℝ := partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l)) y *
          gramBracket (I := I) g₂ α i j l y
        let B₁ : ℝ := partialDeriv (E := E) m
            (chartInvGramOnE (I := I) g₁ α k l) y *
          gramBracketDeriv (I := I) g₁ α d i j l y
        let B₂ : ℝ := partialDeriv (E := E) m
            (chartInvGramOnE (I := I) g₂ α k l) y *
          gramBracketDeriv (I := I) g₂ α d i j l y
        let C₁ : ℝ := partialDeriv (E := E) d
            (chartInvGramOnE (I := I) g₁ α k l) y *
          gramBracketDeriv (I := I) g₁ α m i j l y
        let C₂ : ℝ := partialDeriv (E := E) d
            (chartInvGramOnE (I := I) g₂ α k l) y *
          gramBracketDeriv (I := I) g₂ α m i j l y
        let L₁ : ℝ := chartInvGramOnE (I := I) g₁ α k l y *
          gramBracketDeriv2 (I := I) g₁ α d m i j l y
        let L₂ : ℝ := chartInvGramOnE (I := I) g₂ α k l y *
          gramBracketDeriv2 (I := I) g₂ α d m i j l y
        change |(A₁ + B₁ + C₁ + L₁) - (A₂ + B₂ + C₂ + L₂)| ≤ K * J₃
        have hP : |gramBracket (I := I) g₁ α i j l y| ≤ 3 * Q₁ :=
          gramBracket_abs_le (I := I) (M := M) g₁ α y hQ₁ i j l
        have hRd : |gramBracketDeriv (I := I) g₁ α d i j l y| ≤ 3 * Q₂ :=
          gramBracketD_abs_le (I := I) (M := M) g₁ α y hQ₂ d i j l
        have hRm : |gramBracketDeriv (I := I) g₁ α m i j l y| ≤ 3 * Q₂ :=
          gramBracketD_abs_le (I := I) (M := M) g₁ α y hQ₂ m i j l
        have hU : |gramBracketDeriv2 (I := I) g₁ α d m i j l y| ≤ 3 * Q₃ :=
          gramBracketD2_abs_le (I := I) (M := M) g₁ α y hQ₃ d m i j l
        have hBr : |gramBracket (I := I) g₁ α i j l y -
            gramBracket (I := I) g₂ α i j l y| ≤ 3 * J₃ := by
          have h₁ := (partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup
            (I := I) (M := M) g₁ g₂ α y i l j).trans hP₁_le
          have h₂ := (partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup
            (I := I) (M := M) g₁ g₂ α y j l i).trans hP₁_le
          have h₃ := (partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup
            (I := I) (M := M) g₁ g₂ α y l i j).trans hP₁_le
          set e₁ : ℝ := partialDeriv (E := E) i
              (chartGramOnE (I := I) g₁ α l j) y -
            partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y with he₁
          set e₂ : ℝ := partialDeriv (E := E) j
              (chartGramOnE (I := I) g₁ α l i) y -
            partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y with he₂
          set e₃ : ℝ := partialDeriv (E := E) l
              (chartGramOnE (I := I) g₁ α i j) y -
            partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y with he₃
          have heq : gramBracket (I := I) g₁ α i j l y -
              gramBracket (I := I) g₂ α i j l y = e₁ + e₂ - e₃ := by
            simp only [he₁, he₂, he₃, gramBracket]
            ring
          rw [heq]
          calc
            |e₁ + e₂ - e₃| ≤ (|e₁| + |e₂|) + |e₃| := by
              exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
            _ ≤ J₃ + J₃ + J₃ := add_le_add (add_le_add h₁ h₂) h₃
            _ = 3 * J₃ := by ring
        have hBrd : |gramBracketDeriv (I := I) g₁ α d i j l y -
            gramBracketDeriv (I := I) g₂ α d i j l y| ≤ 3 * J₃ :=
          (gramBracketDeriv_sub_abs_le (I := I) (M := M) g₁ g₂ α y d i j l).trans
            (mul_le_mul_of_nonneg_left hP₂_le (by norm_num))
        have hBrm : |gramBracketDeriv (I := I) g₁ α m i j l y -
            gramBracketDeriv (I := I) g₂ α m i j l y| ≤ 3 * J₃ :=
          (gramBracketDeriv_sub_abs_le (I := I) (M := M) g₁ g₂ α y m i j l).trans
            (mul_le_mul_of_nonneg_left hP₂_le (by norm_num))
        have hBr2 : |gramBracketDeriv2 (I := I) g₁ α d m i j l y -
            gramBracketDeriv2 (I := I) g₂ α d m i j l y| ≤ 3 * J₃ :=
          (gramBracketD2_sub (I := I) (M := M) g₁ g₂ α y d m i j l).trans
            (mul_le_mul_of_nonneg_left hP₃_le (by norm_num))
        have hA : |A₁ - A₂| ≤ (CT * (3 * Q₁) + T * 3) * J₃ := by
          dsimp only [A₁, A₂]
          exact abs_prod_sub_lip hT_nn hCT_nn hJ₃_nn
            (hT₂ d m k l) hP (hInvD2₃ d m k l) hBr
        have hB : |B₁ - B₂| ≤ (CD * (3 * Q₂) + D * 3) * J₃ := by
          dsimp only [B₁, B₂]
          exact abs_prod_sub_lip hD_nn hCD_nn hJ₃_nn
            (hD₂ m k l) hRd (hInvD₃ m k l) hBrd
        have hC : |C₁ - C₂| ≤ (CD * (3 * Q₂) + D * 3) * J₃ := by
          dsimp only [C₁, C₂]
          exact abs_prod_sub_lip hD_nn hCD_nn hJ₃_nn
            (hD₂ d k l) hRm (hInvD₃ d k l) hBrm
        have hL : |L₁ - L₂| ≤ (Cinv * (3 * Q₃) + M_b * 3) * J₃ := by
          dsimp only [L₁, L₂]
          exact abs_prod_sub_lip hMb_nn hCinv_nn hJ₃_nn
            (hMb₂ k l) hU (hInv₃ k l) hBr2
        rw [show (A₁ + B₁ + C₁ + L₁) - (A₂ + B₂ + C₂ + L₂) =
          (A₁ - A₂) + (B₁ - B₂) + (C₁ - C₂) + (L₁ - L₂) by ring]
        calc
          |(A₁ - A₂) + (B₁ - B₂) + (C₁ - C₂) + (L₁ - L₂)| ≤
              ((|A₁ - A₂| + |B₁ - B₂|) + |C₁ - C₂|) + |L₁ - L₂| := by
            exact (abs_add_le _ _).trans
              (add_le_add ((abs_add_le _ _).trans
                (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
          _ ≤ (((CT * (3 * Q₁) + T * 3) * J₃ +
                (CD * (3 * Q₂) + D * 3) * J₃) +
              (CD * (3 * Q₂) + D * 3) * J₃) +
            (Cinv * (3 * Q₃) + M_b * 3) * J₃ :=
              add_le_add (add_le_add (add_le_add hA hB) hC) hL
          _ = K * J₃ := by dsimp [K]; ring
    _ = (Module.finrank ℝ E : ℝ) * (K * J₃) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * K * J₃ := by ring



omit [NeZero (Module.finrank ℝ E)] in
theorem christD2_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d m i j k : Fin (Module.finrank ℝ E))
    {M_b D T P R U : ℝ} (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D) (hT_nn : 0 ≤ T)
    (hMb : ∀ l, |chartInvGramOnE (I := I) g α k l y| ≤ M_b)
    (hD : ∀ e l, |partialDeriv (E := E) e
      (chartInvGramOnE (I := I) g α k l) y| ≤ D)
    (hT : ∀ e r l, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartInvGramOnE (I := I) g α k l)) y| ≤ T)
    (hP : ∀ l, |gramBracket (I := I) g α i j l y| ≤ P)
    (hR : ∀ e l, |gramBracketDeriv (I := I) g α e i j l y| ≤ R)
    (hU : ∀ e r l, |gramBracketDeriv2 (I := I) g α e r i j l y| ≤ U) :
    |partialDeriv (E := E) d
      (partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k)) y| ≤
        (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
          (T * P + 2 * D * R + M_b * U) := by
  classical
  rw [partial2_christ_eq (I := I) g α d m i j k hy, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l)) y *
            gramBracket (I := I) g α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α d i j l y +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α m i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv2 (I := I) g α d m i j l y)| ≤
        ∑ _l : Fin (Module.finrank ℝ E), (T * P + 2 * D * R + M_b * U) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    calc
      |_ + _ + _ + _| ≤ ((|_| + |_|) + |_|) + |_| := by
        exact (abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ ((T * P + D * R) + D * R) + M_b * U := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (by rw [abs_mul]; exact mul_le_mul (hT d m l) (hP l) (abs_nonneg _) hT_nn)
              (by rw [abs_mul]; exact mul_le_mul (hD m l) (hR d l) (abs_nonneg _) hD_nn))
            (by rw [abs_mul]; exact mul_le_mul (hD d l) (hR m l) (abs_nonneg _) hD_nn))
          (by rw [abs_mul]; exact mul_le_mul (hMb l) (hU d m l) (abs_nonneg _) hMb_nn)
      _ = T * P + 2 * D * R + M_b * U := by ring
  calc
    (1 / 2 : ℝ) * |∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l)) y *
            gramBracket (I := I) g α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α d i j l y +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α m i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv2 (I := I) g α d m i j l y)|
      ≤ (1 / 2 : ℝ) * ∑ _l : Fin (Module.finrank ℝ E),
          (T * P + 2 * D * R + M_b * U) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
          (T * P + 2 * D * R + M_b * U) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring



omit [NeZero (Module.finrank ℝ E)] in
theorem christD2_pou_bnd
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ Q₂ Q₃ : ℝ) (hQ₁_nn : 0 ≤ Q₁) (hQ₂_nn : 0 ≤ Q₂) (hQ₃_nn : 0 ≤ Q₃)
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
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂)
    (hQ₃ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α a c))) (extChartAt I α b)| ≤ Q₃) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d m i j l : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartChristoffel (I := I) (gSeq k) α i j l)) (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let T : ℝ := 2 * (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) +
    (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂)
  let P : ℝ := 3 * Q₁
  let R : ℝ := 3 * Q₂
  let U : ℝ := 3 * Q₃
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    (T * P + 2 * D * R + M_b * U)
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hT_nn : 0 ≤ T := by dsimp [T]; positivity
  have hC_nn : 0 ≤ C := by dsimp [C, T, D, P, R, U]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb d m i j l
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
  have hDOnE : ∀ e a c,
      |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) (gSeq k) α a c) (extChartAt I α b)| ≤ D := by
    intro e a c
    exact invGramD_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le hMbOnE
      (hQ₁ α hα k b hb) e a c
  have hTOnE : ∀ e r a c,
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartInvGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ T := by
    intro e r a c
    exact invGramD2_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le hQ₁_nn
      hMbOnE (hQ₁ α hα k b hb) (hQ₂ α hα k b hb) e r a c
  have hPOnE : ∀ r,
      |gramBracket (I := I) (gSeq k) α i j r (extChartAt I α b)| ≤ P := by
    intro r
    exact gramBracket_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (hQ₁ α hα k b hb) i j r
  have hROnE : ∀ e r,
      |gramBracketDeriv (I := I) (gSeq k) α e i j r (extChartAt I α b)| ≤ R := by
    intro e r
    exact gramBracketD_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (hQ₂ α hα k b hb) e i j r
  have hUOnE : ∀ e r a,
      |gramBracketDeriv2 (I := I) (gSeq k) α e r i j a (extChartAt I α b)| ≤ U := by
    intro e r a
    exact gramBracketD2_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (hQ₃ α hα k b hb) e r i j a
  exact christD2_abs_le (I := I) (M := M) (gSeq k) α hy d m i j l hM_b.le hD_nn hT_nn
    (fun a => hMbOnE l a) (fun e a => hDOnE e l a) (fun e r a => hTOnE e r l a)
    hPOnE hROnE hUOnE



omit [NeZero (Module.finrank ℝ E)] in
theorem christD2_pou_lip
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ Q₂ Q₃ : ℝ) (hQ₁_nn : 0 ≤ Q₁) (hQ₂_nn : 0 ≤ Q₂) (hQ₃_nn : 0 ≤ Q₃)
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
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂)
    (hQ₃ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α a c))) (extChartAt I α b)| ≤ Q₃) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d m i j l : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
                (partialDeriv (E := E) m
                  (chartChristoffel (I := I) (gSeq k₁) α i j l)) (extChartAt I α b) -
              partialDeriv (E := E) d
                (partialDeriv (E := E) m
                  (chartChristoffel (I := I) (gSeq k₂) α i j l)) (extChartAt I α b)| ≤
              C * metricJet3DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨CD, hCD, hInvDLip⟩ :=
    invGramD_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv Q₁ hQ₁_nn hQ₁
  obtain ⟨T, hT_nn, hT⟩ :=
    invGramD2_pou_bnd (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ Q₂ hQ₁_nn hQ₂_nn hQ₁ hQ₂
  obtain ⟨CT, hCT, hInvD2Lip⟩ :=
    invGramD2_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ Q₂ hQ₁_nn hQ₂_nn hQ₁ hQ₂
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let C₀ : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    ((CT * (3 * Q₁) + 3 * T) + 2 * (CD * (3 * Q₂) + 3 * D) +
      (Cinv * (3 * Q₃) + 3 * M_b))
  let C : ℝ := C₀ + 1
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hC_pos : 0 < C := by
    dsimp [C, C₀, D]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb d m i j l
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
  have hMb₂ : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₂ b hb a c
  have hD₂ : ∀ e a c,
      |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤ D := by
    intro e a c
    exact invGramD_abs_le (I := I) (M := M) (gSeq k₂) α hy hM_b.le hMb₂
      (hQ₁ α hα k₂ b hb) e a c
  have hT₂ : ∀ e r a c,
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartInvGramOnE (I := I) (gSeq k₂) α a c)) (extChartAt I α b)| ≤ T := by
    intro e r a c
    exact hT α hα k₂ b hb e r a c
  have hInv : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * chartMetricJet2DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro a c
    have hpt : |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * chartGramDiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α b := by
      rw [chartInvGramOnE_def, chartInvGramOnE_def, hleft]
      exact hInvLip α hα k₁ k₂ b hb a c
    have hle := (chartGramDiffSup_le_jet1 (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)).trans
        (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b))
    rw [hleft] at hle
    exact hpt.trans (mul_le_mul_of_nonneg_left hle hCinv.le)
  have hInvD : ∀ e a c,
      |partialDeriv (E := E) e
          (chartInvGramOnE (I := I) (gSeq k₁) α a c) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤
          CD * chartMetricJet2DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e a c
    exact (hInvDLip α hα k₁ k₂ b hb e a c).trans
      (mul_le_mul_of_nonneg_left
        (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b)) hCD.le)
  have hpoint := christD2_sub_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy d m i j l
      hM_b.le hD_nn hT_nn hCinv.le hCD.le hCT.le hMb₂ hD₂ hT₂
      (hQ₁ α hα k₁ b hb) (hQ₂ α hα k₁ b hb) (hQ₃ α hα k₁ b hb)
      hInv hInvD (hInvD2Lip α hα k₁ k₂ b hb)
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C, C₀]; linarith)
    (metricJet3_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
