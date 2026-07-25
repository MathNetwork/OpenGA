import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by ring_nf
    _ ≤ |a| + |(-b)| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma exists_bound_of_contDiffOn_int
    {f : E → ℝ} (α : M)
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f y| ≤ C := by
  classical
  have hcont : ContinuousOn f K := (hf.continuousOn).mono hKsub
  by_cases hKne : K.Nonempty
  · have hcont_abs : ContinuousOn (fun y => |f y|) K :=
      continuous_abs.comp_continuousOn hcont
    obtain ⟨y₀, hy₀K, hy₀max⟩ := hK.exists_isMaxOn hKne hcont_abs
    exact ⟨|f y₀|, abs_nonneg _, fun y hy => hy₀max hy⟩
  · exact ⟨0, le_refl 0, fun y hy => absurd ⟨y, hy⟩ hKne⟩


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma exists_uniform_bound_of_int_family
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (α : M) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i, |f i y| ≤ C := by
  classical
  have hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f i y| ≤ C := fun i =>
    exists_bound_of_contDiffOn_int (I := I) α (hf i) hK hKsub
  choose C hC_nn hC_bd using hbound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty C, ?_, ?_⟩
  · exact le_trans (hC_nn (Classical.arbitrary ι))
      (Finset.le_sup' C (Finset.mem_univ (Classical.arbitrary ι)))
  · intro y hy i
    exact (hC_bd i y hy).trans (Finset.le_sup' C (Finset.mem_univ i))

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma partialDeriv_contDiffOn_int_of_contDiffOn
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f) (interior (extChartAt I α).target) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f) (interior (extChartAt I α).target) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartGramOnE_contDiffOn_int'
    (g : SmoothRiemannianMetric I M) (α : M)
    (a l b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_int_of_contDiffOn (I := I) α
    ((chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset) a

def chartRicciSecondOrderTerm (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
      partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y)

def chartRicciFirstOrderTerm (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    ∑ m : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g α j m j y *
          chartChristoffel (I := I) g α i k m y -
        chartChristoffel (I := I) g α k m j y *
          chartChristoffel (I := I) g α i j m y)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_eq_secondOrder_add_firstOrder
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g α i k y =
      chartRicciSecondOrderTerm (I := I) g α i k y +
        chartRicciFirstOrderTerm (I := I) g α i k y := by
  classical
  rw [chartRicciTensor_def, chartRicciSecondOrderTerm, chartRicciFirstOrderTerm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartRiemannTensor_def]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderTerm_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderTerm (I := I) g α i k y =
      chartRicciSecondOrderTerm (I := I) g α k i y := by
  classical
  rw [chartRicciSecondOrderTerm, chartRicciSecondOrderTerm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hT1 : (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsym : chartChristoffel (I := I) g α i k j =
        chartChristoffel (I := I) g α k i j :=
      funext (fun y' => chartChristoffel_symm (I := I) g α i k j y')
    rw [hsym]
  have hT2 : (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) := by
    rw [sum_partialDeriv_eq_partialDeriv_sum_christ (I := I) g α i k hy,
        sum_partialDeriv_eq_partialDeriv_sum_christ (I := I) g α k i hy]
    exact partialDeriv_contractedChristoffel_swap (I := I) g α i k hy
  rw [hT1, hT2]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciFirstOrderTerm_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderTerm (I := I) g α i k y =
      chartRicciFirstOrderTerm (I := I) g α k i y := by
  classical
  rw [chartRicciFirstOrderTerm, chartRicciFirstOrderTerm]
  simp only [Finset.sum_sub_distrib]
  have hT3 : (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α i k m y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α k i m y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [chartChristoffel_symm (I := I) g α i k m]
  have hT4 : (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k m j y *
            chartChristoffel (I := I) g α i j m y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i m j y *
            chartChristoffel (I := I) g α k j m y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hT3, hT4]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_diff_symm
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y =
      chartRicciTensor (I := I) g₁ α k i y - chartRicciTensor (I := I) g₂ α k i y := by
  rw [chartRicciTensor_symm (I := I) g₁ α i k hy,
      chartRicciTensor_symm (I := I) g₂ α i k hy]

def ricciDiffPrincipalSymbol (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₂ α j l y *
          (gramBracketDeriv (I := I) g₁ α j i k l y -
            gramBracketDeriv (I := I) g₂ α j i k l y) -
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₂ α j l y *
          (gramBracketDeriv (I := I) g₁ α k i j l y -
            gramBracketDeriv (I := I) g₂ α k i j l y))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciDiffPrincipalSymbol_def
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₂ α j l y *
              (gramBracketDeriv (I := I) g₁ α j i k l y -
                gramBracketDeriv (I := I) g₂ α j i k l y) -
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₂ α j l y *
              (gramBracketDeriv (I := I) g₁ α k i j l y -
                gramBracketDeriv (I := I) g₂ α k i j l y)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciDiffPrincipalSymbol_eq_invGram_weighted_d2_gram_diff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₂ α j l y *
              ((partialDeriv (E := E) j
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l k)) y -
                 partialDeriv (E := E) j
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l k)) y) +
               (partialDeriv (E := E) j
                  (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α l i)) y -
                 partialDeriv (E := E) j
                  (partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α l i)) y) -
               (partialDeriv (E := E) j
                  (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i k)) y -
                 partialDeriv (E := E) j
                  (partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i k)) y)) -
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₂ α j l y *
              ((partialDeriv (E := E) k
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j)) y -
                 partialDeriv (E := E) k
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j)) y) +
               (partialDeriv (E := E) k
                  (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i)) y -
                 partialDeriv (E := E) k
                  (partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i)) y) -
               (partialDeriv (E := E) k
                  (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j)) y -
                 partialDeriv (E := E) k
                  (partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j)) y))) := by
  classical
  rw [ricciDiffPrincipalSymbol_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
    simp only [gramBracketDeriv]
    ring
  · congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
    simp only [gramBracketDeriv]
    ring

def chartRicciDiffFirstOrderRemainder (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (chartRicciSecondOrderTerm (I := I) g₁ α i k y -
      chartRicciSecondOrderTerm (I := I) g₂ α i k y) -
    ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderTerm_sub_eq_principalSymbol_add_remainder
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderTerm (I := I) g₁ α i k y -
        chartRicciSecondOrderTerm (I := I) g₂ α i k y =
      ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y +
        chartRicciDiffFirstOrderRemainder (I := I) g₁ g₂ α i k y := by
  rw [chartRicciDiffFirstOrderRemainder]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_sub_eq_principalSymbol_add_lowerOrder
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y =
      ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y +
        (chartRicciDiffFirstOrderRemainder (I := I) g₁ g₂ α i k y +
          (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
            chartRicciFirstOrderTerm (I := I) g₂ α i k y)) := by
  rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₁ α i k y,
      chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₂ α i k y]
  have hsplit := chartRicciSecondOrderTerm_sub_eq_principalSymbol_add_remainder
    (I := I) g₁ g₂ α i k y
  rw [show chartRicciSecondOrderTerm (I := I) g₁ α i k y +
            chartRicciFirstOrderTerm (I := I) g₁ α i k y -
          (chartRicciSecondOrderTerm (I := I) g₂ α i k y +
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) =
        (chartRicciSecondOrderTerm (I := I) g₁ α i k y -
            chartRicciSecondOrderTerm (I := I) g₂ α i k y) +
          (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) from by ring]
  rw [hsplit]
  ring

private lemma exists_chartChristoffel_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α i j k y| ≤ C := by
  classical
  have hsmooth : ∀ p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α p.1.1 p.1.2 p.2)
        (interior (extChartAt I α).target) := by
    intro p
    have heq : chartChristoffel (I := I) g α p.1.1 p.1.2 p.2 =
        fun y : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α p.2 l y *
            gramBracket (I := I) g α p.1.1 p.1.2 l y := by
      funext y
      exact chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g α p.1.1 p.1.2 p.2 y
    rw [heq]
    refine ContDiffOn.mul contDiffOn_const ?_
    refine ContDiffOn.sum (fun l _ => ?_)
    refine ContDiffOn.mul ((chartInvGramOnE_contDiffOn (I := I) g α p.2 l).mono interior_subset) ?_
    refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partial_chartGramOnE_contDiffOn_int' (I := I) g α p.1.1 l p.1.2
    · exact partial_chartGramOnE_contDiffOn_int' (I := I) g α p.1.2 l p.1.1
    · exact partial_chartGramOnE_contDiffOn_int' (I := I) g α l p.1.1 p.1.2
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_uniform_bound_of_int_family (I := I) α
      (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
          (Fin (Module.finrank ℝ E)) => chartChristoffel (I := I) g α p.1.1 p.1.2 p.2)
      hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy i j k => hC y hy ((i, j), k)⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderTerm_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Cdiff : ℝ}
    (hCdiff : ∀ m i j k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
        Cdiff * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y)
    (i k : Fin (Module.finrank ℝ E)) :
    |chartRicciSecondOrderTerm (I := I) g₁ α i k y -
        chartRicciSecondOrderTerm (I := I) g₂ α i k y| ≤
      2 * (Module.finrank ℝ E : ℝ) * Cdiff *
        chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartRicciSecondOrderTerm, chartRicciSecondOrderTerm, ← Finset.sum_sub_distrib]
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hjet2_nn : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) => 2 * Cdiff * jet2) (fun j _ => ?_)) ?_
  · have hjk :
        (partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y) -
          (partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y) =
        (partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
            partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
          (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y) := by ring
    rw [hjk]
    refine (abs_sub_le_abs_add_abs _ _).trans ?_
    have h1 := hCdiff j i k j
    have h2 := hCdiff k i j j
    calc |partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
              partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y| +
            |partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
              partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y|
        ≤ Cdiff * jet2 + Cdiff * jet2 := add_le_add h1 h2
      _ = 2 * Cdiff * jet2 := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show 2 * (Module.finrank ℝ E : ℝ) * Cdiff * jet2 =
          (Module.finrank ℝ E : ℝ) * (2 * Cdiff * jet2) by ring]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciFirstOrderTerm_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Clip Mg : ℝ} (hClip_nn : 0 ≤ Clip) (hMg_nn : 0 ≤ Mg)
    (hClip : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y -
          chartChristoffel (I := I) g₂ α i j k y| ≤
        Clip * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hMg1 : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y| ≤ Mg)
    (hMg2 : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₂ α i j k y| ≤ Mg)
    (i k : Fin (Module.finrank ℝ E)) :
    |chartRicciFirstOrderTerm (I := I) g₁ α i k y -
        chartRicciFirstOrderTerm (I := I) g₂ α i k y| ≤
      4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg *
        chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartRicciFirstOrderTerm, chartRicciFirstOrderTerm, ← Finset.sum_sub_distrib]
  set jet1 : ℝ := chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := chartMetricJet1DiffSup_nonneg _ _ _ _
  have hprod : ∀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α a₁ a₂ a₃ y *
            chartChristoffel (I := I) g₁ α a₄ a₅ a₆ y -
          chartChristoffel (I := I) g₂ α a₁ a₂ a₃ y *
            chartChristoffel (I := I) g₂ α a₄ a₅ a₆ y| ≤
        2 * Clip * Mg * jet1 := by
    intro a₁ a₂ a₃ a₄ a₅ a₆
    set A₁ := chartChristoffel (I := I) g₁ α a₁ a₂ a₃ y
    set A₂ := chartChristoffel (I := I) g₂ α a₁ a₂ a₃ y
    set B₁ := chartChristoffel (I := I) g₁ α a₄ a₅ a₆ y
    set B₂ := chartChristoffel (I := I) g₂ α a₄ a₅ a₆ y
    have hsplit : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have hA : |A₁ - A₂| ≤ Clip * jet1 := hClip a₁ a₂ a₃
    have hB : |B₁ - B₂| ≤ Clip * jet1 := hClip a₄ a₅ a₆
    have hB₁ : |B₁| ≤ Mg := hMg1 a₄ a₅ a₆
    have hA₂ : |A₂| ≤ Mg := hMg2 a₁ a₂ a₃
    calc |(A₁ - A₂) * B₁| + |A₂ * (B₁ - B₂)|
        = |A₁ - A₂| * |B₁| + |A₂| * |B₁ - B₂| := by rw [abs_mul, abs_mul]
      _ ≤ (Clip * jet1) * Mg + Mg * (Clip * jet1) :=
          add_le_add (mul_le_mul hA hB₁ (abs_nonneg _) (mul_nonneg hClip_nn hjet1_nn))
            (mul_le_mul hA₂ hB (abs_nonneg _) hMg_nn)
      _ = 2 * Clip * Mg * jet1 := by ring
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      |∑ m : Fin (Module.finrank ℝ E),
          ((chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y) -
            (chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y))| ≤
        (Module.finrank ℝ E : ℝ) * (4 * Clip * Mg * jet1) := by
    intro j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum
      (g := fun _ : Fin (Module.finrank ℝ E) => 4 * Clip * Mg * jet1) (fun m _ => ?_)) ?_
    · have hrearr :
          (chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y) -
            (chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y) =
          (chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y) -
            (chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y) := by ring
      rw [hrearr]
      refine (abs_sub_le_abs_add_abs _ _).trans ?_
      have h1 := hprod j m j i k m
      have h2 := hprod k m j i j m
      calc |chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y| +
            |chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y|
          ≤ 2 * Clip * Mg * jet1 + 2 * Clip * Mg * jet1 := add_le_add h1 h2
        _ = 4 * Clip * Mg * jet1 := by ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) =>
      (Module.finrank ℝ E : ℝ) * (4 * Clip * Mg * jet1)) (fun j _ => ?_)) ?_
  · have hreorg : ∀ j : Fin (Module.finrank ℝ E),
        ((∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y)) -
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y))) =
          ∑ m : Fin (Module.finrank ℝ E),
            ((chartChristoffel (I := I) g₁ α j m j y *
                  chartChristoffel (I := I) g₁ α i k m y -
                chartChristoffel (I := I) g₁ α k m j y *
                  chartChristoffel (I := I) g₁ α i j m y) -
              (chartChristoffel (I := I) g₂ α j m j y *
                  chartChristoffel (I := I) g₂ α i k m y -
                chartChristoffel (I := I) g₂ α k m j y *
                  chartChristoffel (I := I) g₂ α i j m y)) := by
      intro j
      exact (Finset.sum_sub_distrib
        (f := fun m : Fin (Module.finrank ℝ E) =>
          chartChristoffel (I := I) g₁ α j m j y *
              chartChristoffel (I := I) g₁ α i k m y -
            chartChristoffel (I := I) g₁ α k m j y *
              chartChristoffel (I := I) g₁ α i j m y)
        (g := fun m : Fin (Module.finrank ℝ E) =>
          chartChristoffel (I := I) g₂ α j m j y *
              chartChristoffel (I := I) g₂ α i k m y -
            chartChristoffel (I := I) g₂ α k m j y *
              chartChristoffel (I := I) g₂ α i j m y)).symm
    rw [hreorg j]
    exact hinner j
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show 4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg * jet1 =
          (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) * (4 * Clip * Mg * jet1)) by ring]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicci_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ : ℝ) (hQ₁_nn : 0 ≤ Q₁)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (Q₂ : ℝ) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a q)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i k : Fin (Module.finrank ℝ E),
            |chartRicciTensor (I := I) (gSeq k₁) α i k (extChartAt I α b) -
              chartRicciTensor (I := I) (gSeq k₂) α i k (extChartAt I α b)| ≤
                C * chartMetricJet2DiffSup (I := I) (M := M)
                  (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨Clip, hClip_pos, hClip⟩ :=
    christoffel_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ hQ₁_nn hQ₁
  obtain ⟨Cdiff, hCdiff_pos, hCdiff⟩ :=
    christoffelD_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ hQ₁_nn hQ₁ Q₂ hQ₂_nn hQ₂
  obtain ⟨Mg, hMg_nn, hMg⟩ :=
    christoffel_pou_bnd (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ hQ₁_nn hQ₁
  let C : ℝ := 2 * (Module.finrank ℝ E : ℝ) * Cdiff +
    4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb i k
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1_le_jet2 : chartMetricJet1DiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b) ≤
        chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)
  have hCdiff' : ∀ m i j k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k₁) α i j k) (extChartAt I α b) -
        partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k₂) α i j k) (extChartAt I α b)| ≤
        Cdiff * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
    fun m i j k => hCdiff α hα k₁ k₂ b hb m i j k
  have hClip' : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₁) α i j k (extChartAt I α b) -
        chartChristoffel (I := I) (gSeq k₂) α i j k (extChartAt I α b)| ≤
        Clip * chartMetricJet1DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
    fun i j k => hClip α hα k₁ k₂ b hb i j k
  have hMg1 : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₁) α i j k (extChartAt I α b)| ≤ Mg :=
    fun i j k => hMg α hα k₁ b hb i j k
  have hMg2 : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₂) α i j k (extChartAt I α b)| ≤ Mg :=
    fun i j k => hMg α hα k₂ b hb i j k
  have h2nd := chartRicciSecondOrderTerm_sub_abs_le (I := I) (M := M)
    (gSeq k₁) (gSeq k₂) α hCdiff' i k
  have h1st := chartRicciFirstOrderTerm_sub_abs_le (I := I) (M := M)
    (gSeq k₁) (gSeq k₂) α hClip_pos.le hMg_nn hClip' hMg1 hMg2 i k
  have hsplit :
      chartRicciTensor (I := I) (gSeq k₁) α i k (extChartAt I α b) -
          chartRicciTensor (I := I) (gSeq k₂) α i k (extChartAt I α b) =
        (chartRicciSecondOrderTerm (I := I) (gSeq k₁) α i k (extChartAt I α b) -
          chartRicciSecondOrderTerm (I := I) (gSeq k₂) α i k (extChartAt I α b)) +
        (chartRicciFirstOrderTerm (I := I) (gSeq k₁) α i k (extChartAt I α b) -
          chartRicciFirstOrderTerm (I := I) (gSeq k₂) α i k (extChartAt I α b)) := by
    rw [chartRicciTensor_eq_secondOrder_add_firstOrder
        (I := I) (gSeq k₁) α i k (extChartAt I α b),
      chartRicciTensor_eq_secondOrder_add_firstOrder
        (I := I) (gSeq k₂) α i k (extChartAt I α b)]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M)
    (gSeq k₁) (gSeq k₂) α (extChartAt I α b) with hjet2_def
  have h1st' :
      |chartRicciFirstOrderTerm (I := I) (gSeq k₁) α i k (extChartAt I α b) -
        chartRicciFirstOrderTerm (I := I) (gSeq k₂) α i k (extChartAt I α b)| ≤
        4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg * jet2 := by
    refine h1st.trans ?_
    refine mul_le_mul_of_nonneg_left hjet1_le_jet2 ?_
    positivity
  calc
    |chartRicciSecondOrderTerm (I := I) (gSeq k₁) α i k (extChartAt I α b) -
          chartRicciSecondOrderTerm (I := I) (gSeq k₂) α i k (extChartAt I α b)| +
        |chartRicciFirstOrderTerm (I := I) (gSeq k₁) α i k (extChartAt I α b) -
          chartRicciFirstOrderTerm (I := I) (gSeq k₂) α i k (extChartAt I α b)|
      ≤ 2 * (Module.finrank ℝ E : ℝ) * Cdiff * jet2 +
          4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg * jet2 :=
        add_le_add h2nd h1st'
    _ ≤ C * jet2 := by
      dsimp [C]
      rw [add_mul, add_mul, one_mul]
      linarith

theorem exists_chartRicciTensor_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i k : Fin (Module.finrank ℝ E),
      |chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨Clip, hClip_pos, hClip⟩ :=
    exists_chartChristoffel_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK hKsub
  have hCdiff_each : ∀ m : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j k : Fin (Module.finrank ℝ E),
        |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
            partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
          C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := fun m =>
    exists_chartChristoffelDeriv_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α m hK hKsub
  choose Cm hCm_pos hCm using hCdiff_each
  set Cdiff : ℝ := Finset.univ.sup' Finset.univ_nonempty Cm with hCdiff_def
  have hCdiff_nn : 0 ≤ Cdiff :=
    le_trans (hCm_pos (Classical.arbitrary _)).le
      (Finset.le_sup' Cm (Finset.mem_univ (Classical.arbitrary _)))
  obtain ⟨Mg1, hMg1_nn, hMg1⟩ := exists_chartChristoffel_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨Mg2, hMg2_nn, hMg2⟩ := exists_chartChristoffel_bound_on_compact (I := I) g₂ α hK hKsub
  set Mg : ℝ := max Mg1 Mg2 with hMg_def
  have hMg_nn : 0 ≤ Mg := le_max_of_le_left hMg1_nn
  refine ⟨2 * (Module.finrank ℝ E : ℝ) * Cdiff +
      4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg + 1, ?_, ?_⟩
  · have h1 : 0 ≤ 2 * (Module.finrank ℝ E : ℝ) * Cdiff := by positivity
    have h2 : 0 ≤ 4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg := by
      have : 0 ≤ Clip := hClip_pos.le
      positivity
    linarith
  intro y hy i k
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1_le_jet2 : chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y
  have hCdiff : ∀ m i j k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
        Cdiff * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
    intro m i' j' k'
    refine (hCm m y hy i' j' k').trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.le_sup' Cm (Finset.mem_univ m)) hjet2_nn
  have hClip' : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y -
          chartChristoffel (I := I) g₂ α i j k y| ≤
        Clip * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y :=
    fun i' j' k' => hClip y hy i' j' k'
  have hMg1' : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y| ≤ Mg :=
    fun i' j' k' => (hMg1 y hy i' j' k').trans (le_max_left _ _)
  have hMg2' : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₂ α i j k y| ≤ Mg :=
    fun i' j' k' => (hMg2 y hy i' j' k').trans (le_max_right _ _)
  have h2nd := chartRicciSecondOrderTerm_sub_abs_le (I := I) (M := M) g₁ g₂ α
    hCdiff i k
  have h1st := chartRicciFirstOrderTerm_sub_abs_le (I := I) (M := M) g₁ g₂ α
    hClip_pos.le hMg_nn hClip' hMg1' hMg2' i k
  have hsplit :
      chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y =
        (chartRicciSecondOrderTerm (I := I) g₁ α i k y -
            chartRicciSecondOrderTerm (I := I) g₂ α i k y) +
          (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) := by
    rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₁ α i k y,
        chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₂ α i k y]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have h1st' : |chartRicciFirstOrderTerm (I := I) g₁ α i k y -
        chartRicciFirstOrderTerm (I := I) g₂ α i k y| ≤
      4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg * jet2 := by
    refine h1st.trans ?_
    refine mul_le_mul_of_nonneg_left hjet1_le_jet2 ?_
    have : 0 ≤ Clip := hClip_pos.le
    positivity
  calc |chartRicciSecondOrderTerm (I := I) g₁ α i k y -
            chartRicciSecondOrderTerm (I := I) g₂ α i k y| +
          |chartRicciFirstOrderTerm (I := I) g₁ α i k y -
            chartRicciFirstOrderTerm (I := I) g₂ α i k y|
      ≤ 2 * (Module.finrank ℝ E : ℝ) * Cdiff * jet2 +
          4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg * jet2 := add_le_add h2nd h1st'
    _ ≤ (2 * (Module.finrank ℝ E : ℝ) * Cdiff +
          4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg + 1) * jet2 := by
        rw [add_mul, add_mul, one_mul]
        have : 0 ≤ jet2 := hjet2_nn
        linarith

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
