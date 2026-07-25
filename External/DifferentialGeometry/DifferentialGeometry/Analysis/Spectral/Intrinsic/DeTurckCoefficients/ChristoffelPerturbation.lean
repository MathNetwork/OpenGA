import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.InverseGramPerturbation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.InvGramPerturbation
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def gramPartialDiffEntry (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) ×
      (Fin (Module.finrank ℝ E))) : ℝ :=
  |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₁ α p.1 p.2.2) y -
    partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₂ α p.1 p.2.2) y|

def chartGramPartialDiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p, gramPartialDiffEntry (I := I) (M := M) g₁ g₂ α y p

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramPartialDiffSup_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (a l b : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) a (chartGramOnE (I := I) g₁ α l b) y -
        partialDeriv (E := E) a (chartGramOnE (I := I) g₂ α l b) y| ≤
      chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  have h := Finset.single_le_sum
    (f := gramPartialDiffEntry (I := I) (M := M) g₁ g₂ α y)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (l, a, b))
  exact h

def gramPartial2DiffEntry (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) ×
      (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) : ℝ :=
  |partialDeriv (E := E) p.1
      (partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₁ α p.2.2.1 p.2.2.2)) y -
    partialDeriv (E := E) p.1
      (partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₂ α p.2.2.1 p.2.2.2)) y|

def chartGramPartial2DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p, gramPartial2DiffEntry (I := I) (M := M) g₁ g₂ α y p

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramPartial2DiffSup_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv2_chartGramOnE_sub_abs_le_partial2DiffSup
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (c a l b : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) c
          (partialDeriv (E := E) a (chartGramOnE (I := I) g₁ α l b)) y -
        partialDeriv (E := E) c
          (partialDeriv (E := E) a (chartGramOnE (I := I) g₂ α l b)) y| ≤
      chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  have h := Finset.single_le_sum
    (f := gramPartial2DiffEntry (I := I) (M := M) g₁ g₂ α y)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (c, a, l, b))
  exact h

def chartMetricJet1DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y)
    + chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y

def chartMetricJet2DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y
    + chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y

omit [NeZero (Module.finrank ℝ E)] in
lemma chartMetricJet1DiffSup_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (chartGramDiffSup_nonneg _ _ _ _)
    (chartGramPartialDiffSup_nonneg _ _ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartMetricJet2DiffSup_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (chartMetricJet1DiffSup_nonneg _ _ _ _)
    (chartGramPartial2DiffSup_nonneg _ _ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramDiffSup_le_jet1
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) ≤
      chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (chartGramPartialDiffSup_nonneg _ _ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramPartialDiffSup_le_jet1
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (chartGramDiffSup_nonneg _ _ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartMetricJet1DiffSup_le_jet2
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (chartGramPartial2DiffSup_nonneg _ _ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramPartial2DiffSup_le_jet2
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (chartMetricJet1DiffSup_nonneg _ _ _ _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma symm_mem_baseSet_of_mem_interior_target
    (α : M) {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hy_target : y ∈ (extChartAt I α).target := interior_subset hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsource

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma partialDeriv_contDiffOn_interior_of_contDiffOn
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f) (interior (extChartAt I α).target) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f) (interior (extChartAt I α).target) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (a l b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α
    ((chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset) a

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartInvGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (m k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α
    ((chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset) m

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial2_chartGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (c a l b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) c (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b)))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α
    (partial_chartGramOnE_contDiffOn_int (I := I) g α a l b) c

def gramBracket (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
    partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
    partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffel_eq_sum_invGramOnE_bracket
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y * gramBracket (I := I) g α i j l y := by
  rw [chartChristoffel_def]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma exists_bound_of_contDiffOn_interior
    {f : E → ℝ}
    (α : M)
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f y| ≤ C := by
  classical
  have hcont : ContinuousOn f K := (hf.continuousOn).mono hKsub
  by_cases hKne : K.Nonempty
  · have hcont_abs : ContinuousOn (fun y => |f y|) K :=
      continuous_abs.comp_continuousOn hcont
    obtain ⟨y₀, hy₀K, hy₀max⟩ := hK.exists_isMaxOn hKne hcont_abs
    refine ⟨|f y₀|, abs_nonneg _, fun y hy => hy₀max hy⟩
  · exact ⟨0, le_refl 0, fun y hy => absurd ⟨y, hy⟩ hKne⟩


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma exists_uniform_bound_of_family
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (α : M) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i, |f i y| ≤ C := by
  classical
  have hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f i y| ≤ C := fun i =>
    exists_bound_of_contDiffOn_interior (I := I) α (hf i) hK hKsub
  choose C hC_nn hC_bd using hbound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty C, ?_, ?_⟩
  · exact le_trans (hC_nn (Classical.arbitrary ι))
      (Finset.le_sup' C (Finset.mem_univ (Classical.arbitrary ι)))
  · intro y hy i
    exact (hC_bd i y hy).trans (Finset.le_sup' C (Finset.mem_univ i))

private lemma exists_chartInvGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α k l y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) =>
      chartInvGramOnE (I := I) g α p.1 p.2)
    (fun p => (chartInvGramOnE_contDiffOn (I := I) g α p.1 p.2).mono interior_subset) hK hKsub
  exact ⟨C, hC_nn, fun y hy k l => hC y hy (k, l)⟩

private lemma exists_gramBracket_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i j l : Fin (Module.finrank ℝ E),
      |gramBracket (I := I) g α i j l y| ≤ C := by
  classical
  have hbracket_smooth : ∀ p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (gramBracket (I := I) g α p.1.1 p.1.2 p.2)
        (interior (extChartAt I α).target) := by
    intro p
    refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partial_chartGramOnE_contDiffOn_int (I := I) g α p.1.1 p.2 p.1.2
    · exact partial_chartGramOnE_contDiffOn_int (I := I) g α p.1.2 p.2 p.1.1
    · exact partial_chartGramOnE_contDiffOn_int (I := I) g α p.2 p.1.1 p.1.2
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) => gramBracket (I := I) g α p.1.1 p.1.2 p.2)
    hbracket_smooth hK hKsub
  exact ⟨C, hC_nn, fun y hy i j l => hC y hy ((i, j), l)⟩

private lemma exists_partialDeriv_chartInvGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m k l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      partialDeriv (E := E) p.1.1 (chartInvGramOnE (I := I) g α p.1.2 p.2))
    (fun p => partial_chartInvGramOnE_contDiffOn_int (I := I) g α p.1.1 p.1.2 p.2) hK hKsub
  exact ⟨C, hC_nn, fun y hy m k l => hC y hy ((m, k), l)⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Cinv M_b P : ℝ}
    (hP_nn : 0 ≤ P) (hMb_nn : 0 ≤ M_b)
    (hMb : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b)
    (hP : ∀ i j l : Fin (Module.finrank ℝ E),
      |gramBracket (I := I) g₁ α i j l y| ≤ P)
    (hCinv : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (hCinv_nn : 0 ≤ Cinv)
    (i j k : Fin (Module.finrank ℝ E)) :
    |chartChristoffel (I := I) g₁ α i j k y - chartChristoffel (I := I) g₂ α i j k y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) *
        chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartChristoffel_eq_sum_invGramOnE_bracket, chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  set jet1 : ℝ := chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := chartMetricJet1DiffSup_nonneg _ _ _ _
  rw [show (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) * jet1 =
        (1 / 2 : ℝ) * ((Module.finrank ℝ E : ℝ) * ((Cinv * P + 3 * M_b) * jet1)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1/2)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) => (Cinv * P + 3 * M_b) * jet1)
    (fun l _ => ?_)) ?_
  · have hsplit :
        chartInvGramOnE (I := I) g₁ α k l y * gramBracket (I := I) g₁ α i j l y -
          chartInvGramOnE (I := I) g₂ α k l y * gramBracket (I := I) g₂ α i j l y =
        (chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
            gramBracket (I := I) g₁ α i j l y +
          chartInvGramOnE (I := I) g₂ α k l y *
            (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y) := by
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have hbracketDiff :
        |gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y| ≤
          3 * chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y := by
      have h1 := partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
        g₁ g₂ α y i l j
      have h2 := partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
        g₁ g₂ α y j l i
      have h3 := partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
        g₁ g₂ α y l i j
      set d1 : ℝ := partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j) y -
        partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y with hd1
      set d2 : ℝ := partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i) y -
        partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y with hd2
      set d3 : ℝ := partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j) y -
        partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y with hd3
      have hbrk_eq :
          gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y =
            d1 + d2 - d3 := by
        simp only [hd1, hd2, hd3, gramBracket]; ring
      have htri : |d1 + d2 - d3| ≤ |d1| + |d2| + |d3| := by
        calc |d1 + d2 - d3| = |d1 + d2 + (-d3)| := by ring_nf
          _ ≤ |d1 + d2| + |(-d3)| := abs_add_le _ _
          _ ≤ (|d1| + |d2|) + |(-d3)| := by gcongr; exact abs_add_le _ _
          _ = |d1| + |d2| + |d3| := by rw [abs_neg]
      rw [hbrk_eq]
      calc |d1 + d2 - d3| ≤ |d1| + |d2| + |d3| := htri
        _ ≤ chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y +
              chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y +
              chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y :=
            add_le_add (add_le_add h1 h2) h3
        _ = 3 * chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y := by ring
    have hsum1 :
        |(chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
            gramBracket (I := I) g₁ α i j l y| ≤
          Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) * P := by
      rw [abs_mul]
      refine mul_le_mul (hCinv k l) (hP i j l) (abs_nonneg _)
        (mul_nonneg hCinv_nn (chartGramDiffSup_nonneg _ _ _ _))
    have hsum2 :
        |chartInvGramOnE (I := I) g₂ α k l y *
            (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y)| ≤
          M_b * (3 * chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y) := by
      rw [abs_mul]
      refine mul_le_mul (hMb k l) hbracketDiff (abs_nonneg _) hMb_nn
    refine (add_le_add hsum1 hsum2).trans ?_
    have hgram_le : chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) ≤
        jet1 := chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y
    have hpartial_le : 3 * chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y ≤ 3 * jet1 :=
      mul_le_mul_of_nonneg_left (chartGramPartialDiffSup_le_jet1 _ _ _ _) (by norm_num)
    calc Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) * P +
            M_b * (3 * chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y)
        ≤ Cinv * jet1 * P + M_b * (3 * jet1) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul_of_nonneg_right ?_ hP_nn
            exact mul_le_mul_of_nonneg_left hgram_le hCinv_nn
          · exact mul_le_mul_of_nonneg_left hpartial_le hMb_nn
      _ = (Cinv * P + 3 * M_b) * jet1 := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

theorem exists_chartChristoffel_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y - chartChristoffel (I := I) g₂ α i j k y| ≤
        C * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  have hKsub_target : K ⊆ (extChartAt I α).target := hKsub.trans interior_subset
  set K' : Set M := (extChartAt I α).symm '' K with hK'_def
  have hK'_compact : IsCompact K' :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) α).mono hKsub_target)
  have hK'_sub : K' ⊆ (chartAt H α).source := by
    rintro x ⟨y, hyK, rfl⟩
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (hKsub_target hyK)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  obtain ⟨Cinv, hCinv_pos, hCinv⟩ :=
    exists_chartInvGramMatrix_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK'_compact hK'_sub
  obtain ⟨M_b, hMb_nn, hMb⟩ :=
    exists_chartInvGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  obtain ⟨P, hP_nn, hP⟩ :=
    exists_gramBracket_bound_on_compact (I := I) g₁ α hK hKsub
  refine ⟨(1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) := by
      refine mul_nonneg (mul_nonneg (by norm_num) (by positivity)) ?_
      have : 0 ≤ Cinv * P := mul_nonneg hCinv_pos.le hP_nn
      linarith
    linarith
  intro y hy i j k
  have hxy_mem : (extChartAt I α).symm y ∈ K' := ⟨y, hy, rfl⟩
  have hCinv' : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) := by
    intro k l
    have h := hCinv ((extChartAt I α).symm y) hxy_mem k l
    simpa only [chartInvGramOnE_def] using h
  have h_pt := chartChristoffel_sub_abs_le (I := I) (M := M) g₁ g₂ α
    hP_nn hMb_nn (fun k l => hMb y hy k l) (fun i j l => hP y hy i j l)
    hCinv' hCinv_pos.le i j k
  have hjet1_nn : 0 ≤ chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet1DiffSup_nonneg _ _ _ _
  refine h_pt.trans ?_
  refine mul_le_mul_of_nonneg_right (by linarith) hjet1_nn

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartInvGramOnE_differentiableAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (k l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k l) y := by
  have hcd : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (interior (extChartAt I α).target) :=
    (chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset
  exact (hcd.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartGramOnE_differentiableAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (a l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b)) y := by
  exact ((partial_chartGramOnE_contDiffOn_int (I := I) g α a l b).contDiffAt
    (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramBracket_differentiableAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (i j l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (gramBracket (I := I) g α i j l) y := by
  have h1 := partial_chartGramOnE_differentiableAt_int (I := I) g α i l j hy
  have h2 := partial_chartGramOnE_differentiableAt_int (I := I) g α j l i hy
  have h3 := partial_chartGramOnE_differentiableAt_int (I := I) g α l i j hy
  exact (h1.add h2).sub h3

def gramBracketDeriv (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y +
    partialDeriv (E := E) m (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) y -
    partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_gramBracket_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (gramBracket (I := I) g α i j l) y =
      gramBracketDeriv (I := I) g α m i j l y := by
  have h1 := partial_chartGramOnE_differentiableAt_int (I := I) g α i l j hy
  have h2 := partial_chartGramOnE_differentiableAt_int (I := I) g α j l i hy
  have h3 := partial_chartGramOnE_differentiableAt_int (I := I) g α l i j hy
  unfold gramBracket gramBracketDeriv
  rw [partialDeriv_sub (i := m) (fun y => partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
        partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y)
      (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) (h1.add h2) h3,
    partialDeriv_add (i := m) (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) h1 h2]

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartChristoffel_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracket (I := I) g α i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv (I := I) g α m i j l y) := by
  classical
  have heq : chartChristoffel (I := I) g α i j k =
      fun z : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l z * gramBracket (I := I) g α i j l z := by
    funext z
    exact chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g α i j k z
  rw [show partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y =
        partialDeriv (E := E) m
          (fun z : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l z * gramBracket (I := I) g α i j l z) y from by
    rw [heq]]
  have hsum_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun z : E => chartInvGramOnE (I := I) g α k l z * gramBracket (I := I) g α i j l z) y :=
    fun l => (chartInvGramOnE_differentiableAt_int (I := I) g α k l hy).mul
      (gramBracket_differentiableAt_int (I := I) g α i j l hy)
  rw [partialDeriv_const_mul (i := m) (1 / 2 : ℝ)
      (fun z : E => ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l z * gramBracket (I := I) g α i j l z)
      (DifferentiableAt.fun_sum (fun l _ => hsum_diff l))]
  congr 1
  rw [partialDeriv_sum (i := m) Finset.univ
      (fun l => fun z : E => chartInvGramOnE (I := I) g α k l z * gramBracket (I := I) g α i j l z)
      (fun l _ => hsum_diff l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_mul (i := m) (chartInvGramOnE (I := I) g α k l)
      (gramBracket (I := I) g α i j l)
      (chartInvGramOnE_differentiableAt_int (I := I) g α k l hy)
      (gramBracket_differentiableAt_int (I := I) g α i j l hy),
    partialDeriv_gramBracket_eq (I := I) g α m i j l hy]

private lemma abs_triple_prod_sub_le (A₁ A₂ B₁ B₂ C₁ C₂ : ℝ) :
    |A₁ * B₁ * C₁ - A₂ * B₂ * C₂| ≤
      |A₁ - A₂| * |B₁| * |C₁| + |A₂| * |B₁ - B₂| * |C₁| +
        |A₂| * |B₂| * |C₁ - C₂| := by
  have hsplit : A₁ * B₁ * C₁ - A₂ * B₂ * C₂ =
      (A₁ - A₂) * B₁ * C₁ + A₂ * (B₁ - B₂) * C₁ + A₂ * B₂ * (C₁ - C₂) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans ?_) (le_of_eq ?_)
  · refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
    · rw [abs_mul, abs_mul]
    · rw [abs_mul, abs_mul]
  · rw [abs_mul, abs_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartInvGramOnE_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {Cinv M_b Q : ℝ}
    (hMb_nn : 0 ≤ M_b) (hQ_nn : 0 ≤ Q) (hCinv_nn : 0 ≤ Cinv)
    (hMb1 : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y| ≤ M_b)
    (hMb2 : ∀ k l, |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b)
    (hQ : ∀ m a b, |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| ≤ Q)
    (hCinv : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y -
        chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (m k l : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
        partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) *
        chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [partialDeriv_chartInvGramOnE_eq (I := I) g₁ α y m k l hy,
    partialDeriv_chartInvGramOnE_eq (I := I) g₂ α y m k l hy]
  rw [neg_sub_neg, abs_sub_comm, ← Finset.sum_sub_distrib]
  set jet1 : ℝ := chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := chartMetricJet1DiffSup_nonneg _ _ _ _
  set gd : ℝ := chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) with hgd
  have hgd_le : gd ≤ jet1 := chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y
  have hgd_nn : 0 ≤ gd := chartGramDiffSup_nonneg _ _ _ _
  have hterm : ∀ a : Fin (Module.finrank ℝ E),
      |(∑ b : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g₁ α k a y *
            chartInvGramOnE (I := I) g₁ α b l y *
            partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y) -
        (∑ b : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g₂ α k a y *
            chartInvGramOnE (I := I) g₂ α b l y *
            partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y)| ≤
        (Module.finrank ℝ E : ℝ) * ((2 * Cinv * M_b * Q + M_b ^ 2) * jet1) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
      (2 * Cinv * M_b * Q + M_b ^ 2) * jet1) (fun b _ => ?_)) ?_
    · have htp := abs_triple_prod_sub_le
        (chartInvGramOnE (I := I) g₁ α k a y) (chartInvGramOnE (I := I) g₂ α k a y)
        (chartInvGramOnE (I := I) g₁ α b l y) (chartInvGramOnE (I := I) g₂ α b l y)
        (partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y)
        (partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y)
      refine htp.trans ?_
      have hC_ka : |chartInvGramOnE (I := I) g₁ α k a y -
          chartInvGramOnE (I := I) g₂ α k a y| ≤ Cinv * gd := hCinv k a
      have hC_bl : |chartInvGramOnE (I := I) g₁ α b l y -
          chartInvGramOnE (I := I) g₂ α b l y| ≤ Cinv * gd := hCinv b l
      have hP_ab : |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
          partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y| ≤
          chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y :=
        partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M) g₁ g₂ α y m a b
      have hP_ab' : |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
          partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y| ≤ jet1 :=
        hP_ab.trans (chartGramPartialDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y)
      have ht1 : |chartInvGramOnE (I := I) g₁ α k a y - chartInvGramOnE (I := I) g₂ α k a y| *
            |chartInvGramOnE (I := I) g₁ α b l y| *
            |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| ≤
          Cinv * M_b * Q * jet1 := by
        calc |chartInvGramOnE (I := I) g₁ α k a y - chartInvGramOnE (I := I) g₂ α k a y| *
                |chartInvGramOnE (I := I) g₁ α b l y| *
                |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y|
            ≤ (Cinv * gd) * M_b * Q := by
              refine mul_le_mul (mul_le_mul hC_ka (hMb1 b l) (abs_nonneg _)
                (mul_nonneg hCinv_nn hgd_nn)) (hQ m a b) (abs_nonneg _) ?_
              exact mul_nonneg (mul_nonneg hCinv_nn hgd_nn) hMb_nn
          _ = Cinv * M_b * Q * gd := by ring
          _ ≤ Cinv * M_b * Q * jet1 :=
              mul_le_mul_of_nonneg_left hgd_le
                (mul_nonneg (mul_nonneg hCinv_nn hMb_nn) hQ_nn)
      have ht2 : |chartInvGramOnE (I := I) g₂ α k a y| *
            |chartInvGramOnE (I := I) g₁ α b l y - chartInvGramOnE (I := I) g₂ α b l y| *
            |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| ≤
          Cinv * M_b * Q * jet1 := by
        calc |chartInvGramOnE (I := I) g₂ α k a y| *
                |chartInvGramOnE (I := I) g₁ α b l y - chartInvGramOnE (I := I) g₂ α b l y| *
                |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y|
            ≤ M_b * (Cinv * gd) * Q := by
              refine mul_le_mul (mul_le_mul (hMb2 k a) hC_bl (abs_nonneg _) hMb_nn)
                (hQ m a b) (abs_nonneg _) ?_
              exact mul_nonneg hMb_nn (mul_nonneg hCinv_nn hgd_nn)
          _ = Cinv * M_b * Q * gd := by ring
          _ ≤ Cinv * M_b * Q * jet1 :=
              mul_le_mul_of_nonneg_left hgd_le
                (mul_nonneg (mul_nonneg hCinv_nn hMb_nn) hQ_nn)
      have ht3 : |chartInvGramOnE (I := I) g₂ α k a y| *
            |chartInvGramOnE (I := I) g₂ α b l y| *
            |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
              partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y| ≤
          M_b ^ 2 * jet1 := by
        calc |chartInvGramOnE (I := I) g₂ α k a y| *
                |chartInvGramOnE (I := I) g₂ α b l y| *
                |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
                  partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y|
            ≤ M_b * M_b * jet1 := by
              refine mul_le_mul (mul_le_mul (hMb2 k a) (hMb2 b l) (abs_nonneg _) hMb_nn)
                hP_ab' (abs_nonneg _) (mul_nonneg hMb_nn hMb_nn)
          _ = M_b ^ 2 * jet1 := by ring
      calc |chartInvGramOnE (I := I) g₁ α k a y - chartInvGramOnE (I := I) g₂ α k a y| *
              |chartInvGramOnE (I := I) g₁ α b l y| *
              |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| +
            |chartInvGramOnE (I := I) g₂ α k a y| *
              |chartInvGramOnE (I := I) g₁ α b l y - chartInvGramOnE (I := I) g₂ α b l y| *
              |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| +
            |chartInvGramOnE (I := I) g₂ α k a y| *
              |chartInvGramOnE (I := I) g₂ α b l y| *
              |partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
                partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y|
          ≤ Cinv * M_b * Q * jet1 + Cinv * M_b * Q * jet1 + M_b ^ 2 * jet1 :=
            add_le_add (add_le_add ht1 ht2) ht3
        _ = (2 * Cinv * M_b * Q + M_b ^ 2) * jet1 := by ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
    (Module.finrank ℝ E : ℝ) * ((2 * Cinv * M_b * Q + M_b ^ 2) * jet1)) (fun a _ => hterm a)) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) * jet1 =
        (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * ((2 * Cinv * M_b * Q + M_b ^ 2) * jet1)) by ring]

omit [NeZero (Module.finrank ℝ E)] in
lemma gramBracketDeriv_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (m i j l : Fin (Module.finrank ℝ E)) :
    |gramBracketDeriv (I := I) g₁ α m i j l y -
        gramBracketDeriv (I := I) g₂ α m i j l y| ≤
      3 * chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  have h1 := partialDeriv2_chartGramOnE_sub_abs_le_partial2DiffSup (I := I) (M := M)
    g₁ g₂ α y m i l j
  have h2 := partialDeriv2_chartGramOnE_sub_abs_le_partial2DiffSup (I := I) (M := M)
    g₁ g₂ α y m j l i
  have h3 := partialDeriv2_chartGramOnE_sub_abs_le_partial2DiffSup (I := I) (M := M)
    g₁ g₂ α y m l i j
  set e1 : ℝ := partialDeriv (E := E) m
      (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j)) y -
    partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j)) y with he1
  set e2 : ℝ := partialDeriv (E := E) m
      (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i)) y -
    partialDeriv (E := E) m (partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i)) y with he2
  set e3 : ℝ := partialDeriv (E := E) m
      (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j)) y -
    partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j)) y with he3
  have heq : gramBracketDeriv (I := I) g₁ α m i j l y -
      gramBracketDeriv (I := I) g₂ α m i j l y = e1 + e2 - e3 := by
    simp only [he1, he2, he3, gramBracketDeriv]; ring
  rw [heq]
  calc |e1 + e2 - e3| = |e1 + e2 + (-e3)| := by ring_nf
    _ ≤ |e1 + e2| + |(-e3)| := abs_add_le _ _
    _ ≤ (|e1| + |e2|) + |(-e3)| := by gcongr; exact abs_add_le _ _
    _ = |e1| + |e2| + |e3| := by rw [abs_neg]
    _ ≤ chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y +
          chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y +
          chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y :=
        add_le_add (add_le_add h1 h2) h3
    _ = 3 * chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y := by ring

private lemma exists_gramBracketDeriv_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m i j l : Fin (Module.finrank ℝ E),
      |gramBracketDeriv (I := I) g α m i j l y| ≤ C := by
  classical
  have hsmooth : ∀ p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (gramBracketDeriv (I := I) g α p.1.1.1 p.1.1.2 p.1.2 p.2)
        (interior (extChartAt I α).target) := by
    intro p
    refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partial2_chartGramOnE_contDiffOn_int (I := I) g α p.1.1.1 p.1.1.2 p.2 p.1.2
    · exact partial2_chartGramOnE_contDiffOn_int (I := I) g α p.1.1.1 p.1.2 p.2 p.1.1.2
    · exact partial2_chartGramOnE_contDiffOn_int (I := I) g α p.1.1.1 p.2 p.1.1.2 p.1.2
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)) =>
      gramBracketDeriv (I := I) g α p.1.1.1 p.1.1.2 p.1.2 p.2)
    hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy m i j l => hC y hy (((m, i), j), l)⟩

private lemma exists_partial_chartGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartGramOnE (I := I) g α a b) y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      partialDeriv (E := E) p.1.1 (chartGramOnE (I := I) g α p.1.2 p.2))
    (fun p => partial_chartGramOnE_contDiffOn_int (I := I) g α p.1.1 p.1.2 p.2) hK hKsub
  exact ⟨C, hC_nn, fun y hy m a b => hC y hy ((m, a), b)⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartChristoffel_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {Cd Cinv M_b P D R : ℝ}
    (hCd_nn : 0 ≤ Cd) (hCinv_nn : 0 ≤ Cinv) (hMb_nn : 0 ≤ M_b)
    (hP_nn : 0 ≤ P) (hD_nn : 0 ≤ D) (hR_nn : 0 ≤ R)
    (m i j k : Fin (Module.finrank ℝ E))
    (hCd : ∀ k l, |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
        partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤
        Cd * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y)
    (hMb2 : ∀ k l, |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b)
    (hP : ∀ i j l, |gramBracket (I := I) g₁ α i j l y| ≤ P)
    (hD : ∀ k l, |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤ D)
    (hR : ∀ i j l, |gramBracketDeriv (I := I) g₁ α m i j l y| ≤ R)
    (hCinv : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y -
        chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y)) :
    |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        (Cd * P + 3 * D + Cinv * R + 3 * M_b) *
        chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [partialDeriv_chartChristoffel_eq (I := I) g₁ α m i j k hy,
    partialDeriv_chartChristoffel_eq (I := I) g₂ α m i j k hy,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hjet2_nn : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  set jet1 : ℝ := chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_le : jet1 ≤ jet2 := chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y
  have hjet1_nn : 0 ≤ jet1 := chartMetricJet1DiffSup_nonneg _ _ _ _
  set gd : ℝ := chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) with hgd
  have hgd_nn : 0 ≤ gd := chartGramDiffSup_nonneg _ _ _ _
  have hgd_le2 : gd ≤ jet2 :=
    le_trans (chartGramDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y) hjet1_le
  rw [show (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        (Cd * P + 3 * D + Cinv * R + 3 * M_b) * jet2 =
      (1 / 2 : ℝ) * ((Module.finrank ℝ E : ℝ) *
        ((Cd * P + 3 * D + Cinv * R + 3 * M_b) * jet2)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1/2)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) =>
      (Cd * P + 3 * D + Cinv * R + 3 * M_b) * jet2) (fun l _ => ?_)) ?_
  · have hsplit :
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y *
              gramBracket (I := I) g₁ α i j l y +
            chartInvGramOnE (I := I) g₁ α k l y *
              gramBracketDeriv (I := I) g₁ α m i j l y) -
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
              gramBracket (I := I) g₂ α i j l y +
            chartInvGramOnE (I := I) g₂ α k l y *
              gramBracketDeriv (I := I) g₂ α m i j l y) =
        ((partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y) *
              gramBracket (I := I) g₁ α i j l y +
            partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
              (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y)) +
          ((chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
              gramBracketDeriv (I := I) g₁ α m i j l y +
            chartInvGramOnE (I := I) g₂ α k l y *
              (gramBracketDeriv (I := I) g₁ α m i j l y -
                gramBracketDeriv (I := I) g₂ α m i j l y)) := by ring
    rw [hsplit]
    have hA1 : |(partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y) *
          gramBracket (I := I) g₁ α i j l y| ≤ Cd * P * jet2 := by
      rw [abs_mul]
      calc |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| *
            |gramBracket (I := I) g₁ α i j l y|
          ≤ (Cd * jet1) * P := mul_le_mul (hCd k l) (hP i j l) (abs_nonneg _)
              (mul_nonneg hCd_nn hjet1_nn)
        _ = Cd * P * jet1 := by ring
        _ ≤ Cd * P * jet2 := mul_le_mul_of_nonneg_left hjet1_le (mul_nonneg hCd_nn hP_nn)
    have hA2 : |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
          (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y)| ≤
          3 * D * jet2 := by
      rw [abs_mul]
      have hbrkdiff : |gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y| ≤
          3 * jet2 := by
        have h1 := partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
          g₁ g₂ α y i l j
        have h2 := partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
          g₁ g₂ α y j l i
        have h3 := partialDeriv_chartGramOnE_sub_abs_le_partialDiffSup (I := I) (M := M)
          g₁ g₂ α y l i j
        have hps_le2 : chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y ≤ jet2 :=
          le_trans (chartGramPartialDiffSup_le_jet1 (I := I) (M := M) g₁ g₂ α y) hjet1_le
        set d1 : ℝ := partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j) y -
          partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y with hd1
        set d2 : ℝ := partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i) y -
          partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y with hd2
        set d3 : ℝ := partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y with hd3
        have hbrk_eq : gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y =
            d1 + d2 - d3 := by simp only [hd1, hd2, hd3, gramBracket]; ring
        rw [hbrk_eq]
        calc |d1 + d2 - d3| = |d1 + d2 + (-d3)| := by ring_nf
          _ ≤ |d1 + d2| + |(-d3)| := abs_add_le _ _
          _ ≤ (|d1| + |d2|) + |(-d3)| := by gcongr; exact abs_add_le _ _
          _ = |d1| + |d2| + |d3| := by rw [abs_neg]
          _ ≤ jet2 + jet2 + jet2 :=
              add_le_add (add_le_add (h1.trans hps_le2) (h2.trans hps_le2)) (h3.trans hps_le2)
          _ = 3 * jet2 := by ring
      calc |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| *
            |gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y|
          ≤ D * (3 * jet2) := mul_le_mul (hD k l) hbrkdiff (abs_nonneg _) hD_nn
        _ = 3 * D * jet2 := by ring
    have hB1 : |(chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
          gramBracketDeriv (I := I) g₁ α m i j l y| ≤ Cinv * R * jet2 := by
      rw [abs_mul]
      calc |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| *
            |gramBracketDeriv (I := I) g₁ α m i j l y|
          ≤ (Cinv * gd) * R := mul_le_mul (hCinv k l) (hR i j l) (abs_nonneg _)
              (mul_nonneg hCinv_nn hgd_nn)
        _ = Cinv * R * gd := by ring
        _ ≤ Cinv * R * jet2 := mul_le_mul_of_nonneg_left hgd_le2 (mul_nonneg hCinv_nn hR_nn)
    have hB2 : |chartInvGramOnE (I := I) g₂ α k l y *
          (gramBracketDeriv (I := I) g₁ α m i j l y -
            gramBracketDeriv (I := I) g₂ α m i j l y)| ≤ 3 * M_b * jet2 := by
      rw [abs_mul]
      have hbdderiv : |gramBracketDeriv (I := I) g₁ α m i j l y -
          gramBracketDeriv (I := I) g₂ α m i j l y| ≤ 3 * jet2 := by
        refine (gramBracketDeriv_sub_abs_le (I := I) (M := M) g₁ g₂ α y m i j l).trans ?_
        have hp2_le2 : chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y ≤ jet2 :=
          chartGramPartial2DiffSup_le_jet2 (I := I) (M := M) g₁ g₂ α y
        exact mul_le_mul_of_nonneg_left hp2_le2 (by norm_num)
      calc |chartInvGramOnE (I := I) g₂ α k l y| *
            |gramBracketDeriv (I := I) g₁ α m i j l y -
              gramBracketDeriv (I := I) g₂ α m i j l y|
          ≤ M_b * (3 * jet2) := mul_le_mul (hMb2 k l) hbdderiv (abs_nonneg _) hMb_nn
        _ = 3 * M_b * jet2 := by ring
    refine (abs_add_le _ _).trans ?_
    refine le_trans (add_le_add ((abs_add_le _ _).trans (add_le_add hA1 hA2))
      ((abs_add_le _ _).trans (add_le_add hB1 hB2))) (le_of_eq ?_)
    ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

theorem exists_chartChristoffelDeriv_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j k : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
          partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  have hKsub_target : K ⊆ (extChartAt I α).target := hKsub.trans interior_subset
  set K' : Set M := (extChartAt I α).symm '' K with hK'_def
  have hK'_compact : IsCompact K' :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) α).mono hKsub_target)
  have hK'_sub : K' ⊆ (chartAt H α).source := by
    rintro x ⟨z, hzK, rfl⟩
    have hsource : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (hKsub_target hzK)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  obtain ⟨Cinv, hCinv_pos, hCinv⟩ :=
    exists_chartInvGramMatrix_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK'_compact hK'_sub
  obtain ⟨Mb1, hMb1_nn, hMb1⟩ := exists_chartInvGramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨Mb2, hMb2_nn, hMb2⟩ := exists_chartInvGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  set M_b : ℝ := max Mb1 Mb2 with hMb_def
  have hMb_nn : 0 ≤ M_b := le_max_of_le_left hMb1_nn
  obtain ⟨Q, hQ_nn, hQ⟩ := exists_partial_chartGramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨P, hP_nn, hP⟩ := exists_gramBracket_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨D, hD_nn, hD⟩ :=
    exists_partialDeriv_chartInvGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  obtain ⟨R, hR_nn, hR⟩ := exists_gramBracketDeriv_bound_on_compact (I := I) g₁ α hK hKsub
  set Cd : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) with hCd_def
  have hCd_nn : 0 ≤ Cd := by
    refine mul_nonneg (by positivity) ?_
    have : 0 ≤ 2 * Cinv * M_b * Q := by positivity
    have hsq : 0 ≤ M_b ^ 2 := sq_nonneg _
    linarith
  refine ⟨(1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
      (Cd * P + 3 * D + Cinv * R + 3 * M_b) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        (Cd * P + 3 * D + Cinv * R + 3 * M_b) := by
      refine mul_nonneg (mul_nonneg (by norm_num) (by positivity)) ?_
      have h1 : 0 ≤ Cd * P := mul_nonneg hCd_nn hP_nn
      have h2 : 0 ≤ Cinv * R := mul_nonneg hCinv_pos.le hR_nn
      linarith
    linarith
  intro y hy i j k
  have hy_int : y ∈ interior (extChartAt I α).target := hKsub hy
  have hxy_mem : (extChartAt I α).symm y ∈ K' := ⟨y, hy, rfl⟩
  have hCinv' : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) := by
    intro k l
    simpa only [chartInvGramOnE_def] using hCinv ((extChartAt I α).symm y) hxy_mem k l
  have hMb1' : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y| ≤ M_b :=
    fun k l => (hMb1 y hy k l).trans (le_max_left _ _)
  have hMb2' : ∀ k l, |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b :=
    fun k l => (hMb2 y hy k l).trans (le_max_right _ _)
  have hCd : ∀ k l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤
        Cd * chartMetricJet1DiffSup (I := I) (M := M) g₁ g₂ α y := by
    intro k l
    exact partialDeriv_chartInvGramOnE_sub_abs_le (I := I) (M := M) g₁ g₂ α hy_int
      hMb_nn hQ_nn hCinv_pos.le hMb1' hMb2' (fun m a b => hQ y hy m a b) hCinv' m k l
  have h_pt := partialDeriv_chartChristoffel_sub_abs_le (I := I) (M := M) g₁ g₂ α hy_int
    hCd_nn hCinv_pos.le hMb_nn hP_nn hD_nn hR_nn m i j k
    hCd hMb2' (fun i j l => hP y hy i j l) (fun k l => hD y hy m k l)
    (fun i j l => hR y hy m i j l) hCinv'
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  refine h_pt.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hjet2_nn

private lemma abs_add_sub_le (A B C : ℝ) :
    |A + B - C| ≤ |A| + |B| + |C| := by
  calc
    |A + B - C| = |A + B + (-C)| := by ring_nf
    _ ≤ |A + B| + |(-C)| := abs_add_le _ _
    _ ≤ (|A| + |B|) + |(-C)| := by gcongr; exact abs_add_le _ _
    _ = |A| + |B| + |C| := by rw [abs_neg]

omit [NeZero (Module.finrank ℝ E)] in

theorem gramBracket_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E) {Q : ℝ}
    (hQ : ∀ m a c, |partialDeriv (E := E) m
      (chartGramOnE (I := I) g α a c) y| ≤ Q)
    (i j l : Fin (Module.finrank ℝ E)) :
    |gramBracket (I := I) g α i j l y| ≤ 3 * Q := by
  unfold gramBracket
  exact (abs_add_sub_le _ _ _).trans <| by
    calc
      |partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y| +
            |partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y| +
            |partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y|
          ≤ Q + Q + Q := add_le_add (add_le_add (hQ i l j) (hQ j l i)) (hQ l i j)
      _ = 3 * Q := by ring



omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E)
    (i j k : Fin (Module.finrank ℝ E)) {M_b Q : ℝ}
    (hMb_nn : 0 ≤ M_b)
    (hMb : ∀ l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α k l y| ≤ M_b)
    (hQ : ∀ l : Fin (Module.finrank ℝ E),
      |gramBracket (I := I) g α i j l y| ≤ Q) :
    |chartChristoffel (I := I) g α i j k y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * M_b * Q := by
  classical
  rw [chartChristoffel_eq_sum_invGramOnE_bracket, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y * gramBracket (I := I) g α i j l y| ≤
        ∑ _l : Fin (Module.finrank ℝ E), M_b * Q := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hMb l) (hQ l) (abs_nonneg _) hMb_nn
  calc
    (1 / 2 : ℝ) *
        |∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y * gramBracket (I := I) g α i j l y|
        ≤ (1 / 2 : ℝ) * ∑ _l : Fin (Module.finrank ℝ E), M_b * Q :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * M_b * Q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [NeZero (Module.finrank ℝ E)] in
theorem gramBracketD_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E) {Q : ℝ}
    (hQ : ∀ c m a q, |partialDeriv (E := E) c
      (partialDeriv (E := E) m (chartGramOnE (I := I) g α a q)) y| ≤ Q)
    (c i j l : Fin (Module.finrank ℝ E)) :
    |gramBracketDeriv (I := I) g α c i j l y| ≤ 3 * Q := by
  unfold gramBracketDeriv
  exact (abs_add_sub_le _ _ _).trans <| by
    calc
      |partialDeriv (E := E) c
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y| +
          |partialDeriv (E := E) c
            (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) y| +
          |partialDeriv (E := E) c
            (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y|
        ≤ Q + Q + Q := add_le_add
          (add_le_add (hQ c i l j) (hQ c j l i)) (hQ c l i j)
      _ = 3 * Q := by ring




omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {M_b Q : ℝ} (hMb_nn : 0 ≤ M_b)
    (hMb : ∀ a c, |chartInvGramOnE (I := I) g α a c y| ≤ M_b)
    (hQ : ∀ m a c, |partialDeriv (E := E) m
      (chartGramOnE (I := I) g α a c) y| ≤ Q)
    (m p q : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) m (chartInvGramOnE (I := I) g α p q) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q := by
  classical
  rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y m p q hy, abs_neg]
  calc
    |∑ a : Fin (Module.finrank ℝ E),
        ∑ c : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α p a y *
            chartInvGramOnE (I := I) g α c q y *
            partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y|
        ≤ ∑ a : Fin (Module.finrank ℝ E),
            |∑ c : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α p a y *
                chartInvGramOnE (I := I) g α c q y *
                partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin (Module.finrank ℝ E),
          ∑ _c : Fin (Module.finrank ℝ E), M_b * M_b * Q := by
        refine Finset.sum_le_sum fun a _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun c _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hMb p a) (hMb c q) (abs_nonneg _) hMb_nn)
          (hQ m a c) (abs_nonneg _) (mul_nonneg hMb_nn hMb_nn)
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring




omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelD_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (m i j k : Fin (Module.finrank ℝ E))
    {M_b D P R : ℝ} (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D)
    (hMb : ∀ l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α k l y| ≤ M_b)
    (hD : ∀ l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y| ≤ D)
    (hP : ∀ l : Fin (Module.finrank ℝ E),
      |gramBracket (I := I) g α i j l y| ≤ P)
    (hR : ∀ l : Fin (Module.finrank ℝ E),
      |gramBracketDeriv (I := I) g α m i j l y| ≤ R) :
    |partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (D * P + M_b * R) := by
  classical
  rw [partialDeriv_chartChristoffel_eq (I := I) g α m i j k hy, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
              gramBracket (I := I) g α i j l y +
            chartInvGramOnE (I := I) g α k l y *
              gramBracketDeriv (I := I) g α m i j l y)| ≤
        ∑ _l : Fin (Module.finrank ℝ E), (D * P + M_b * R) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (hD l) (hP l) (abs_nonneg _) hD_nn)
      (mul_le_mul (hMb l) (hR l) (abs_nonneg _) hMb_nn)
  calc
    (1 / 2 : ℝ) *
        |∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
              gramBracket (I := I) g α i j l y +
            chartInvGramOnE (I := I) g α k l y *
              gramBracketDeriv (I := I) g α m i j l y)|
        ≤ (1 / 2 : ℝ) *
          ∑ _l : Fin (Module.finrank ℝ E), (D * P + M_b * R) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (D * P + M_b * R) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring




omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q : ℝ) (hQ_nn : 0 ≤ Q)
    (hQ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ m p q : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) m
                (chartInvGramOnE (I := I) (gSeq k₁) α p q) (extChartAt I α b) -
              partialDeriv (E := E) m
                (chartInvGramOnE (I := I) (gSeq k₂) α p q) (extChartAt I α b)| ≤
              C * chartMetricJet1DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ :=
    (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb m p q
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hMb1 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₁) α a c
      (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₁ b hb a c
  have hMb2 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₂) α a c
      (extChartAt I α b)| ≤ M_b := by
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
  have hpoint := partialDeriv_chartInvGramOnE_sub_abs_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy hM_b.le hQ_nn hCinv.le
      hMb1 hMb2 (hQ α hα k₁ b hb) hInv m p q
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (chartMetricJet1DiffSup_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))





omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_pou_bnd
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q : ℝ) (hQ_nn : 0 ≤ Q)
    (hQ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j l : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) (gSeq k) α i j l (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * M_b * (3 * Q)
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb i j l
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMbOnE : ∀ q : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k) α l q (extChartAt I α b)| ≤ M_b := by
    intro q
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k b hb l q
  have hBracket : ∀ q : Fin (Module.finrank ℝ E),
      |gramBracket (I := I) (gSeq k) α i j q (extChartAt I α b)| ≤ 3 * Q := by
    intro q
    exact gramBracket_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (fun m a c => hQ α hα k b hb m a c) i j q
  exact christoffel_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
    i j l hM_b.le hMbOnE hBracket




omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelD_pou_bnd
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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ m i j l : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) m
              (chartChristoffel (I := I) (gSeq k) α i j l) (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let P : ℝ := 3 * Q₁
  let R : ℝ := 3 * Q₂
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (D * P + M_b * R)
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hC_nn : 0 ≤ C := by dsimp [C, D, P, R]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb m i j l
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hMbOnE : ∀ q : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k) α l q (extChartAt I α b)| ≤ M_b := by
    intro q
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k b hb l q
  have hDOnE : ∀ q : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartInvGramOnE (I := I) (gSeq k) α l q) (extChartAt I α b)| ≤ D := by
    intro q
    exact invGramD_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le
      (fun a c => by
        rw [chartInvGramOnE_def, hleft]
        exact hMb α hα k b hb a c)
      (fun r a c => hQ₁ α hα k b hb r a c) m l q
  have hP : ∀ q : Fin (Module.finrank ℝ E),
      |gramBracket (I := I) (gSeq k) α i j q (extChartAt I α b)| ≤ P := by
    intro q
    exact gramBracket_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (fun r a c => hQ₁ α hα k b hb r a c) i j q
  have hR : ∀ q : Fin (Module.finrank ℝ E),
      |gramBracketDeriv (I := I) (gSeq k) α m i j q (extChartAt I α b)| ≤ R := by
    intro q
    exact gramBracketD_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (fun r s a c => hQ₂ α hα k b hb r s a c) m i j q
  exact christoffelD_abs_le (I := I) (M := M) (gSeq k) α hy m i j l
    hM_b.le hD_nn hMbOnE hDOnE hP hR




omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q : ℝ) (hQ_nn : 0 ≤ Q)
    (hQ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j k : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) (gSeq k₁) α i j k (extChartAt I α b) -
              chartChristoffel (I := I) (gSeq k₂) α i j k (extChartAt I α b)| ≤
                C * chartMetricJet1DiffSup (I := I) (M := M)
                  (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    (Cinv * (3 * Q) + 3 * M_b) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb i j k
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMb2 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₂) α a c
      (extChartAt I α b)| ≤ M_b := by
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
  have hP : ∀ a c l,
      |gramBracket (I := I) (gSeq k₁) α a c l (extChartAt I α b)| ≤ 3 * Q := by
    intro a c l
    exact gramBracket_abs_le (I := I) (M := M) (gSeq k₁) α (extChartAt I α b)
      (fun m a c => hQ α hα k₁ b hb m a c) a c l
  have hpoint := chartChristoffel_sub_abs_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α
      (mul_nonneg (by norm_num) hQ_nn) hM_b.le hMb2 hP hInv hCinv.le i j k
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (chartMetricJet1DiffSup_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelD_pou_lip
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
          ∀ m i j k : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) m
                (chartChristoffel (I := I) (gSeq k₁) α i j k) (extChartAt I α b) -
              partialDeriv (E := E) m
                (chartChristoffel (I := I) (gSeq k₂) α i j k) (extChartAt I α b)| ≤
              C * chartMetricJet2DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cd, hCd, hInvDLip⟩ :=
    invGramD_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv Q₁ hQ₁_nn hQ₁
  let P : ℝ := 3 * Q₁
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let R : ℝ := 3 * Q₂
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    (Cd * P + 3 * D + Cinv * R + 3 * M_b) + 1
  have hP_nn : 0 ≤ P := by dsimp [P]; positivity
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hR_nn : 0 ≤ R := by dsimp [R]; positivity
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb m i j k
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hMb2 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₂) α a c
      (extChartAt I α b)| ≤ M_b := by
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
  have hP : ∀ a c l,
      |gramBracket (I := I) (gSeq k₁) α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    exact gramBracket_abs_le (I := I) (M := M) (gSeq k₁) α (extChartAt I α b)
      (fun r p q => hQ₁ α hα k₁ b hb r p q) a c l
  have hD : ∀ a c, |partialDeriv (E := E) m
      (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤ D := by
    intro a c
    exact invGramD_abs_le (I := I) (M := M) (gSeq k₂) α hy hM_b.le hMb2
      (fun r p q => hQ₁ α hα k₂ b hb r p q) m a c
  have hR : ∀ a c l,
      |gramBracketDeriv (I := I) (gSeq k₁) α m a c l (extChartAt I α b)| ≤ R := by
    intro a c l
    exact gramBracketD_abs_le (I := I) (M := M) (gSeq k₁) α (extChartAt I α b)
      (fun r s p q => hQ₂ α hα k₁ b hb r s p q) m a c l
  have hpoint := partialDeriv_chartChristoffel_sub_abs_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy hCd.le hCinv.le hM_b.le
      hP_nn hD_nn hR_nn m i j k
      (fun a c => hInvDLip α hα k₁ k₂ b hb m a c) hMb2 hP hD hR hInv
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (chartMetricJet2DiffSup_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
