import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.GramInvUniformEigenvalueLowerBound
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

def chartInvGramMatrix_l1Sum
    (g : SmoothRiemannianMetric I M) (α x : M) : ℝ :=
  ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
    |chartInvGramMatrix (I := I) g α x ij.1 ij.2|

omit [T2Space M] in
lemma chartInvGramMatrix_l1Sum_nonneg
    (g : SmoothRiemannianMetric I M) (α x : M) :
    0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x := by
  unfold chartInvGramMatrix_l1Sum
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [T2Space M] in
private lemma chartGramMatrix_entry_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun b : M => chartGramMatrix (I := I) g α b i j)
      (chartAt H α).source := by
  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun b : M => chartGramMatrix (I := I) g α b i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
      = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
  rw [h_set_eq] at hsmooth
  exact hsmooth.continuousOn

omit [T2Space M] in
private lemma chartInvGramMatrix_entry_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun b : M => chartInvGramMatrix (I := I) g α b i j)
      (chartAt H α).source := by
  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun b : M => chartInvGramMatrix (I := I) g α b i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
      = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
  rw [h_set_eq] at hsmooth
  exact hsmooth.continuousOn

omit [T2Space M] in
private lemma chartInvGramMatrix_l1Sum_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (chartInvGramMatrix_l1Sum (I := I) (M := M) g α)
      (chartAt H α).source := by
  classical
  unfold chartInvGramMatrix_l1Sum
  refine continuousOn_finset_sum _ (fun ij _ => ?_)
  exact (chartInvGramMatrix_entry_continuousOn_chartSource
    (I := I) (M := M) g α ij.1 ij.2).abs

omit [T2Space M] in
private lemma exists_bound_on_compact_of_continuousOn
    (α : M) (f : M → ℝ)
    (h_cont : ContinuousOn f (chartAt H α).source)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, f b ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro b hb
    rw [h_empty] at hb
    exact absurd hb (Set.notMem_empty _)
  have h_cont_K : ContinuousOn f K := h_cont.mono hKsub
  have h_bdd : BddAbove (f '' K) := hK.bddAbove_image h_cont_K
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
  intro b hb
  have h1 : f b ≤ C := hC ⟨b, hb, rfl⟩
  have h2 : C ≤ max C 0 := le_max_left _ _
  linarith

omit [T2Space M] in
theorem chartGramMatrix_entry_isBounded_on_compact
(g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b ∈ K, |chartGramMatrix (I := I) g α b i j| ≤ C := by
  have h_cont : ContinuousOn (fun b : M => |chartGramMatrix (I := I) g α b i j|)
      (chartAt H α).source :=
    (chartGramMatrix_entry_continuousOn_chartSource (I := I) (M := M) g α i j).abs
  exact exists_bound_on_compact_of_continuousOn (α := α) _ h_cont hK hKsub

omit [T2Space M] in
theorem chartInvGramMatrix_entry_isBounded_on_compact
(g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b ∈ K, |chartInvGramMatrix (I := I) g α b i j| ≤ C := by
  have h_cont :
      ContinuousOn (fun b : M => |chartInvGramMatrix (I := I) g α b i j|)
        (chartAt H α).source :=
    (chartInvGramMatrix_entry_continuousOn_chartSource
      (I := I) (M := M) g α i j).abs
  exact exists_bound_on_compact_of_continuousOn (α := α) _ h_cont hK hKsub

omit [T2Space M] in
theorem chartInvGramMatrix_l1Sum_isBounded_on_compact
(g : SmoothRiemannianMetric I M)
    (α : M) {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b ∈ K, chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ C := by
  have h_cont := chartInvGramMatrix_l1Sum_continuousOn_chartSource
    (I := I) (M := M) g α
  exact exists_bound_on_compact_of_continuousOn (α := α) _ h_cont hK hKsub

theorem chartInvGramMatrix_l1Sum_isBounded_on_pouTsupport
    [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ C := by
  classical
  set Kα : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_base :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  have hKα_sub_src : Kα ⊆ (chartAt H α).source := by
    have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
        = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
    rw [← h_set_eq]
    exact hKα_sub_base
  rcases chartInvGramMatrix_l1Sum_isBounded_on_compact
      (I := I) (M := M) g α hKα_compact hKα_sub_src with ⟨C, hC_pos, hC_le⟩
  exact ⟨C, hC_pos, fun b hb => hC_le b hb⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
