import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSAbstractJet2Bound












































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem extChartAt_self_mem_interior_target (α : M) :
    extChartAt I α α ∈ interior ((extChartAt I α).target : Set E) := by
  rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
  exact mem_extChartAt_target (I := I) α




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem singleton_chartCenter_subset_interior_target (α : M) :
    ({extChartAt I α α} : Set E) ⊆ interior ((extChartAt I α).target : Set E) :=
  Set.singleton_subset_iff.mpr (extChartAt_self_mem_interior_target (I := I) α)








omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem abstractRHSFrameComponent_diff_abs_le_jet2_chartCenter
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : Fin (Module.finrank ℝ E),
      |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I α).symm (extChartAt I α α)) -
            deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I α).symm (extChartAt I α α)))
          (chartFrameVec (I := I) α i ((extChartAt I α).symm (extChartAt I α α)))
          (chartFrameVec (I := I) α j ((extChartAt I α).symm (extChartAt I α α)))| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α (extChartAt I α α) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    abstractRHSFrameComponent_diff_abs_le_jet2 (I := I) g_bg g₁ g₂ α
      (K := {extChartAt I α α}) isCompact_singleton
      (singleton_chartCenter_subset_interior_target (I := I) α)
  exact ⟨C, hC_pos, fun i j => hC (extChartAt I α α) (Set.mem_singleton _) i j⟩




omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_finite_chartSource_cover :
    ∃ s : Finset M, (⋃ α ∈ s, (chartAt H α).source) = Set.univ := by
  classical
  have hcover : (⋃ α : M, (chartAt H α).source) = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
  have hopen : ∀ α : M, IsOpen ((chartAt H α).source) := fun α => (chartAt H α).open_source
  obtain ⟨s, hs⟩ :=
    IsCompact.elim_finite_subcover (isCompact_univ (X := M))
      (fun α : M => (chartAt H α).source) hopen
      (by rw [hcover])
  refine ⟨s, Set.eq_univ_of_univ_subset ?_⟩
  simpa using hs















omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem exists_uniform_const_RHSFrameComponent_diff_jet2_on_finset
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M)
    {ι : Type*} (t : Finset ι) (α : ι → M) (K : ι → Set E)
    (hK : ∀ c ∈ t, IsCompact (K c))
    (hKsub : ∀ c ∈ t, K c ⊆ interior ((extChartAt I (α c)).target : Set E)) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ t, ∀ y ∈ K c, ∀ i j : Fin (Module.finrank ℝ E),
      |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I (α c)).symm y) -
            deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I (α c)).symm y))
          (chartFrameVec (I := I) (α c) i ((extChartAt I (α c)).symm y))
          (chartFrameVec (I := I) (α c) j ((extChartAt I (α c)).symm y))| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y := by
  classical
  choose C hC_pos hC using fun (c : ι) (hc : c ∈ t) =>
    abstractRHSFrameComponent_diff_abs_le_jet2 (I := I) g_bg g₁ g₂ (α c)
      (hK c hc) (hKsub c hc)
  refine ⟨1 + ∑ c ∈ t.attach, C c.1 c.2, ?_, ?_⟩
  · have hsum_nn : 0 ≤ ∑ c ∈ t.attach, C c.1 c.2 :=
      Finset.sum_nonneg (fun c _ => (hC_pos c.1 c.2).le)
    linarith
  intro c hc y hy i j
  have hbound := hC c hc y hy i j
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y :=
    chartMetricJet2DiffSup_nonneg _ _ _ _
  have hCc_le : C c hc ≤ 1 + ∑ d ∈ t.attach, C d.1 d.2 := by
    have hmem : (⟨c, hc⟩ : {x // x ∈ t}) ∈ t.attach := Finset.mem_attach _ _
    have hsingle : C c hc ≤ ∑ d ∈ t.attach, C d.1 d.2 :=
      Finset.single_le_sum (f := fun d : {x // x ∈ t} => C d.1 d.2)
        (fun d _ => (hC_pos d.1 d.2).le) hmem
    linarith
  calc
    |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I (α c)).symm y) -
          deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I (α c)).symm y))
        (chartFrameVec (I := I) (α c) i ((extChartAt I (α c)).symm y))
        (chartFrameVec (I := I) (α c) j ((extChartAt I (α c)).symm y))|
      ≤ C c hc * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y := hbound
    _ ≤ (1 + ∑ d ∈ t.attach, C d.1 d.2) *
          chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ (α c) y :=
        mul_le_mul_of_nonneg_right hCc_le hjet2_nn

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
