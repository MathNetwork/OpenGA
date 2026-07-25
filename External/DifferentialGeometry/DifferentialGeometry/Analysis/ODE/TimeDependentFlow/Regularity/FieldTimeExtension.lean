import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge











namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem field_time_clamp_extension
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hcont0 : ContinuousOn (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2)) (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M, ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartTrivRepr (I := I) α (X_DT q.1) z) (extChartAt I α q.2)) (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Xext : ℝ → ∀ x : M, TangentSpace I x,
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : M, Xext s x = X_DT s x) ∧
      ContinuousOn (fun q : ℝ × M => (Xext q.1 q.2 : TangentSpace I q.2)) (Set.univ : Set (ℝ × M)) ∧
      (∀ α : M, ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartTrivRepr (I := I) α (Xext q.1) z) (extChartAt I α q.2)) (Set.univ : Set (ℝ × M))) := by
  classical
  set c : ℝ → ℝ := fun s => max 0 (min s T) with hc
  have hc_cont : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hc_id : ∀ s ∈ Set.Icc (0 : ℝ) T, c s = s := by
    intro s hs
    rw [Set.mem_Icc] at hs
    show max 0 (min s T) = s
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hc_mem : ∀ s : ℝ, c s ∈ Set.Icc (0 : ℝ) T := by
    intro s
    rw [Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  refine ⟨fun s x => X_DT (c s) x, ?_, ?_, ?_⟩
  · intro s hs x
    show X_DT (c s) x = X_DT s x
    rw [hc_id s hs]
  · have hmaps : Continuous (fun q : ℝ × M => ((c q.1, q.2) : ℝ × M)) :=
      (hc_cont.comp continuous_fst).prodMk continuous_snd
    have hmem : ∀ q : ℝ × M, ((c q.1, q.2) : ℝ × M) ∈ Set.Icc (0 : ℝ) T ×ˢ Set.univ :=
      fun q => Set.mk_mem_prod (hc_mem q.1) (Set.mem_univ _)
    exact (hcont0.comp_continuous hmaps hmem).continuousOn
  · intro α
    have hmaps : Continuous (fun q : ℝ × M => ((c q.1, q.2) : ℝ × M)) :=
      (hc_cont.comp continuous_fst).prodMk continuous_snd
    have hmem : ∀ q : ℝ × M, ((c q.1, q.2) : ℝ × M) ∈ Set.Icc (0 : ℝ) T ×ˢ Set.univ :=
      fun q => Set.mk_mem_prod (hc_mem q.1) (Set.mem_univ _)
    exact ((hgrad0 α).comp_continuous hmaps hmem).continuousOn

end DifferentialGeometry.PDE.RicciFlow.ODE
