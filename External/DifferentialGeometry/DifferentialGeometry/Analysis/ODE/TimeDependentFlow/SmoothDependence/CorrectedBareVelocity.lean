import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.Manifold












namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in




private lemma chartTrivRepr_eq_tangentCoordChange_of_target
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (s : ℝ) {c : E}
    (hc : c ∈ (extChartAt I α).target) :
    chartTrivRepr (I := I) α (X s) c =
      tangentCoordChange I ((extChartAt I α).symm c) α
        ((extChartAt I α).symm c) (X s ((extChartAt I α).symm c)) := by
  have hq_src : (extChartAt I α).symm c ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I) α]
    exact (extChartAt I α).map_target hc
  show (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((extChartAt I α).symm c)
        (X s ((extChartAt I α).symm c)) = _
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hq_src]
  rfl




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem corrected_chartflow_eq_bareflow
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (flow : E → ℝ → E) (y : E) {a b : ℝ}
    (hconf : ∀ t ∈ Set.Ioo a b, flow y t ∈ (extChartAt I α).target)
    (hode : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt (flow y) (chartTrivRepr (I := I) α (X t) (flow y t)) (Set.Ioo a b) t) :
    ∀ t ∈ Set.Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (extChartAt I α).symm (flow y s)) (Set.Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((extChartAt I α).symm (flow y t)))) := by
  set F : ℝ → E → E := fun s c =>
    tangentCoordChange I ((extChartAt I α).symm c) α
      ((extChartAt I α).symm c) (X s ((extChartAt I α).symm c)) with hF_def
  have hF : ∀ (s : ℝ) (c : E), F s c =
      tangentCoordChange I ((extChartAt I α).symm c) α
        ((extChartAt I α).symm c) (X s ((extChartAt I α).symm c)) := fun s c => rfl
  have hode' : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt (flow y) (F t (flow y t)) (Set.Ioo a b) t := by
    intro t ht
    have hpt : F t (flow y t) = chartTrivRepr (I := I) α (X t) (flow y t) := by
      rw [hF t (flow y t)]
      exact (chartTrivRepr_eq_tangentCoordChange_of_target X α t (hconf t ht)).symm
    rw [hpt]
    exact hode t ht
  exact chartflow_eq_bareflow_on_U (I := I) X α F
    (fun cs => flow y cs.2) ((extChartAt I α).source) (a := a) (b := b)
    (fun p _ t ht => hode' t ht)
    hF
    (fun p _ t ht => hconf t ht)
    (le_refl _)
    α (mem_extChartAt_source (I := I) α)

end DifferentialGeometry.PDE.RicciFlow.ODE
