import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckShortTime
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Flow.VectorFieldSmooth
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckVectorFieldContinuousInMetric
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deturck_vf_time_family_smoothness
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (h_metric_cont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T))
    (h_metric_partial_cont :
      ∀ (x : M) (l i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun t : ℝ =>
            partialDeriv (E := E) l
              (chartGramOnE (I := I) (g_DT t) x i j) (extChartAt I x x))
          (Set.Ico (0 : ℝ) T)) :
    ∀ x : M,
      ContinuousOn
        (fun t : ℝ =>
          (deTurckVF (I := I) (g_DT t) g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        (Set.Ico (0 : ℝ) T) := by
  intro x
  have hrewrite : (fun t : ℝ =>
        (deTurckVF (I := I) (g_DT t) g_bg :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      fun t : ℝ =>
        ∑ p : Fin (Module.finrank ℝ E),
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg x p
              (extChartAt I x x) •
            ((chartModelBasis E) p : TangentSpace I x) := by
    funext t
    exact deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) (g_DT t) g_bg x
  rw [hrewrite]
  refine continuousOn_finset_sum _ ?_
  intro p _
  refine ContinuousOn.smul ?_ continuousOn_const
  have h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ =>
          chartGramOnE (I := I) (g_DT t) x i j (extChartAt I x x))
        (Set.Ico (0 : ℝ) T) := by
    intro i j
    have hreduce :
        (fun t : ℝ =>
            chartGramOnE (I := I) (g_DT t) x i j (extChartAt I x x))
          = fun t : ℝ =>
              (g_DT t).inner x
                ((chartModelBasis E) i : TangentSpace I x)
                ((chartModelBasis E) j : TangentSpace I x) := by
      funext t
      rw [chartGramOnE_def]
      rw [extChartAt_to_inv (I := I) x]
      rw [chartGramMatrix_apply]
      rw [chartBasisVecFiber_self (I := I) x i,
          chartBasisVecFiber_self (I := I) x j]
    rw [hreduce]
    exact h_metric_cont x ((chartModelBasis E) i) ((chartModelBasis E) j)
  have h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) x i j)
            (extChartAt I x x))
        (Set.Ico (0 : ℝ) T) := h_metric_partial_cont x
  have hx_base : ((extChartAt I x).symm (extChartAt I x x)) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [extChartAt_to_inv (I := I) x]
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  exact chartDeTurckVFComp_continuous_in_metric_at (I := I) g_bg x
    (extChartAt I x x) (Set.Ico (0 : ℝ) T) g_DT h_entry h_partial hx_base p

end DifferentialGeometry.PDE.RicciFlow
