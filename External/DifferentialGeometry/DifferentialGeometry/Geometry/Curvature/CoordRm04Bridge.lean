import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
















namespace DifferentialGeometry

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]





omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricRm04StdAt_eq_chartRiemannCLM
    (g : SmoothRiemannianMetric I M) (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) g x X Y Z W
      = g.inner x W (chartRiemannCLM (I := I) g x X Y Z) := by
  rw [metricRm04StdAt_apply,
    show metricRm04At (I := I) g x
        = riemannCurvature04At g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl,
    riemannCurvature04At_apply_const]
  haveI : ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ := LeviCivita_isContMDiff g
  rw [riemannCurvatureAux_tangentConst_eq_riemannOp (metricCov (I := I) g)
      (metricCov_smooth (I := I) g) x X Y Z,
    show riemannOp (cov := metricCov (I := I) g) x X Y Z
        = riemannOp (cov := LeviCivita (I := I) g) x X Y Z from rfl,
    riemannOp_eq_chartRiemannCLM_apply]

end DifferentialGeometry
