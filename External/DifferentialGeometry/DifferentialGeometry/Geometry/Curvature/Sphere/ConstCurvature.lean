import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import DifferentialGeometry.Geometry.Curvature.PullbackNaturality
import DifferentialGeometry.Geometry.Metric.Sphere.RoundShape
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections


















noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Connection.CovariantDerivative

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]





omit [NeZero n] in
theorem metricRm04_round_invariant [NeZero n]
    (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1)
    (X Y Z W : TangentSpace (𝓡 n) x) :
    metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Z W
      = metricRm04StdAt (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e x)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x X)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Y)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Z)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x W) := by
  haveI : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  haveI : IsManifold (𝓡 n) 1 (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  haveI : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  have h := metricRm04Std_pullback (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e)
    x X Y Z W
  rwa [pullbackMetric_round_eq] at h

set_option maxHeartbeats 800000 in







omit [NeZero n] in
omit [FiniteDimensional ℝ E] in
theorem roundMetric_sec_value [NeZero n]
    (x : sphere (0 : E) 1) (X Y : TangentSpace (𝓡 n) x) :
    metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Y X
      = (roundMetric (E := E) (n := n)).inner x X X * (roundMetric (E := E) (n := n)).inner x Y Y
        - (roundMetric (E := E) (n := n)).inner x X Y * (roundMetric (E := E) (n := n)).inner x X Y := by
  haveI : IsManifold (𝓡 n) ∞ (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := 𝓡 n) x X
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := 𝓡 n) x Y
  rw [metricRm04StdAt_apply,
    show metricRm04At (roundMetric (E := E) (n := n)) x
        = riemannCurvature04At (roundMetric (E := E) (n := n))
            (metricCov (roundMetric (E := E) (n := n)))
            (metricCov_smooth (roundMetric (E := E) (n := n))) x from rfl,
    riemannCurvature04At_apply_const,
    show CovariantDerivative.riemannCurvatureAux (metricCov (roundMetric (E := E) (n := n)))
          (CovariantDerivative.tangentConstAt x X) (CovariantDerivative.tangentConstAt x Y)
          (CovariantDerivative.tangentConstAt x Y) x
        = CovariantDerivative.riemannCurvatureAux (metricCov (roundMetric (E := E) (n := n)))
            (⇑Xc) (⇑Yc) (⇑Yc) x from by
        simp only [riemannCurvatureAux_eq_connectionRiemannCurvatureField]
        exact connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
          (metricCov (roundMetric (E := E) (n := n)))
          (metricCov_smooth (roundMetric (E := E) (n := n))) X Y Y Xc Yc Yc hXc hYc hYc,
    roundMetric_inner, real_inner_comm,
    dIncl_curv_inner Yc Xc Yc x X
      (ambDeriv_section_mdiffAt Yc Yc x) (ambDeriv_section_mdiffAt Yc Xc x),
    hXcx, hYcx]
  simp only [roundInner_apply, roundMetric_inner,
    real_inner_comm (dIncl (n := n) x Y) (dIncl (n := n) x X)]
  ring






omit [NeZero n] in
omit [FiniteDimensional ℝ E] in
theorem roundMetric_constPosSec [NeZero n] :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : sphere (0 : E) 1) (X Y : TangentSpace (𝓡 n) x),
      metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Y X
        = c * ((roundMetric (E := E) (n := n)).inner x X X * (roundMetric (E := E) (n := n)).inner x Y Y
            - (roundMetric (E := E) (n := n)).inner x X Y * (roundMetric (E := E) (n := n)).inner x X Y) :=
  ⟨1, one_pos, fun x X Y => by rw [one_mul]; exact roundMetric_sec_value x X Y⟩

end Geometry
end DifferentialGeometry
