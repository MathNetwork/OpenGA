import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric

set_option linter.unnecessarySimpa false


namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def smoothRiemannianMetricToInfty
    (g : SmoothRiemannianMetric I M) :
    Integral.Measure.SmoothRiemannianMetric I M := g

private noncomputable def lieDerivMetricClmAux
    (g : Integral.Measure.SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  { toFun := fun v =>
      LinearMap.toContinuousLinearMap (lieDerivMetric (I := I) g W x v)
    map_add' := fun v v' => by
      ext w
      have := (lieDerivMetric (I := I) g W x).map_add v v'
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      simpa [LinearMap.add_apply, ContinuousLinearMap.add_apply,
             LinearMap.coe_toContinuousLinearMap'] using happ
    map_smul' := fun c v => by
      ext w
      have := (lieDerivMetric (I := I) g W x).map_smul c v
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      simpa [LinearMap.smul_apply, ContinuousLinearMap.smul_apply,
             LinearMap.coe_toContinuousLinearMap', smul_eq_mul] using happ }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] private lemma lieDerivMetricClmAux_apply
    (g : Integral.Measure.SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v w : TangentSpace I x) :
    lieDerivMetricClmAux (I := I) g W x v w =
      lieDerivMetric (I := I) g W x v w := rfl

noncomputable def lieDerivMetricClm
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (lieDerivMetricClmAux (I := I) (smoothRiemannianMetricToInfty (I := I) g) W x)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetricClm_apply
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetricClm (I := I) g W x v w
      = lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g) W x v w := rfl

noncomputable def deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x +
    lieDerivMetricClm (I := I) g
      (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w
      = (-2 : ℝ) * ricciTensor (I := I) g x v w
        + lieDerivMetric (I := I) g (deTurckVF (I := I) g g_bg) x v w := by
  unfold deTurckRicciRHS
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [lieDerivMetricClm_apply]
  simp only [smul_eq_mul]
  rfl

end RicciFlow
end PDE
end DifferentialGeometry
