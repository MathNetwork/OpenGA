import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Tensor.RSTensor.Components

set_option autoImplicit false
set_option linter.style.longLine false














noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




def metricVariationComponent
    (v : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) (X Y : TangentSpace I x) : Real :=
  v x (fun q : Fin 2 => if q = 0 then X else Y)





structure MetricPotentialVariationPath
    (g : SmoothRiemannianMetric I M) (potential : M -> Real) where
  G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real
  potentialPath : Real -> M -> Real
  base : Real
  metricBase : G.metric base = g
  potentialBase : potentialPath base = potential

namespace MetricPotentialVariationPath

variable {g : SmoothRiemannianMetric I M} {potential : M -> Real}

omit [FiniteDimensional ℝ E] in
@[simp] theorem metric_base
    (path : MetricPotentialVariationPath (I := I) g potential) :
    path.G.metric path.base = g :=
  path.metricBase

omit [FiniteDimensional ℝ E] in
@[simp] theorem potential_base
    (path : MetricPotentialVariationPath (I := I) g potential) :
    path.potentialPath path.base = potential :=
  path.potentialBase

end MetricPotentialVariationPath






structure IsMetricPotentialVariationPath
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation : M -> Real) : Prop where
  leviCivita :
    ∀ s : Real,
      DifferentialGeometry.Integral.Connection.IsLeviCivita (I := I) (path.G.connection s)
        (path.G.metric s)
  metric_deriv :
    ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun s : Real => (path.G.metric s).inner x X Y)
        (metricVariationComponent (I := I) metricVariation x X Y)
        path.base
  potential_deriv :
    ∀ x : M,
      HasDerivAt (fun s : Real => path.potentialPath s x)
        (potentialVariation x) path.base

end DifferentialGeometry.Integral.Connection
