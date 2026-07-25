import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false













namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}



def metricCovDerivForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (frame d x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d a p *
        metricCompForMetricInFrame (I := I) g frame x p b) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d b p *
        metricCompForMetricInFrame (I := I) g frame x a p)







def metricCovDeriv2ForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b c : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M =>
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe y a b c)
      x (frame d x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d a p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x p b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d b p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x a p c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d c p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x a b p)







def metricCovDeriv3ForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (m d a b c : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M =>
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe y d a b c)
      x (frame m x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m d p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x p a b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m a p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d p b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m b p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a p c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m c p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a b p)

end Components

end

end DifferentialGeometry.Tensor.Coordinates
