import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import Mathlib.LinearAlgebra.Trace


namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

def adjointRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    Tensor0SSpace s I x →ₗ[Real] Tensor0SSpace r I x :=
  MetricFiberData.adjoint
    (tensor0SMetricData (I := I) g x r)
    (tensor0SMetricData (I := I) g x s)
    A.toLinearMap

theorem adjointRS_inner
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x)
    (Y : Tensor0SSpace s I x) (X : Tensor0SSpace r I x) :
    inner0S (I := I) g x r (adjointRS (I := I) (g := g) (x := x) r s A Y) X =
      inner0S (I := I) g x s Y (A X) := by
  simpa [adjointRS, inner0S] using
    MetricFiberData.adjoint_inner
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
      A.toLinearMap Y X

def innerRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) : Real :=
  LinearMap.trace Real (Tensor0SSpace r I x)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap)

@[simp] theorem innerRS_eq_trace
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) :
    innerRS (I := I) (g := g) (x := x) r s A B =
      LinearMap.trace Real (Tensor0SSpace r I x)
        ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap) := by
  rfl

def normSqRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) : Real :=
  innerRS (I := I) (g := g) (x := x) r s A A

@[simp] theorem normSqRS_eq_inner
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      innerRS (I := I) (g := g) (x := x) r s A A := by
  rfl

abbrev TensorRSTimeField
    (I : ModelWithCorners Real E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (Time : Type*) (r s : Nat) :=
  Time -> (x : M) -> TensorRSSpace r s I x

def tensorNormSqRS
    (g : Time -> SmoothMetric I M)
    {r s : Nat}
    (A : TensorRSTimeField I M Time r s) :
    Time -> M -> Real :=
  fun t x => normSqRS (I := I) (g := g t) (x := x) r s (A t x)

end

end Tensor0SBundle
