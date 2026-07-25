import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricFiberData

set_option autoImplicit false
set_option linter.style.longLine false










namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff


namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

omit [FiniteDimensional ℝ V] in
private theorem dual_finrank_eq :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V) :=
  Subspace.dual_finrank_eq.symm






variable {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]


end MetricFiberData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev SmoothMetric_gen
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)


def tangentFlatLinear_gen (g : SmoothMetric_gen I M) (x : M) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    simp
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    simp

omit [FiniteDimensional ℝ E] in
@[simp] theorem tangentFlatLinear_apply_gen
    (g : SmoothMetric_gen I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatLinear_gen (I := I) g x v w = g.inner x v w := by
  rfl


omit [FiniteDimensional ℝ E] in
theorem tangentFlatLinear_injective_gen
    (g : SmoothMetric_gen I M) (x : M) :
    Function.Injective (tangentFlatLinear_gen (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [tangentFlatLinear_apply_gen] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)


def tangentFlatEquiv_gen (g : SmoothMetric_gen I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (tangentFlatLinear_gen (I := I) g x)
    (tangentFlatLinear_injective_gen (I := I) g x)
    MetricFiberData.dual_finrank_eq

@[simp] theorem tangentFlatEquiv_apply_gen
    (g : SmoothMetric_gen I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatEquiv_gen (I := I) g x v w = g.inner x v w := by
  rfl





structure TangentMetricData_gen
    (g : SmoothMetric_gen I M) (x : M) where
  metric : MetricFiberData (TangentSpace I x)
  realizes_inner : forall X Y : TangentSpace I x,
    metric.inner X Y = g.inner x X Y


def tangentMetricData_gen (g : SmoothMetric_gen I M) (x : M) :
    TangentMetricData_gen (I := I) g x where
  metric :=
    { flat := tangentFlatEquiv_gen (I := I) g x
      symm := by
        intro X Y
        exact g.symm x X Y
      nonneg := by
        intro X
        by_cases hX : X = 0
        · simp [hX]
        · exact le_of_lt (g.pos x X hX) }
  realizes_inner := by
    intro X Y
    rfl

namespace TangentMetricData_gen

@[simp] theorem inner_eq_gen
    {g : SmoothMetric_gen I M} {x : M} (D : TangentMetricData_gen (I := I) g x)
    (X Y : TangentSpace I x) :
    D.metric.inner X Y = g.inner x X Y :=
  D.realizes_inner X Y

end TangentMetricData_gen

end

end Tensor0SBundle
