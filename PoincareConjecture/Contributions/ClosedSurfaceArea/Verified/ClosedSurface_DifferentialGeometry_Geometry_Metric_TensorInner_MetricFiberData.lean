import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

structure MetricFiberData (V : Type*) [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] where
  flat : V ≃ₗ[Real] Module.Dual Real V
  symm : forall v w : V, flat v w = flat w v
  nonneg : forall v : V, 0 <= flat v v

namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

omit [FiniteDimensional ℝ V] in
 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq_closedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V) :=
  Subspace.dual_finrank_eq.symm

def ofFlat
    (flat : V →ₗ[Real] Module.Dual Real V)
    (hinj : Function.Injective flat)
    (hsymm : forall v w : V, flat v w = flat w v)
    (hnonneg : forall v : V, 0 <= flat v v) :
    MetricFiberData V where
  flat := LinearMap.linearEquivOfInjective flat hinj _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq_closedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
  symm := hsymm
  nonneg := hnonneg

def inner (D : MetricFiberData V) (v w : V) : Real :=
  D.flat v w

def sharp (D : MetricFiberData V) : Module.Dual Real V ≃ₗ[Real] V :=
  D.flat.symm

@[simp] theorem inner_apply (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.flat v w := by
  rfl

theorem inner_nonneg (D : MetricFiberData V) (v : V) :
    0 <= D.inner v v := by
  exact D.nonneg v

theorem inner_self_eq_zero_iff (D : MetricFiberData V) (v : V) :
    D.inner v v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hvw : forall w : V, D.inner v w = 0 := by
      intro w
      by_contra hne
      let a := D.inner v w
      let b := D.inner w w
      let t := -((b + 1) / (2 * a))
      have ha : a ≠ 0 := hne
      have hquad : 0 <= D.inner (w + t • v) (w + t • v) :=
        D.inner_nonneg (w + t • v)
      have hcalc : D.inner (w + t • v) (w + t • v) = -1 := by
        have hexpand :
            D.inner (w + t • v) (w + t • v) =
              b + 2 * t * a + t * t * D.inner v v := by
          unfold inner a b
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul]
          rw [D.symm w v]
          simp [inner]
          ring_nf
        rw [hexpand, hv]
        unfold t b a
        field_simp [ha]
        ring
      linarith
    have hflat : D.flat v = 0 := by
      ext w
      exact hvw w
    exact D.flat.injective (by simpa using hflat)
  · intro hv
    simp [hv, inner]

@[reducible] def toCore (D : MetricFiberData V) : InnerProductSpace.Core Real V where
  inner := fun v w => D.inner v w
  conj_inner_symm := by
    intro x y
    exact D.symm y x
  re_inner_nonneg := by
    intro x
    simpa using D.inner_nonneg x
  add_left := by
    intro x y z
    simp [MetricFiberData.inner, map_add]
  smul_left := by
    intro x y r
    simp [MetricFiberData.inner, smul_eq_mul]
  definite := by
    intro x hx
    exact (D.inner_self_eq_zero_iff x).1 (by simpa using hx)

theorem toCore_inner (D : MetricFiberData V) (v w : V) :
    letI : InnerProductSpace.Core Real V := D.toCore
    letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
    Inner.inner Real v w = D.inner v w := by
  change D.toCore.inner v w = D.inner v w
  rfl

variable {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]

def adjoint (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) : W →ₗ[Real] V :=
  DV.flat.symm.toLinearMap.comp
    (A.dualMap.comp DW.flat.toLinearMap)

theorem adjoint_inner
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) (y : W) (x : V) :
    DV.inner (adjoint DV DW A y) x = DW.inner y (A x) := by
  unfold inner adjoint
  change
    DV.flat (DV.flat.symm
        ((A.dualMap.comp DW.flat.toLinearMap) y)) x =
      DW.flat y (A x)
  rw [DV.flat.apply_symm_apply]
  rfl

end MetricFiberData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev SmoothMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

def tangentFlatLinear (g : SmoothMetric I M) (x : M) :
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
@[simp] theorem tangentFlatLinear_apply
    (g : SmoothMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatLinear (I := I) g x v w = g.inner x v w := by
  rfl

omit [FiniteDimensional ℝ E] in
theorem tangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (tangentFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [tangentFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)

def tangentFlatEquiv (g : SmoothMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (tangentFlatLinear (I := I) g x)
    (tangentFlatLinear_injective (I := I) g x)
    _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq_closedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData

structure TangentMetricData
    (g : SmoothMetric I M) (x : M) where
  metric : MetricFiberData (TangentSpace I x)
  realizes_inner : forall X Y : TangentSpace I x,
    metric.inner X Y = g.inner x X Y

def tangentMetricData (g : SmoothMetric I M) (x : M) :
    TangentMetricData (I := I) g x where
  metric :=
    { flat := tangentFlatEquiv (I := I) g x
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

end

end Tensor0SBundle

end DifferentialGeometry
