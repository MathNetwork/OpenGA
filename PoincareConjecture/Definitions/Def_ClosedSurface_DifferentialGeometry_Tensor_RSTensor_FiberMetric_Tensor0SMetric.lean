import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_CotangentRiemannian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Riemannian

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MetricFiberData

variable {V W : Type*}

def realFlatLinear : Real →ₗ[Real] Module.Dual Real Real where
  toFun := fun a =>
    { toFun := fun b => a * b
      map_add' := by
        intro b c
        ring
      map_smul' := by
        intro c b
        simp [smul_eq_mul, mul_left_comm] }
  map_add' := by
    intro a b
    ext
    simp
  map_smul' := by
    intro c a
    ext
    simp [smul_eq_mul]

def real : MetricFiberData Real :=
  MetricFiberData.ofFlat realFlatLinear
    (by
      intro a b h
      have h1 := congrArg (fun φ : Module.Dual Real Real => φ 1) h
      simpa [realFlatLinear] using h1)
    (by
      intro a b
      change a * b = b * a
      ring)
    (by
      intro a
      change 0 <= a * a
      nlinarith [sq_nonneg a])

def pullback [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (e : V ≃ₗ[Real] W) (D : MetricFiberData W) : MetricFiberData V where
  flat := e.trans (D.flat.trans e.dualMap)
  symm := by
    intro v w
    change D.flat (e v) (e w) = D.flat (e w) (e v)
    exact D.symm (e v) (e w)
  nonneg := by
    intro v
    change 0 <= D.flat (e v) (e v)
    exact D.nonneg (e v)

 def _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    (V →ₗ[Real] W) →ₗ[Real] Module.Dual Real (V →ₗ[Real] W) where
  toFun A :=
    { toFun := fun B =>
        LinearMap.trace Real V
          ((MetricFiberData.adjoint DV DW A).comp B)
      map_add' := by
        intro B C
        simp [LinearMap.comp_add, map_add]
      map_smul' := by
        intro c B
        simp [LinearMap.comp_smul, map_smul] }
  map_add' := by
    intro A B
    ext C
    have hdual :
        (A + B).dualMap = A.dualMap + B.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((A + B).dualMap).comp DW.flat.toLinearMap)).comp C) =
        LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (A.dualMap.comp DW.flat.toLinearMap)).comp C) +
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (B.dualMap.comp DW.flat.toLinearMap)).comp C)
    rw [hdual]
    simp [LinearMap.add_comp, LinearMap.comp_add, map_add]
  map_smul' := by
    intro c A
    ext B
    have hdual :
        (c • A).dualMap = c • A.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((c • A).dualMap).comp DW.flat.toLinearMap)).comp B) =
        c *
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (A.dualMap.comp DW.flat.toLinearMap)).comp B)
    rw [hdual]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, map_smul]

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_sum_inner_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      ∑ i : Fin (Module.finrank Real V),
        Inner.inner Real (A (stdOrthonormalBasis Real V i))
          (B (stdOrthonormalBasis Real V i)) := by
  rw [LinearMap.trace_eq_matrix_trace Real
    (stdOrthonormalBasis Real V).toBasis ((LinearMap.adjoint A).comp B)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show
      (LinearMap.toMatrix (stdOrthonormalBasis Real V).toBasis
        (stdOrthonormalBasis Real V).toBasis
        ((LinearMap.adjoint A).comp B)) i i =
        (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis Real V)
          ((LinearMap.adjoint A).comp B)) i i from rfl]
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  exact LinearMap.adjoint_inner_right A
    (stdOrthonormalBasis Real V i) (B (stdOrthonormalBasis Real V i))

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    0 <= LinearMap.trace Real V ((LinearMap.adjoint A).comp A) := by
  rw [_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_sum_inner_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric]
  exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_zero_iff_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp A) = 0 ↔ A = 0 := by
  constructor
  · intro htrace
    have hsum :
        (∑ i : Fin (Module.finrank Real V),
          Inner.inner Real (A (stdOrthonormalBasis Real V i))
            (A (stdOrthonormalBasis Real V i))) = 0 := by
      simpa [_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_sum_inner_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric] using htrace
    have hzero :
        forall i : Fin (Module.finrank Real V),
          A (stdOrthonormalBasis Real V i) = 0 := by
      intro i
      have hi :
          Inner.inner Real (A (stdOrthonormalBasis Real V i))
            (A (stdOrthonormalBasis Real V i)) = 0 := by
        have hs := (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ)
          (f := fun i : Fin (Module.finrank Real V) =>
            Inner.inner Real (A (stdOrthonormalBasis Real V i))
              (A (stdOrthonormalBasis Real V i)))
          (by intro _ _; exact real_inner_self_nonneg)).1 hsum
        exact hs i (Finset.mem_univ i)
      exact (inner_self_eq_zero).1 hi
    apply (stdOrthonormalBasis Real V).toBasis.ext
    intro i
    simpa using hzero i
  · intro hA
    simp [hA]

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_comm_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      LinearMap.trace Real V ((LinearMap.adjoint B).comp A) := by
  rw [_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_sum_inner_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric, _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_sum_inner_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric]
  apply Finset.sum_congr rfl
  intro i _
  exact (real_inner_comm (A (stdOrthonormalBasis Real V i))
    (B (stdOrthonormalBasis Real V i))).symm

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.metric_adjoint_eq_adjoint_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
    [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) (A : V →ₗ[Real] W) :
    letI : InnerProductSpace.Core Real V := DV.toCore
    letI : NormedAddCommGroup V :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
    letI : InnerProductSpace.Core Real W := DW.toCore
    letI : NormedAddCommGroup W :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
    letI : InnerProductSpace Real W :=
      @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
    MetricFiberData.adjoint DV DW A = LinearMap.adjoint A := by
  let : InnerProductSpace.Core Real V := DV.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  let : InnerProductSpace.Core Real W := DW.toCore
  let : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  let : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  apply LinearMap.ext
  intro y
  apply ext_inner_right Real
  intro x
  change DV.inner (MetricFiberData.adjoint DV DW A y) x =
    DV.inner (LinearMap.adjoint A y) x
  rw [MetricFiberData.adjoint_inner]
  rw [← DW.toCore_inner y (A x), ← DV.toCore_inner (LinearMap.adjoint A y) x]
  exact (LinearMap.adjoint_inner_left A x y).symm

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_comm_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A B : V →ₗ[Real] W) :
    _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A B = _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW B A := by
  let : InnerProductSpace.Core Real V := DV.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  let : InnerProductSpace.Core Real W := DW.toCore
  let : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  let : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  have hA := _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.metric_adjoint_eq_adjoint_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A
  have hB := _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.metric_adjoint_eq_adjoint_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW B
  change LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp B) =
    LinearMap.trace Real V ((MetricFiberData.adjoint DV DW B).comp A)
  rw [hA, hB]
  exact _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_comm_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric A B

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    0 <= _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A A := by
  let : InnerProductSpace.Core Real V := DV.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  let : InnerProductSpace.Core Real W := DW.toCore
  let : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  let : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  have hA := _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.metric_adjoint_eq_adjoint_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A
  change 0 <= LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp A)
  rw [hA]
  exact _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric A

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_self_eq_zero_iff_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A A = 0 ↔ A = 0 := by
  let : InnerProductSpace.Core Real V := DV.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  let : InnerProductSpace.Core Real W := DW.toCore
  let : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  let : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  have hA := _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.metric_adjoint_eq_adjoint_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A
  change LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp A) = 0 ↔ A = 0
  rw [hA]
  exact _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_adjoint_comp_eq_zero_iff_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric A

 theorem _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.hom_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    Function.Injective (_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW) ∧
      (forall A B : V →ₗ[Real] W,
        _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A B = _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW B A) ∧
      (forall A : V →ₗ[Real] W, 0 <= _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW A A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hAB
    have hflat : _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW (A - B) = 0 := by
      rw [map_sub, hAB, sub_self]
    have hdiag : _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW (A - B) (A - B) = 0 := by
      rw [hflat]
      rfl
    have hzero : A - B = 0 :=
      (_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_self_eq_zero_iff_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW (A - B)).1 hdiag
    exact sub_eq_zero.mp hzero
  · exact _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_comm_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW
  · exact _root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW

def hom [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →ₗ[Real] W) :=
  MetricFiberData.ofFlat (_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.homFlatLinear_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW)
    (_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.hom_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW).1
    (_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.hom_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW).2.1
    (_root_.DifferentialGeometry.Tensor0SBundle.MetricFiberData.hom_nonneg_closedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric DV DW).2.2

def homCLM [AddCommGroup V] [Module Real V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul Real V] [T2Space V]
    [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →L[Real] W) :=
  MetricFiberData.pullback
    (LinearMap.toContinuousLinearMap (𝕜 := Real) (E := V) (F' := W)).symm
    (MetricFiberData.hom DV DW)

end MetricFiberData

def scalarMetricData (x : M) :
  MetricFiberData (Tensor0SSpace 0 I x) :=
  MetricFiberData.pullback
    ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) 0 x).toLinearEquiv.trans
      (continuousMultilinearCurryFin0 Real (TangentSpace I x) Real).toLinearEquiv)
    MetricFiberData.real

def tensor0SMetricStep
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (D : MetricFiberData (Tensor0SSpace s I x)) :
    MetricFiberData (Tensor0SSpace (s + 1) I x) :=
  have hTopAdd0 : IsTopologicalAddGroup (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  letI : IsTopologicalAddGroup (Tensor0SSpace s I x) := hTopAdd0
  have hContAdd0 : ContinuousAdd (Tensor0SSpace s I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  letI : ContinuousAdd (Tensor0SSpace s I x) := hContAdd0
  have hContSMul0 : ContinuousSMul Real (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  letI : ContinuousSMul Real (Tensor0SSpace s I x) := hContSMul0
  letI : ContinuousConstSMul Real (Tensor0SSpace s I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd0
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd0
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd0
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance inferInstance hTopAdd0 hContSMul0
      inferInstance inferInstance inferInstance).finiteDimensional
  MetricFiberData.pullback
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x).toLinearEquiv
    (@MetricFiberData.homCLM
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance
      inferInstance inferInstance inferInstance hTopAdd0 hContSMul0 inferInstance
      (tangentMetricData (I := I) g x).metric D)

def tensor0SMetricData (g : SmoothMetric I M) (x : M) :
    (s : Nat) -> MetricFiberData (Tensor0SSpace s I x)
  | 0 => scalarMetricData (I := I) x
  | 1 => cotangentMetricData (I := I) g x
  | s + 2 =>
      tensor0SMetricStep (I := I) g x (s + 1) (tensor0SMetricData g x (s + 1))

def inner0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) : Real :=
  (tensor0SMetricData (I := I) g x s).inner A B

def normSq0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) : Real :=
  inner0S (I := I) g x s A A

end

end Tensor0SBundle

end DifferentialGeometry
