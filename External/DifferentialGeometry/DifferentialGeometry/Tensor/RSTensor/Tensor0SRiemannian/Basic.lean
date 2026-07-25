import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TwoTensor
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric

set_option autoImplicit false
set_option linter.style.longLine false









namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MetricFiberData

variable {V W : Type*}

def homFlatLinear [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
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

theorem trace_adjoint_comp_eq_sum_inner
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

theorem trace_adjoint_comp_nonneg
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    0 <= LinearMap.trace Real V ((LinearMap.adjoint A).comp A) := by
  rw [trace_adjoint_comp_eq_sum_inner]
  exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg

theorem trace_adjoint_comp_eq_zero_iff
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
      simpa [trace_adjoint_comp_eq_sum_inner] using htrace
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

theorem trace_adjoint_comp_comm
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      LinearMap.trace Real V ((LinearMap.adjoint B).comp A) := by
  rw [trace_adjoint_comp_eq_sum_inner, trace_adjoint_comp_eq_sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact (real_inner_comm (A (stdOrthonormalBasis Real V i))
    (B (stdOrthonormalBasis Real V i))).symm

theorem metric_adjoint_eq_adjoint
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
  apply LinearMap.ext
  intro y
  apply ext_inner_right Real
  intro x
  change DV.inner (MetricFiberData.adjoint DV DW A y) x =
    DV.inner (LinearMap.adjoint A y) x
  rw [MetricFiberData.adjoint_inner]
  rw [← DW.toCore_inner y (A x), ← DV.toCore_inner (LinearMap.adjoint A y) x]
  exact (LinearMap.adjoint_inner_left A x y).symm

theorem homFlatLinear_comm [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A B : V →ₗ[Real] W) :
    homFlatLinear DV DW A B = homFlatLinear DV DW B A := by
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
  have hA := metric_adjoint_eq_adjoint DV DW A
  have hB := metric_adjoint_eq_adjoint DV DW B
  change LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp B) =
    LinearMap.trace Real V ((MetricFiberData.adjoint DV DW B).comp A)
  rw [hA, hB]
  exact trace_adjoint_comp_comm A B

theorem homFlatLinear_nonneg [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    0 <= homFlatLinear DV DW A A := by
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
  have hA := metric_adjoint_eq_adjoint DV DW A
  change 0 <= LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp A)
  rw [hA]
  exact trace_adjoint_comp_nonneg A

theorem homFlatLinear_self_eq_zero_iff [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    homFlatLinear DV DW A A = 0 ↔ A = 0 := by
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
  have hA := metric_adjoint_eq_adjoint DV DW A
  change LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp A) = 0 ↔ A = 0
  rw [hA]
  exact trace_adjoint_comp_eq_zero_iff A

theorem hom_nonneg [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    Function.Injective (homFlatLinear DV DW) ∧
      (forall A B : V →ₗ[Real] W,
        homFlatLinear DV DW A B = homFlatLinear DV DW B A) ∧
      (forall A : V →ₗ[Real] W, 0 <= homFlatLinear DV DW A A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hAB
    have hflat : homFlatLinear DV DW (A - B) = 0 := by
      rw [map_sub, hAB, sub_self]
    have hdiag : homFlatLinear DV DW (A - B) (A - B) = 0 := by
      rw [hflat]
      rfl
    have hzero : A - B = 0 :=
      (homFlatLinear_self_eq_zero_iff DV DW (A - B)).1 hdiag
    exact sub_eq_zero.mp hzero
  · exact homFlatLinear_comm DV DW
  · exact homFlatLinear_nonneg DV DW


end MetricFiberData





end

end Tensor0SBundle
