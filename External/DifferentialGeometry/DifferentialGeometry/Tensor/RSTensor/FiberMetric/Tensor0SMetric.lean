import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap



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

private def homFlatLinear [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
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

private theorem trace_adjoint_comp_eq_sum_inner
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

private theorem trace_adjoint_comp_nonneg
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    0 <= LinearMap.trace Real V ((LinearMap.adjoint A).comp A) := by
  rw [trace_adjoint_comp_eq_sum_inner]
  exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg

private theorem trace_adjoint_comp_eq_zero_iff
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

private theorem trace_adjoint_comp_comm
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

private theorem metric_adjoint_eq_adjoint
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

private theorem homFlatLinear_comm [AddCommGroup V] [Module Real V]
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

private theorem homFlatLinear_nonneg [AddCommGroup V] [Module Real V]
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

private theorem homFlatLinear_self_eq_zero_iff [AddCommGroup V] [Module Real V]
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

private theorem hom_nonneg [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
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

def hom [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →ₗ[Real] W) :=
  MetricFiberData.ofFlat (homFlatLinear DV DW)
    (hom_nonneg DV DW).1
    (hom_nonneg DV DW).2.1
    (hom_nonneg DV DW).2.2

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

def scalarMetricData (_g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 0 I x) :=
  MetricFiberData.pullback
    ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x).toLinearEquiv.trans
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
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x).toLinearEquiv
    (@MetricFiberData.homCLM
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd0 hContSMul0 inferInstance
      (tangentMetricData (I := I) g x).metric D)

def tensor0SMetricData (g : SmoothMetric I M) (x : M) :
    (s : Nat) -> MetricFiberData (Tensor0SSpace s I x)
  | 0 => scalarMetricData (I := I) g x
  | 1 => cotangentMetricData (I := I) g x
  | s + 2 =>
      tensor0SMetricStep (I := I) g x (s + 1) (tensor0SMetricData g x (s + 1))

def inner0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) : Real :=
  (tensor0SMetricData (I := I) g x s).inner A B

def flat0S
    (g : SmoothMetric I M) (x : M) (s : Nat) :
    Tensor0SSpace s I x ≃ₗ[Real] Module.Dual Real (Tensor0SSpace s I x) :=
  (tensor0SMetricData (I := I) g x s).flat

def normSq0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) : Real :=
  inner0S (I := I) g x s A A

@[simp] theorem normSq0S_eq_inner
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A = inner0S (I := I) g x s A A := by
  rfl

theorem inner0S_one_eq_cotangent
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    inner0S (I := I) g x 1 α β =
      cotangentInner (I := I) g x α β := by
  rfl

def tensor0SComponent {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) : Real :=
  A (fun a => frame (slots a))

omit [FiniteDimensional ℝ E] in
@[simp] theorem tensor0SComponent_apply {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) :
    tensor0SComponent (I := I) A frame slots =
      A (fun a => frame (slots a)) := by
  rfl

def coordInner0S
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) *
      tensor0SComponent (I := I) A (fun i => basis i) I0 *
        tensor0SComponent (I := I) B (fun i => basis i) J0

private theorem sum_fin_two_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

private theorem sum_fin_succ_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α] (s : Nat)
    (F : (Fin (s + 1) -> Idx) -> α) :
    (∑ I0 : Fin (s + 1) -> Idx, F I0) =
      ∑ i : Idx, ∑ tail : Fin s -> Idx, F (Fin.cons i tail) := by
  classical
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm
    F (fun p : Idx × (Fin s -> Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr 1
    exact (Fin.cons_self_tail I0).symm

private theorem sum_fin_one_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 -> Idx) -> α) :
    (∑ I0 : Fin 1 -> Idx, F I0) =
      ∑ i : Idx, F (fun _ : Fin 1 => i) := by
  classical
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Idx)
    F (fun i : Idx => F (fun _ : Fin 1 => i))]
  intro I0
  congr 1
  funext a
  simpa [Equiv.funUnique] using congrArg I0 (Subsingleton.elim a (0 : Fin 1))

omit [FiniteDimensional ℝ E] in
private theorem basis_repr_eq_sum_inv_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Z : TangentSpace I x) (i : Idx) :
    basis.repr Z i =
      ∑ j : Idx, gInv i j * g.inner x Z (basis j) := by
  classical
  let Z' : TangentSpace I x :=
    ∑ i : Idx, (∑ j : Idx, gInv i j * g.inner x Z (basis j)) • basis i
  have hZ : Z = Z' := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro l
    calc
      g.inner x Z (basis l)
          = ∑ j : Idx, (if l = j then 1 else 0) *
              g.inner x Z (basis j) := by
            simp
      _ = ∑ j : Idx,
            (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
              g.inner x Z (basis j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [(hinv l j).2]
      _ = ∑ i : Idx,
            (∑ j : Idx, gInv i j * g.inner x Z (basis j)) *
              g.inner x (basis i) (basis l) := by
            calc
              (∑ j : Idx,
                  (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
                    g.inner x Z (basis j))
                  = ∑ j : Idx, ∑ i : Idx,
                      (g.inner x (basis l) (basis i) * gInv i j) *
                        g.inner x Z (basis j) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
              _ = ∑ i : Idx, ∑ j : Idx,
                      (g.inner x (basis l) (basis i) * gInv i j) *
                        g.inner x Z (basis j) := by
                      rw [Finset.sum_comm]
              _ = ∑ i : Idx,
                    (∑ j : Idx, gInv i j * g.inner x Z (basis j)) *
                      g.inner x (basis i) (basis l) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [g.symm x (basis l) (basis i)]
                      ring
      _ = g.inner x Z' (basis l) := by
            simp [Z', map_sum]
  calc
    basis.repr Z i = basis.repr Z' i := by rw [hZ]
    _ = ∑ j : Idx, gInv i j * g.inner x Z (basis j) := by
      change
        basis.repr
            (∑ i : Idx, (∑ j : Idx, gInv i j * g.inner x Z (basis j)) • basis i) i =
          ∑ j : Idx, gInv i j * g.inner x Z (basis j)
      rw [map_sum]
      rw [show
          (∑ x_1 : Idx,
              basis.repr
                ((∑ j : Idx, gInv x_1 j * g.inner x Z (basis j)) • basis x_1)) i =
          ∑ x_1 : Idx,
              (basis.repr
                ((∑ j : Idx, gInv x_1 j * g.inner x Z (basis j)) • basis x_1)) i by
        simp]
      simp only [map_smul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hi
        simp at hi

private theorem hom_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j)) := by
  change LinearMap.trace Real (TangentSpace I x)
      ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A).comp A) =
    ∑ i : Idx, ∑ j : Idx,
      gInv i j * D.inner (A (basis i)) (A (basis j))
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A).comp A)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change
    g.inner x
        ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A)
          (A (basis i)))
        (basis j) =
      D.inner (A (basis i)) (A (basis j))
  rw [← TangentMetricData.inner_eq (I := I)
    (tangentMetricData (I := I) g x)
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A)
      (A (basis i)))
    (basis j)]
  exact MetricFiberData.adjoint_inner
    (tangentMetricData (I := I) g x).metric D A (A (basis i)) (basis j)

private theorem hom_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j)) := by
  rw [MetricFiberData.homFlatLinear_comm
    (tangentMetricData (I := I) g x).metric D A B]
  change LinearMap.trace Real (TangentSpace I x)
      ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B).comp A) =
    ∑ i : Idx, ∑ j : Idx,
      gInv i j * D.inner (A (basis i)) (B (basis j))
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B).comp A)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change
    g.inner x
        ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B)
          (A (basis i)))
        (basis j) =
      D.inner (A (basis i)) (B (basis j))
  rw [← TangentMetricData.inner_eq (I := I)
    (tangentMetricData (I := I) g x)
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B)
      (A (basis i)))
    (basis j)]
  exact MetricFiberData.adjoint_inner
    (tangentMetricData (I := I) g x).metric D B (A (basis i)) (basis j)

private theorem homCLM_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j)) := by
  exact hom_normSq_eq_basis (I := I) g x basis gInv hinv D A.toLinearMap

private theorem homCLM_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j)) := by
  exact hom_inner_eq_basis (I := I) g x basis gInv hinv D A.toLinearMap B.toLinearMap

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_one_apply
    {x : M} (A : Tensor0SSpace 2 I x)
    (X Y : TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A X)
        (fun _ : Fin 1 => Y) =
      A (fun a : Fin 2 => if a = 0 then X else Y) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (1 + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
        X)
        (fun _ : Fin 1 => Y)) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
        (fun a : Fin 2 => if a = 0 then X else Y)
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  funext a
  fin_cases a <;> simp [Fin.cons_zero]

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_apply_cons
    {x : M} (s : Nat) (A : Tensor0SSpace (s + 1) I x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (s + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        X)
        tail) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        (Fin.cons X tail)
  rw [continuousMultilinearCurryLeftEquiv_apply]

theorem normSq0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 2 A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  classical
  have hTopAdd1 : IsTopologicalAddGroup (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : IsTopologicalAddGroup (Tensor0SSpace 1 I x) := hTopAdd1
  have hContSMul1 : ContinuousSMul Real (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : ContinuousSMul Real (Tensor0SSpace 1 I x) := hContSMul1
  have hContAdd1 : ContinuousAdd (Tensor0SSpace 1 I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace 1 I x) := hContAdd1
  haveI : ContinuousConstSMul Real (Tensor0SSpace 1 I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace 1 I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd1
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd1
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd1
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance inferInstance hTopAdd1 hContSMul1
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold normSq0S inner0S MetricFiberData.inner
  change
    (tensor0SMetricStep (I := I) g x 1 (cotangentMetricData (I := I) g x)).flat A A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)
  unfold tensor0SMetricStep MetricFiberData.pullback MetricFiberData.homCLM
    MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric
      (cotangentMetricData (I := I) g x)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)
  rw [hom_normSq_eq_basis (I := I) g x basis gInv hinv
    (cotangentMetricData (I := I) g x)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)]
  calc
    (∑ i : Idx, ∑ k : Idx,
        gInv i k *
          (cotangentMetricData (I := I) g x).inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis k)))
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
            gInv i k *
              (gInv j l *
                A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
                  A (fun a : Fin 2 => if a = 0 then basis k else basis l)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [cotangentMetricData_inner_eq_coord (I := I) g x basis gInv hinv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [cotangentToDual_apply, cotangentToDual_apply]
          rw [tensor0S_curry_one_apply, tensor0S_curry_one_apply]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring

theorem inner0S_two_eq_coord_direct
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  classical
  have hTopAdd1 : IsTopologicalAddGroup (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : IsTopologicalAddGroup (Tensor0SSpace 1 I x) := hTopAdd1
  have hContSMul1 : ContinuousSMul Real (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : ContinuousSMul Real (Tensor0SSpace 1 I x) := hContSMul1
  have hContAdd1 : ContinuousAdd (Tensor0SSpace 1 I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace 1 I x) := hContAdd1
  haveI : ContinuousConstSMul Real (Tensor0SSpace 1 I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace 1 I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd1
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd1
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd1
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance inferInstance hTopAdd1 hContSMul1
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold inner0S MetricFiberData.inner
  change
    (tensor0SMetricStep (I := I) g x 1 (cotangentMetricData (I := I) g x)).flat A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)
  unfold tensor0SMetricStep MetricFiberData.pullback MetricFiberData.homCLM
    MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric
      (cotangentMetricData (I := I) g x)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)
  rw [hom_inner_eq_basis (I := I) g x basis gInv hinv
    (cotangentMetricData (I := I) g x)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B).toLinearMap)]
  calc
    (∑ i : Idx, ∑ k : Idx,
        gInv i k *
          (cotangentMetricData (I := I) g x).inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B) (basis k)))
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
            gInv i k *
              (gInv j l *
                A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
                  B (fun a : Fin 2 => if a = 0 then basis k else basis l)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [cotangentMetricData_inner_eq_coord (I := I) g x basis gInv hinv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [cotangentToDual_apply, cotangentToDual_apply]
          rw [tensor0S_curry_one_apply, tensor0S_curry_one_apply]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring

private theorem inner0S_zero_eq
    (g : SmoothMetric I M) (x : M)
    (A B : Tensor0SSpace 0 I x) :
    inner0S (I := I) g x 0 A B = A Fin.elim0 * B Fin.elim0 := by
  unfold inner0S tensor0SMetricData scalarMetricData MetricFiberData.inner
    MetricFiberData.pullback MetricFiberData.real MetricFiberData.ofFlat
    MetricFiberData.realFlatLinear
  change
    ((continuousMultilinearCurryFin0 Real (TangentSpace I x) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x) A)) *
      ((continuousMultilinearCurryFin0 Real (TangentSpace I x) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x) B)) =
      A Fin.elim0 * B Fin.elim0
  simp [tensor0SSpace_continuousLinearEquiv]
  congr

omit [FiniteDimensional ℝ E] in
private theorem coordInner0S_zero_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace 0 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 0 gInv A B basis =
      A Fin.elim0 * B Fin.elim0 := by
  classical
  unfold coordInner0S tensor0SComponent
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton]
  congr <;> funext a <;> exact Fin.elim0 a

omit [FiniteDimensional ℝ E] in
private theorem coordInner0S_one_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (α β : Tensor0SSpace 1 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 1 gInv α β basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro j _
  simp [cotangentToDual_apply]

private theorem tensor0SMetricStep_inner_eq_coordStep
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData (Tensor0SSpace s I x))
    (A B : Tensor0SSpace (s + 1) I x) :
    (tensor0SMetricStep (I := I) g x s D).inner A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j)) := by
  classical
  have hTopAdd0 : IsTopologicalAddGroup (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  haveI : IsTopologicalAddGroup (Tensor0SSpace s I x) := hTopAdd0
  have hContSMul0 : ContinuousSMul Real (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  haveI : ContinuousSMul Real (Tensor0SSpace s I x) := hContSMul0
  have hContAdd0 : ContinuousAdd (Tensor0SSpace s I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace s I x) := hContAdd0
  haveI : ContinuousConstSMul Real (Tensor0SSpace s I x) := inferInstance
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
  unfold MetricFiberData.inner tensor0SMetricStep MetricFiberData.pullback
    MetricFiberData.homCLM MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric D
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
  rw [hom_inner_eq_basis (I := I) g x basis gInv hinv D
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A).toLinearMap)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B).toLinearMap)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rfl

omit [FiniteDimensional ℝ E] in
private theorem coordInner0S_succ_summand_eq
    {Idx : Type*}  {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) (tailI tailJ : Fin s -> Idx) :
    ((∏ a : Fin (s + 1),
        gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
          (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
        A (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
      B (fun a : Fin (s + 1) =>
        basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
      (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
          ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            (fun a : Fin s => basis (tailI a))) *
        ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
          (fun a : Fin s => basis (tailJ a)) := by
  rw [Fin.prod_univ_succ]
  rw [tensor0S_curry_apply_cons, tensor0S_curry_apply_cons]
  have hA :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))) =
        Fin.cons (basis i) (fun a : Fin s => basis (tailI a)) := by
    funext a
    cases a using Fin.cases <;> simp
  have hB :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
        Fin.cons (basis j) (fun a : Fin s => basis (tailJ a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hA, hB]
  simp [Fin.cons_zero, Fin.cons_succ]

omit [FiniteDimensional ℝ E] in
set_option maxHeartbeats 800000 in
private theorem coordInner0S_succ_eq
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) (s + 1) gInv A B basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordInner0S (I := I) (x := x) s gInv
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
            basis := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_succ_fun s]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ tailI : Fin s -> Idx,
        ∑ J0 : Fin (s + 1) -> Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)) (J0 a)) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
            B (fun a : Fin (s + 1) => basis (J0 a)))
        =
        ∑ tailI : Fin s -> Idx, ∑ j : Idx, ∑ tailJ : Fin s -> Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
                (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
            B (fun a : Fin (s + 1) =>
              basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) := by
          apply Finset.sum_congr rfl
          intro tailI _
          rw [sum_fin_succ_fun s]
    _ =
        ∑ tailI : Fin s -> Idx, ∑ j : Idx, ∑ tailJ : Fin s -> Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro tailI _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro tailJ _
          exact coordInner0S_succ_summand_eq (I := I) s gInv A B basis i j tailI tailJ
    _ =
        ∑ j : Idx, ∑ tailI : Fin s -> Idx, ∑ tailJ : Fin s -> Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ j : Idx,
          gInv i j *
            ∑ tailI : Fin s -> Idx, ∑ tailJ : Fin s -> Idx,
              (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
                ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                  (fun a : Fin s => basis (tailI a)) *
                  ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
                    (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailI _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailJ _
          ring

theorem inner0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      coordInner0S (I := I) (x := x) s gInv A B basis := by
  induction s with
  | zero =>
      rw [inner0S_zero_eq (I := I) g x A B,
        coordInner0S_zero_eq (I := I) gInv A B basis]
  | succ s ih =>
      cases s with
      | zero =>
          rw [inner0S_one_eq_cotangent (I := I) g x A B,
            cotangentInner_eq_coord (I := I) g x basis gInv hinv A B,
            coordInner0S_one_eq (I := I) gInv A B basis]
      | succ s =>
          rw [coordInner0S_succ_eq (I := I) (s + 1) gInv A B basis]
          unfold inner0S
          change
            (tensor0SMetricStep (I := I) g x (s + 1)
              (tensor0SMetricData (I := I) g x (s + 1))).inner A B =
              ∑ i : Idx, ∑ j : Idx,
                gInv i j *
                  coordInner0S (I := I) (x := x) (s + 1) gInv
                    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                      (basis i))
                    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                      (basis j))
                    basis
          rw [tensor0SMetricStep_inner_eq_coordStep (I := I) g x (s + 1)
            basis gInv hinv (tensor0SMetricData (I := I) g x (s + 1)) A B]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change
            gInv i j *
                inner0S (I := I) g x (s + 1)
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                    (basis i)))
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                    (basis j))) =
              gInv i j *
                coordInner0S (I := I) (x := x) (s + 1) gInv
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                    (basis i)))
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                    (basis j)))
                  basis
          rw [ih]

theorem normSq0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      coordInner0S (I := I) (x := x) s gInv A A basis := by
  rw [normSq0S_eq_inner, inner0S_eq_coord (I := I) g x s basis gInv hinv]

theorem inner0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  exact inner0S_two_eq_coord_direct (I := I) g x basis gInv hinv A B

theorem coord_normSq0S_eq_coord
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    (A : Tensor0SSpace s I x) :
    coordInner0S (I := I) (x := x) s gInv₁ A A basis₁ =
      coordInner0S (I := I) (x := x) s gInv₂ A A basis₂ := by
  rw [← normSq0S_eq_coord (I := I) g x s basis₁ gInv₁ hinv₁ A,
    ← normSq0S_eq_coord (I := I) g x s basis₂ gInv₂ hinv₂ A]
theorem normSq0S_nonneg
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    0 <= normSq0S (I := I) g x s A := by
  exact (tensor0SMetricData (I := I) g x s).nonneg A


end

end Tensor0SBundle
