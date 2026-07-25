import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.RoughLapNablaK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.FrozenSlotAllK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannReactionBound

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
























noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]








def nablaKRmFrozenSlotField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  freezeAllBut0SField (I := I) (M := M) (nablaKRm04Field (I := I) S t k) q Y

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRmFrozenSlotField_apply_vec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) (W : TangentSpace I x) :
    nablaKRmFrozenSlotField (I := I) S t k q Y x (fun _ : Fin 1 => W) =
      nablaKRm04Field (I := I) S t k x (Function.update (fun i : Fin (4 + k) => Y i x) q W) :=
  freezeAllBut0SField_apply_vec (I := I) (M := M) (nablaKRm04Field (I := I) S t k) q Y x W


def nablaKRmNablaFrozenSlotField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 (S.family.connection t) (nablaKRmFrozenSlotField (I := I) S t k q Y)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaKRmFrozenSlotField (I := I) S t k q Y))

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRmNablaFrozenSlotField_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t) (nablaKRmFrozenSlotField (I := I) S t k q Y)
      (nablaKRmNablaFrozenSlotField (I := I) S t k q Y) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 (S.family.connection t) (nablaKRmFrozenSlotField (I := I) S t k q Y)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaKRmFrozenSlotField (I := I) S t k q Y))

set_option backward.isDefEq.respectTransparency false in



omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRmFrozenSlot_chartBasis_contMDiffOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α : M) (j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real) ∞
      (fun b : M =>
        nablaKRmFrozenSlotField (I := I) S t k q Y b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hv_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun b : M =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
            (chartBasisVecFiber (I := I) α j b)) x₀ :=
    (chartBasisVec_contMDiffOn (I := I) α j).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds
        (by
          rw [trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M)]
          exact hx₀))
  have h_eval := TensorMultilinear.contMDiffAt_section_apply_gen
    (𝕜 := Real) (I := I) (M := M) (n := 1) (x₀ := x₀)
    (T := fun b : M => (freezeAllBut0SField (I := I) (M := M) (nablaKRm04Field (I := I) S t k) q Y) b)
    ((freezeAllBut0SField (I := I) (M := M) (nablaKRm04Field (I := I) S t k) q Y).contMDiff x₀)
    (v := fun _ : Fin 1 => fun b : M => chartBasisVecFiber (I := I) α j b)
    (fun _ => hv_at)
  simpa [nablaKRmFrozenSlotField, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv_apply] using h_eval

open DifferentialGeometry.Integral.DivergenceTheorem in


def nablaKRmFrozenSlotSharpSection
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk
    (fun y : M =>
      cotangentSharp_gen (I := I) (S.base.metric t) y
        (nablaKRmFrozenSlotField (I := I) S t k q Y y))
    (cotangentSharp_gen_contMDiff_total (I := I) (S.base.metric t)
      (β := fun y : M => nablaKRmFrozenSlotField (I := I) S t k q Y y)
      (fun α j => nablaKRmFrozenSlot_chartBasis_contMDiffOn (I := I) S t k q Y α j))

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
@[simp] theorem nablaKRmFrozenSlotSharpSection_apply
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (y : M) :
    nablaKRmFrozenSlotSharpSection (I := I) S t k q Y y =
      cotangentSharp_gen (I := I) (S.base.metric t) y
        (nablaKRmFrozenSlotField (I := I) S t k q Y y) :=
  rfl

open DifferentialGeometry.Integral.DivergenceTheorem in


omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem nablaKRmFrozenSlotSharp_mdiffAt
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDiffAt
      (T% (fun y : M =>
        cotangentSharp_gen (I := I) (S.base.metric t) y
          (nablaKRmFrozenSlotField (I := I) S t k q Y y))) x :=
  cotangentSharp_gen_mdiffAt (I := I) (S.base.metric t)
    (β := fun y : M => nablaKRmFrozenSlotField (I := I) S t k q Y y)
    (fun α j => nablaKRmFrozenSlot_chartBasis_contMDiffOn (I := I) S t k q Y α j) x





omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem nablaKRmFrozenSlot_eval
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (q : Fin (4 + k))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Y : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M)
    (hYzero : ∀ i : Fin (4 + k), i ≠ q →
      ((S.family.connection (t : Real) (fun p : M => Y i p) x₀) (X x₀)) = 0)
    (U : TangentSpace I x₀) :
    nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Y x₀
        (vec2 (I := I) (X x₀) U) =
      nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀
        (Fin.cons (X x₀)
          (Function.update (fun i : Fin (4 + k) => Y i x₀) q U)) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have hBval :
      nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Y x₀
          (vec2 (I := I) (X x₀) U) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (S.family.connection (t : Real))
          (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Y) x₀
          (vec2 (I := I) (X x₀) U) := rfl
  have hAval :
      nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀
          (Fin.cons (X x₀)
            (Function.update (fun i : Fin (4 + k) => Y i x₀) q U)) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (4 + k) (S.family.connection (t : Real)) (nablaKRm04Field (I := I) S (t : Real) k) x₀
          (Fin.cons (X x₀)
            (Function.update (fun i : Fin (4 + k) => Y i x₀) q U)) := rfl
  rw [hBval, hAval]
  exact allBut0SFreezeNabla (I := I) (S.family.connection (t : Real)) hcov
    (nablaKRm04Field (I := I) S (t : Real) k) q X Y hYzero U




def nablaKRmRaiseSlotSections
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ![Vb, Vc, Vm q, nablaKRmFrozenSlotSharpSection (I := I) S t k q Vm]

open DifferentialGeometry.Integral.DivergenceTheorem in




omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem nablaKRmRaise_summand_covDeriv
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) (k : ℕ) (q : Fin (4 + k))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin (4 + k),
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    extDerivFun (I := I)
        (fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm y))))
        x₀ (X x₀) =
      nablaRm04Field (I := I) S (t : Real) x₀
          (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀))) +
        S.base.rm04 (t : Real) x₀
          (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀)))) := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def
  set W : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    nablaKRmRaiseSlotSections (I := I) S (t : Real) k q Vb Vc Vm with hW_def
  have hW0 : W 0 = Vb := rfl
  have hW1 : W 1 = Vc := rfl
  have hW2 : W 2 = Vm q := rfl
  have hW3 : W 3 = nablaKRmFrozenSlotSharpSection (I := I) S (t : Real) k q Vm := rfl
  have heval :=
    (nablaRm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X W x₀
  have hscalar :
      (fun y : M => S.base.rm04 (t : Real) y (fun a : Fin 4 => W a y)) =
        fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm y))) := by
    funext y
    congr 1
    funext a
    fin_cases a <;>
      simp [hW_def, nablaKRmRaiseSlotSections, vec4, nablaKRmFrozenSlotSharpSection_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcons :
      (Fin.cons (X x₀) (fun a : Fin 4 => W a x₀) : Fin 5 → TangentSpace I x₀) =
        vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
          (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
            (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀)) := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · rfl
    · rw [Fin.cons_succ]
      fin_cases j <;>
        simp [hW_def, nablaKRmRaiseSlotSections, vec5, nablaKRmFrozenSlotSharpSection_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcorr :
      (∑ a : Fin 4,
          S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) a
              ((cov (fun p : M => W a p) x₀) (X x₀)))) =
        S.base.rm04 (t : Real) x₀
          (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀)))) := by
    rw [Fin.sum_univ_four]
    have hc0 : (cov (fun p : M => W 0 p) x₀) (X x₀) = 0 := by rw [hW0]; exact hVb
    have hc1 : (cov (fun p : M => W 1 p) x₀) (X x₀) = 0 := by rw [hW1]; exact hVc
    have hc2 : (cov (fun p : M => W 2 p) x₀) (X x₀) = 0 := by rw [hW2]; exact hVm q
    have hc3 :
        (cov (fun p : M => W 3 p) x₀) (X x₀) =
          cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
              (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀)) := by
      have hsharp :=
        cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
          cov (S.base.metric (t : Real))
          (solution_isMetricCompatible (I := I) S (t : Real))
          (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm)
          (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm)
          (nablaKRmNablaFrozenSlotField_realizes (I := I) S (t : Real) k q Vm)
          X x₀
          (nablaKRmFrozenSlotSharp_mdiffAt (I := I) S (t : Real) k q Vm x₀)
      rw [hW3]
      simpa [nablaKRmFrozenSlotSharpSection_apply] using hsharp
    rw [hc0, hc1, hc2, hc3]
    rw [show
        S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) 0 (0 : TangentSpace I x₀)) = 0 from
      (S.base.rm04 (t : Real) x₀).map_update_zero _ 0]
    rw [show
        S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) 1 (0 : TangentSpace I x₀)) = 0 from
      (S.base.rm04 (t : Real) x₀).map_update_zero _ 1]
    rw [show
        S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) 2 (0 : TangentSpace I x₀)) = 0 from
      (S.base.rm04 (t : Real) x₀).map_update_zero _ 2]
    simp only [zero_add, add_zero]
    congr 1
    funext b
    fin_cases b <;>
      simp [hW_def, nablaKRmRaiseSlotSections, vec4, Function.update]
  rw [← hscalar]
  rw [hcons] at heval
  rw [hcorr] at heval
  linarith [heval]




def nablaKSlotSections {k : ℕ}
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin (4 + (k + 2)) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  Fin.cons Vb (Fin.cons Vc Vm)



omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nablaKSlotSections_apply {k : ℕ}
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (y : M) :
    (fun a : Fin (4 + (k + 2)) => nablaKSlotSections (I := I) Vb Vc Vm a y) =
      metricTraceInput (I := I) (Vb y) (Vc y) (fun i : Fin (4 + k) => Vm i y) := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun l => ?_) j
    · rfl
    · rfl







omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaK_antisym_eq_covDeriv_curvatureAction
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x₀ : M)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin (4 + k),
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin (4 + k) => Vm i x₀))) -
      nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin (4 + k) => Vm i x₀))) =
      extDerivFun (I := I)
        (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (nablaKRm04Field (I := I) S (t : Real) k y)
            (Vb y) (Vc y) (fun i : Fin (4 + k) => Vm i y))
        x₀ (X x₀) := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def
  set Wbc := nablaKSlotSections (I := I) (k := k) Vb Vc Vm with hWbc_def
  set Wcb := nablaKSlotSections (I := I) (k := k) Vc Vb Vm with hWcb_def

  have hWbc_cov : ∀ a : Fin (4 + (k + 2)), (cov (fun p : M => Wbc a p) x₀) (X x₀) = 0 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [hWbc_def, nablaKSlotSections] using hVb
    · refine Fin.cases ?_ (fun l => ?_) j
      · simpa [hWbc_def, nablaKSlotSections] using hVc
      · simpa [hWbc_def, nablaKSlotSections] using hVm l
  have hWcb_cov : ∀ a : Fin (4 + (k + 2)), (cov (fun p : M => Wcb a p) x₀) (X x₀) = 0 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [hWcb_def, nablaKSlotSections] using hVc
    · refine Fin.cases ?_ (fun l => ?_) j
      · simpa [hWcb_def, nablaKSlotSections] using hVb
      · simpa [hWcb_def, nablaKSlotSections] using hVm l

  have hbc :=
    (nablaKRm04Field_realizes (I := I) S (t : Real) (k + 2)).eval_smooth_slots X Wbc x₀
  have hcb :=
    (nablaKRm04Field_realizes (I := I) S (t : Real) (k + 2)).eval_smooth_slots X Wcb x₀
  rw [← hcov_def] at hbc hcb
  have hbc_corr :
      (∑ a : Fin (4 + (k + 2)),
          nablaKRm04Field (I := I) S (t : Real) (k + 2) x₀
            (Function.update (fun b : Fin (4 + (k + 2)) => Wbc b x₀) a
              ((cov (fun p : M => Wbc a p) x₀) (X x₀)))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hWbc_cov a]
    exact (nablaKRm04Field (I := I) S (t : Real) (k + 2) x₀).map_update_zero _ a
  have hcb_corr :
      (∑ a : Fin (4 + (k + 2)),
          nablaKRm04Field (I := I) S (t : Real) (k + 2) x₀
            (Function.update (fun b : Fin (4 + (k + 2)) => Wcb b x₀) a
              ((cov (fun p : M => Wcb a p) x₀) (X x₀)))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hWcb_cov a]
    exact (nablaKRm04Field (I := I) S (t : Real) (k + 2) x₀).map_update_zero _ a
  have hWbc_x : (fun a : Fin (4 + (k + 2)) => Wbc a x₀) =
      metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin (4 + k) => Vm i x₀) :=
    nablaKSlotSections_apply (I := I) (k := k) Vb Vc Vm x₀
  have hWcb_x : (fun a : Fin (4 + (k + 2)) => Wcb a x₀) =
      metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin (4 + k) => Vm i x₀) :=
    nablaKSlotSections_apply (I := I) (k := k) Vc Vb Vm x₀
  rw [hbc_corr, sub_zero] at hbc
  rw [hcb_corr, sub_zero] at hcb
  rw [hWbc_x] at hbc
  rw [hWcb_x] at hcb


  have ebc :
      nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin (4 + k) => Vm i x₀))) =
        extDerivFun (I := I)
          (fun p : M =>
            nablaKRm04Field (I := I) S (t : Real) (k + 2) p (fun a : Fin (4 + (k + 2)) => Wbc a p))
          x₀ (X x₀) := hbc
  have ecb :
      nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin (4 + k) => Vm i x₀))) =
        extDerivFun (I := I)
          (fun p : M =>
            nablaKRm04Field (I := I) S (t : Real) (k + 2) p (fun a : Fin (4 + (k + 2)) => Wcb a p))
          x₀ (X x₀) := hcb
  rw [ebc, ecb]
  have hmdiff_bc :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          nablaKRm04Field (I := I) S (t : Real) (k + 2) p (fun a : Fin (4 + (k + 2)) => Wbc a p)) x₀ :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (nablaKRm04Field (I := I) S (t : Real) (k + 2)) Wbc x₀).mdifferentiableAt (by simp)
  have hmdiff_cb :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          nablaKRm04Field (I := I) S (t : Real) (k + 2) p (fun a : Fin (4 + (k + 2)) => Wcb a p)) x₀ :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (nablaKRm04Field (I := I) S (t : Real) (k + 2)) Wcb x₀).mdifferentiableAt (by simp)
  rw [← extDerivFun_sub_at (I := I) (X x₀) hmdiff_bc hmdiff_cb]
  have hfield :
      (fun y : M =>
          nablaKRm04Field (I := I) S (t : Real) (k + 2) y (fun a : Fin (4 + (k + 2)) => Wbc a y) -
            nablaKRm04Field (I := I) S (t : Real) (k + 2) y (fun a : Fin (4 + (k + 2)) => Wcb a y)) =
        fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (nablaKRm04Field (I := I) S (t : Real) k y)
            (Vb y) (Vc y) (fun i : Fin (4 + k) => Vm i y) := by
    funext y
    rw [nablaKSlotSections_apply (I := I) (k := k) Vb Vc Vm y,
      nablaKSlotSections_apply (I := I) (k := k) Vc Vb Vm y]
    exact nablaKRm04_ricciIdentityAt (I := I) S hS t k y
      (Vb y) (Vc y) (fun i : Fin (4 + k) => Vm i y)
  rw [hfield]











omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem nablaK_antisym_eq_rm04_raise_leibniz
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x₀ : M)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin (4 + k),
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin (4 + k) => Vm i x₀))) -
      nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin (4 + k) => Vm i x₀))) =
      -∑ q : Fin (4 + k),
        (nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
                (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀))) +
          S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀))))) := by
  classical
  rw [nablaK_antisym_eq_covDeriv_curvatureAction (I := I) S hS t k x₀ X Vb Vc Vm hVb hVc hVm]

  have hKfield :
      (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (nablaKRm04Field (I := I) S (t : Real) k y) (Vb y) (Vc y)
            (fun i : Fin (4 + k) => Vm i y)) =
        fun y : M =>
          -∑ q : Fin (4 + k),
            S.base.rm04 (t : Real) y
              (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
                (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                  (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm y))) := by
    funext y
    rw [curvatureAction0SAt_eq_rm04_raise (I := I) (S.base.metric (t : Real))
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) y)
      (solution_rm04LowersRm13At (I := I) S (t : Real) y)
      (nablaKRm04Field (I := I) S (t : Real) k y) (Vb y) (Vc y)
      (fun i : Fin (4 + k) => Vm i y)]
    rfl
  rw [hKfield]
  set g : Fin (4 + k) → M → Real := fun q y =>
    S.base.rm04 (t : Real) y
      (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
        (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
          (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm y))) with hg_def
  have hmdiff_q : ∀ q : Fin (4 + k),
      MDifferentiableAt I 𝓘(Real, Real) (g q) x₀ := by
    intro q
    have h := (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (S.base.rm04 (t : Real))
      (nablaKRmRaiseSlotSections (I := I) S (t : Real) k q Vb Vc Vm) x₀).mdifferentiableAt (by simp)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [hg_def]
    dsimp only
    congr 1
    funext a
    fin_cases a <;>
      simp [nablaKRmRaiseSlotSections, vec4, nablaKRmFrozenSlotSharpSection_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  have hstep3 :
      extDerivFun (I := I) (fun y : M => -∑ q : Fin (4 + k), g q y) x₀ (X x₀) =
        -∑ q : Fin (4 + k), extDerivFun (I := I) (g q) x₀ (X x₀) := by
    have hsumfun : (fun y : M => ∑ q : Fin (4 + k), g q y) =
        (Finset.univ : Finset (Fin (4 + k))).sum g := by
      funext y; simp [Finset.sum_apply]
    have hneg :
        extDerivFun (I := I) (fun y : M => -∑ q : Fin (4 + k), g q y) x₀ (X x₀) =
          -extDerivFun (I := I) (fun y : M => ∑ q : Fin (4 + k), g q y) x₀ (X x₀) :=
      extDerivFun_neg_at (I := I) (f := fun y : M => ∑ q : Fin (4 + k), g q y) (X x₀)
        (by
          rw [hsumfun]
          exact MDifferentiableAt.sum (𝕜 := Real) (I := I)
            (t := (Finset.univ : Finset (Fin (4 + k)))) (fun q _ => hmdiff_q q))
    rw [hneg, hsumfun]
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real (I := I)
      (t := (Finset.univ : Finset (Fin (4 + k)))) g (X x₀) (fun q _ => hmdiff_q q)]
  rw [hstep3]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hg_def]
  exact nablaKRmRaise_summand_covDeriv (I := I) S t x₀ k q X Vb Vc Vm hVb hVc (fun i => hVm i)



section AllKBound

variable {n : ℕ}












omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_nablaK_antisym_covConst_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x₀ : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin (4 + k) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (a b c : Fin n) (m : Fin (4 + k) → Fin n)
    (hXa : X x₀ = basis a) (hVb : Vb x₀ = basis b) (hVc : Vc x₀ = basis c)
    (hVm : ∀ i : Fin (4 + k), Vm i x₀ = basis (m i))
    (hVbcov : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVccov : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVmcov : ∀ i : Fin (4 + k),
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    |nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin (4 + k) => Vm i x₀))) -
        nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin (4 + k) => Vm i x₀)))| ≤
      ((4 + k : ℕ) : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
              nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
            Real.sqrt (compNormSqMulti (fun idx : Fin (4 + k) → Fin n =>
              nablaKRm04Field (I := I) S (t : Real) k x₀ (fun p => basis (idx p)))) +
          Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
              S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) *
            Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
              nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p))))) := by
  classical
  set g := S.base.metric (t : Real) with hg_def
  set Nnab : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) with hNnab
  set NRm : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
      S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) with hNRm
  set Nk : Real := Real.sqrt (compNormSqMulti (fun idx : Fin (4 + k) → Fin n =>
      nablaKRm04Field (I := I) S (t : Real) k x₀ (fun p => basis (idx p)))) with hNk
  set Nk1 : Real := Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
      nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p)))) with hNk1
  have hNnabnn : 0 ≤ Nnab := Real.sqrt_nonneg _
  have hNRmnn : 0 ≤ NRm := Real.sqrt_nonneg _
  have hNknn : 0 ≤ Nk := Real.sqrt_nonneg _
  have hNk1nn : 0 ≤ Nk1 := Real.sqrt_nonneg _
  have hcardnn : (0 : Real) ≤ (Fintype.card (Fin n) : Real) := by positivity
  rw [nablaK_antisym_eq_rm04_raise_leibniz (I := I) S hS t k x₀ X Vb Vc Vm
    hVbcov hVccov hVmcov]
  rw [abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hper : ∀ q : Fin (4 + k),
      |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀))) +
          S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀))))| ≤
        (Fintype.card (Fin n) : Real) * (Nnab * Nk) +
          (Fintype.card (Fin n) : Real) * (NRm * Nk1) := by
    intro q
    refine le_trans (abs_add_le _ _) ?_

    have hT1a :
        |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀)))| ≤
          (Fintype.card (Fin n) : Real) * (Nnab * Nk) := by
      have hCS := abs_tensor05_sharp_last_le (I := I) g basis horth
        (nablaRm04Field (I := I) S (t : Real) x₀)
        (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
        (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀)
      refine le_trans hCS ?_
      have hf1 :
          Real.sqrt (∑ e : Fin n,
              (nablaRm04Field (I := I) S (t : Real) x₀
                (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀) (basis e))) ^ 2) ≤ Nnab := by
        rw [hNnab]
        refine Real.sqrt_le_sqrt ?_
        rw [hXa, hVb, hVc, hVm q]
        have hidx : ∀ e : Fin n,
            vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e) =
              fun p : Fin 5 => basis ((Function.update ![a, b, c, m q, a] 4 e) p) := by
          intro e; funext p; fin_cases p <;> simp [vec5, Function.update]
        simp only [hidx]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (nablaRm04Field (I := I) S (t : Real) x₀) basis ![a, b, c, m q, a] 4
      have hf2 :
          Real.sqrt (∑ e : Fin n,
              (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀
                (fun _ : Fin 1 => basis e)) ^ 2) ≤ Nk := by
        rw [hNk]
        refine Real.sqrt_le_sqrt ?_
        have hβ : ∀ e : Fin n,
            (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x₀
                (fun _ : Fin 1 => basis e)) ^ 2 =
              (nablaKRm04Field (I := I) S (t : Real) k x₀
                (fun p : Fin (4 + k) => basis ((Function.update m q e) p))) ^ 2 := by
          intro e
          rw [nablaKRmFrozenSlotField_apply_vec (I := I) S (t : Real) k q Vm x₀ (basis e)]
          congr 2
          funext p
          by_cases hp : p = q
          · subst hp; simp [Function.update]
          · simp [Function.update, hp, hVm p]
        rw [Finset.sum_congr rfl (fun e _ => hβ e)]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (nablaKRm04Field (I := I) S (t : Real) k x₀) basis m q
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hf1 hf2 (Real.sqrt_nonneg _) hNnabnn) hcardnn

    have hT1b :
        |S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀))))| ≤
          (Fintype.card (Fin n) : Real) * (NRm * Nk1) := by
      have hCS := abs_tensor04_sharp_last_le (I := I) g basis horth
        (S.base.rm04 (t : Real) x₀)
        (Vb x₀) (Vc x₀) (Vm q x₀)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
          (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀))
      refine le_trans hCS ?_
      have hf1 :
          Real.sqrt (∑ e : Fin n,
              (S.base.rm04 (t : Real) x₀
                (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀) (basis e))) ^ 2) ≤ NRm := by
        rw [hNRm]
        refine Real.sqrt_le_sqrt ?_
        rw [hVb, hVc, hVm q]
        have hidx : ∀ e : Fin n,
            vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e) =
              fun p : Fin 4 => basis ((Function.update ![b, c, m q, b] 3 e) p) := by
          intro e; funext p; fin_cases p <;> simp [vec4, Function.update]
        simp only [hidx]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (S.base.rm04 (t : Real) x₀) basis ![b, c, m q, b] 3
      have hf2 :
          Real.sqrt (∑ e : Fin n,
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀)
                (fun _ : Fin 1 => basis e)) ^ 2) ≤ Nk1 := by
        have hcomb : ∀ e : Fin n,
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x₀) (X x₀)
                (fun _ : Fin 1 => basis e)) ^ 2 =
              (nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀
                (fun p : Fin (4 + k + 1) =>
                  basis ((Function.update (Fin.cons a m : Fin (4 + k + 1) → Fin n)
                    q.succ e) p))) ^ 2 := by
          intro e
          rw [tensor0S_curry_apply_cons]
          have hcons2 :
              (Fin.cons (X x₀) (fun _ : Fin 1 => basis e) : Fin 2 → TangentSpace I x₀) =
                vec2 (I := I) (X x₀) (basis e) := by
            funext p; fin_cases p <;> rfl
          rw [hcons2, nablaKRmFrozenSlot_eval (I := I) S hS t k q X Vm x₀
            (fun i _ => hVmcov i) (basis e)]
          have htuple :
              (Fin.cons (X x₀)
                  (Function.update (fun i : Fin (4 + k) => Vm i x₀) q (basis e)) :
                    Fin (4 + k + 1) → TangentSpace I x₀) =
                fun p : Fin (4 + k + 1) =>
                  basis ((Function.update (Fin.cons a m : Fin (4 + k + 1) → Fin n)
                    q.succ e) p) := by
            funext p
            refine Fin.cases ?_ (fun j => ?_) p
            · simp only [Fin.cons_zero]
              rw [Function.update_of_ne (Fin.succ_ne_zero q).symm, Fin.cons_zero, hXa]
            · simp only [Fin.cons_succ]
              by_cases hj : j = q
              · subst hj; rw [Function.update_self, Function.update_self]
              · rw [Function.update_of_ne hj,
                  Function.update_of_ne (fun h => hj (Fin.succ_injective _ h)),
                  Fin.cons_succ, hVm j]
          rw [htuple]
        rw [hNk1]
        refine Real.sqrt_le_sqrt ?_
        rw [Finset.sum_congr rfl (fun e (_ : e ∈ (Finset.univ : Finset (Fin n))) => hcomb e)]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀) basis (Fin.cons a m) q.succ
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hf1 hf2 (Real.sqrt_nonneg _) hNRmnn) hcardnn
    exact add_le_add hT1a hT1b
  refine le_trans (Finset.sum_le_sum fun q _ => hper q) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_of_eq ?_
  push_cast
  ring





omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_nablaK_antisym_basis_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x₀ : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) (m : Fin (4 + k) → Fin n) :
    |nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
          (Fin.cons (basis a)
            (metricTraceInput (I := I) (basis b) (basis c) (fun i : Fin (4 + k) => basis (m i)))) -
        nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
          (Fin.cons (basis a)
            (metricTraceInput (I := I) (basis c) (basis b) (fun i : Fin (4 + k) => basis (m i))))| ≤
      ((4 + k : ℕ) : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
              nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
            Real.sqrt (compNormSqMulti (fun idx : Fin (4 + k) → Fin n =>
              nablaKRm04Field (I := I) S (t : Real) k x₀ (fun p => basis (idx p)))) +
          Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
              S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) *
            Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
              nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p))))) := by
  classical
  have hconn := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  obtain ⟨Xa, hXa, hXacov⟩ := TensorLieDeriv.exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis a)
  obtain ⟨Vb, hVb, hVbcov⟩ := TensorLieDeriv.exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis b)
  obtain ⟨Vc, hVc, hVccov⟩ := TensorLieDeriv.exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis c)
  choose Vm hVm hVmcov using fun i : Fin (4 + k) =>
    TensorLieDeriv.exists_cov_zero_at_apply (I := I)
      (S.family.connection (t : Real)) hconn x₀ (basis (m i))
  rw [show (basis a) = Xa x₀ from hXa.symm, show (basis b) = Vb x₀ from hVb.symm,
    show (basis c) = Vc x₀ from hVc.symm,
    show (fun i : Fin (4 + k) => basis (m i)) = (fun i : Fin (4 + k) => Vm i x₀) from
      funext fun i => (hVm i).symm]
  exact abs_nablaK_antisym_covConst_le (I := I) S hS t k x₀ basis horth Xa Vb Vc Vm
    a b c m hXa hVb hVc hVm (hVbcov Xa) (hVccov Xa) (fun i => hVmcov i Xa)






omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_spatialBracket_nablaKRm_ortho_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x₀ : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (i j c' : Fin n) (m' : Fin (4 + k) → Fin n) :
    |(nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
            (metricTraceInput (I := I) (basis i) (basis j)
              (Fin.cons (basis c') (fun p : Fin (4 + k) => basis (m' p)))) -
          nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀
            (metricTraceInput (I := I) (basis i) (basis c')
              (Fin.cons (basis j) (fun p : Fin (4 + k) => basis (m' p))))) +
        curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
          (nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀)
          (basis i) (basis c')
          (Fin.cons (basis j) (fun p : Fin (4 + k) => basis (m' p)))| ≤
      ((4 + k : ℕ) : Real) * (Fintype.card (Fin n) : Real) *
          (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
                nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
              Real.sqrt (compNormSqMulti (fun idx : Fin (4 + k) → Fin n =>
                nablaKRm04Field (I := I) S (t : Real) k x₀ (fun p => basis (idx p)))) +
            Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
                S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) *
              Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
                nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p))))) +
        ((4 + (k + 1) : ℕ) : Real) * (Fintype.card (Fin n) : Real) *
          (Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
                S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) *
            Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
              nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p))))) := by
  classical
  refine le_trans (abs_add_le _ _) ?_



  have hAB1 := congrArg (nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀)
    (show metricTraceInput (I := I) (basis i) (basis j)
          (Fin.cons (basis c') (fun p : Fin (4 + k) => basis (m' p)))
        = Fin.cons (basis i)
          (metricTraceInput (I := I) (basis j) (basis c') (fun p : Fin (4 + k) => basis (m' p)))
      from rfl)
  have hAB2 := congrArg (nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀)
    (show metricTraceInput (I := I) (basis i) (basis c')
          (Fin.cons (basis j) (fun p : Fin (4 + k) => basis (m' p)))
        = Fin.cons (basis i)
          (metricTraceInput (I := I) (basis c') (basis j) (fun p : Fin (4 + k) => basis (m' p)))
      from rfl)
  rw [hAB1, hAB2]
  refine add_le_add (abs_nablaK_antisym_basis_le (I := I) S hS t k x₀ basis horth i j c' m') ?_



  have hslot :
      (Fin.cons (basis j) (fun p : Fin (4 + k) => basis (m' p)) :
          Fin (4 + k + 1) → TangentSpace I x₀) =
        fun p : Fin (4 + k + 1) =>
          basis ((Fin.cons j m' : Fin (4 + k + 1) → Fin n) p) := by
    funext p; refine Fin.cases ?_ (fun q => ?_) p <;> rfl
  rw [hslot]
  have hC :=
    abs_curvatureAction0SAt_orthoBasis_le (I := I) (S.base.metric (t : Real))
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
      (solution_rm04LowersRm13At (I := I) S (t : Real) x₀) basis horth
      (nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀) i c'
      (Fin.cons j m')
  rw [← compNormSqMulti_eq_compNormSq4_basis (I := I) (S.base.rm04 (t : Real) x₀) basis] at hC
  exact hC






omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_spatialComm_nablaKRm_ortho_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x₀ : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (c' : Fin n) (m' : Fin (4 + k) → Fin n) :
    |metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
          (nablaKRm04Field (I := I) S (t : Real) (k + 3) x₀)
          (Fin.cons (basis c') (fun p : Fin (4 + k) => basis (m' p))) -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (4 + k) (S.family.connection (t : Real))
          (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
            (nablaKRm04Field (I := I) S (t : Real) (k + 2))) x₀
          (Fin.cons (basis c') (fun p : Fin (4 + k) => basis (m' p)))| ≤
      (Fintype.card (Fin n) : Real) *
        (((4 + k : ℕ) : Real) * (Fintype.card (Fin n) : Real) *
            (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
                  nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
                Real.sqrt (compNormSqMulti (fun idx : Fin (4 + k) → Fin n =>
                  nablaKRm04Field (I := I) S (t : Real) k x₀ (fun p => basis (idx p)))) +
              Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
                  S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) *
                Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
                  nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p))))) +
          ((4 + (k + 1) : ℕ) : Real) * (Fintype.card (Fin n) : Real) *
            (Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
                  S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) *
              Real.sqrt (compNormSqMulti (fun idx : Fin (4 + (k + 1)) → Fin n =>
                nablaKRm04Field (I := I) S (t : Real) (k + 1) x₀ (fun p => basis (idx p)))))) := by
  classical
  set gInv : Fin n → Fin n → Real := fun i j => if i = j then (1 : Real) else 0 with hgInv
  have hdiag : ∀ i : Fin n, gInv i i = 1 := by intro i; simp [hgInv]
  have hoff : ∀ i l : Fin n, i ≠ l → gInv i l = 0 := by intro i l hl; simp [hgInv, hl]
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric (t : Real)) x₀ basis
      gInv := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_single i]
      · rw [hdiag i, one_mul]; exact horth i j
      · intro l _ hl; rw [hoff i l (fun h => hl h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [Finset.sum_eq_single j]
      · rw [hdiag j, mul_one]; exact horth i j
      · intro l _ hl; rw [hoff l j hl, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
  rw [spatialComm_nablaKRm_split (I := I) S hS t k basis gInv hinv (basis c')
    (fun p : Fin (4 + k) => basis (m' p))]

  simp only [hgInv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ =>
    abs_spatialBracket_nablaKRm_ortho_le (I := I) S hS t k x₀ basis horth i i c' m') ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end AllKBound

end DifferentialGeometry.PDE.RicciFlow
