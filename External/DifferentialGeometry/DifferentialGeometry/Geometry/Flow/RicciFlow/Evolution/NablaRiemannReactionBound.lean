import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannT1Bound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannT2Bound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmFrozenSlotField
import DifferentialGeometry.Geometry.Operator.CotangentSharpSmooth
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false












noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem solution_isMetricCompatible
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.base.metric t) := by
  simpa [SolutionFamily.connection, metricCov] using
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (S.base.metric t)









open DifferentialGeometry.Integral.DivergenceTheorem
  DifferentialGeometry.Integral.Measure in
set_option backward.isDefEq.respectTransparency false in









omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rmFrozenSlot_chartBasis_contMDiffOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α : M) (j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real) ∞
      (fun b : M =>
        rmFrozenSlotField (I := I) S t q Y b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by



  have hval : ∀ b : M,
      rmFrozenSlotField (I := I) S t q Y b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) =
        (freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y) b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
    intro b; rfl
  simp only [hval]
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
    (T := fun b : M => (freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y) b)
    ((freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y).contMDiff x₀)
    (v := fun _ : Fin 1 => fun b : M => chartBasisVecFiber (I := I) α j b)
    (fun _ => hv_at)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using h_eval

open DifferentialGeometry.Integral.DivergenceTheorem in




omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rmFrozenSlotSharp_mdiffAt
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDiffAt
      (T% (fun y : M =>
        cotangentSharp_gen (I := I) (S.base.metric t) y
          (rmFrozenSlotField (I := I) S t q Y y))) x :=
  cotangentSharp_gen_mdiffAt (I := I) (S.base.metric t)
    (β := fun y : M => rmFrozenSlotField (I := I) S t q Y y)
    (fun α j => rmFrozenSlot_chartBasis_contMDiffOn (I := I) S t q Y α j) x

open DifferentialGeometry.Integral.DivergenceTheorem in




def rmFrozenSlotSharpSection
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk
    (fun y : M =>
      cotangentSharp_gen (I := I) (S.base.metric t) y
        (rmFrozenSlotField (I := I) S t q Y y))
    (cotangentSharp_gen_contMDiff_total (I := I) (S.base.metric t)
      (β := fun y : M => rmFrozenSlotField (I := I) S t q Y y)
      (fun α j => rmFrozenSlot_chartBasis_contMDiffOn (I := I) S t q Y α j))

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
@[simp] theorem rmFrozenSlotSharpSection_apply [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (y : M) :
    rmFrozenSlotSharpSection (I := I) S t q Y y =
      cotangentSharp_gen (I := I) (S.base.metric t) y
        (rmFrozenSlotField (I := I) S t q Y y) :=
  rfl














def rmRaiseSlotSections
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ![Vb, Vc, Vm q, rmFrozenSlotSharpSection (I := I) S t q Vm]













omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem rmRaise_summand_covDeriv
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) (q : Fin 4)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    extDerivFun (I := I)
        (fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                (rmFrozenSlotField (I := I) S (t : Real) q Vm y))))
        x₀ (X x₀) =
      nablaRm04Field (I := I) S (t : Real) x₀
          (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀))) +
        S.base.rm04 (t : Real) x₀
          (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)))) := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def

  set W : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    rmRaiseSlotSections (I := I) S (t : Real) q Vb Vc Vm with hW_def

  have hW0 : W 0 = Vb := rfl
  have hW1 : W 1 = Vc := rfl
  have hW2 : W 2 = Vm q := rfl
  have hW3 : W 3 = rmFrozenSlotSharpSection (I := I) S (t : Real) q Vm := rfl

  have heval :=
    (nablaRm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X W x₀

  have hscalar :
      (fun y : M => S.base.rm04 (t : Real) y (fun a : Fin 4 => W a y)) =
        fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                (rmFrozenSlotField (I := I) S (t : Real) q Vm y))) := by
    funext y
    congr 1
    funext a
    fin_cases a <;>
      simp [hW_def, rmRaiseSlotSections, vec4, rmFrozenSlotSharpSection_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

  have hcons :
      (Fin.cons (X x₀) (fun a : Fin 4 => W a x₀) : Fin 5 → TangentSpace I x₀) =
        vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
          (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
            (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)) := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · rfl
    · rw [Fin.cons_succ]
      fin_cases j <;>
        simp [hW_def, rmRaiseSlotSections, vec5, rmFrozenSlotSharpSection_apply,
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
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)))) := by
    rw [Fin.sum_univ_four]

    have hc0 : (cov (fun p : M => W 0 p) x₀) (X x₀) = 0 := by rw [hW0]; exact hVb
    have hc1 : (cov (fun p : M => W 1 p) x₀) (X x₀) = 0 := by rw [hW1]; exact hVc
    have hc2 : (cov (fun p : M => W 2 p) x₀) (X x₀) = 0 := by rw [hW2]; exact hVm q

    have hc3 :
        (cov (fun p : M => W 3 p) x₀) (X x₀) =
          cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
              (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)) := by
      have hsharp :=
        cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
          cov (S.base.metric (t : Real))
          (solution_isMetricCompatible (I := I) S (t : Real))
          (rmFrozenSlotField (I := I) S (t : Real) q Vm)
          (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm)
          (nablaRmFrozenSlotField_realizes (I := I) S (t : Real) q Vm)
          X x₀
          (rmFrozenSlotSharp_mdiffAt (I := I) S (t : Real) q Vm x₀)
      rw [hW3]

      simpa [rmFrozenSlotSharpSection_apply] using hsharp

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
      simp [hW_def, rmRaiseSlotSections, vec4, Function.update,
        rmFrozenSlotSharpSection_apply]

  rw [← hscalar]


  rw [hcons] at heval
  rw [hcorr] at heval
  linarith [heval]












def nabla2SlotSections
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin 6 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  Fin.cons Vb (Fin.cons Vc Vm)



omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nabla2SlotSections_apply
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (y : M) :
    (fun a : Fin 6 => nabla2SlotSections (I := I) Vb Vc Vm a y) =
      metricTraceInput (I := I) (Vb y) (Vc y)
        (fun i : Fin 4 => Vm i y) := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · rfl












omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla3_antisym_eq_covDeriv_curvatureAction_covConst
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀))) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀))) =
      extDerivFun (I := I)
        (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y))
        x₀ (X x₀) := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def

  set Wbc := nabla2SlotSections (I := I) Vb Vc Vm with hWbc_def
  set Wcb := nabla2SlotSections (I := I) Vc Vb Vm with hWcb_def

  have hWbc_cov : ∀ a : Fin 6, (cov (fun p : M => Wbc a p) x₀) (X x₀) = 0 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [hWbc_def, nabla2SlotSections] using hVb
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [hWbc_def, nabla2SlotSections] using hVc
      · simpa [hWbc_def, nabla2SlotSections] using hVm k
  have hWcb_cov : ∀ a : Fin 6, (cov (fun p : M => Wcb a p) x₀) (X x₀) = 0 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [hWcb_def, nabla2SlotSections] using hVc
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [hWcb_def, nabla2SlotSections] using hVb
      · simpa [hWcb_def, nabla2SlotSections] using hVm k

  have hbc :=
    (nabla3Rm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X Wbc x₀
  have hcb :=
    (nabla3Rm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X Wcb x₀

  have hbc_corr :
      (∑ a : Fin 6,
          nabla2Rm04Field (I := I) S (t : Real) x₀
            (Function.update (fun b : Fin 6 => Wbc b x₀) a
              ((cov (fun p : M => Wbc a p) x₀) (X x₀)))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hWbc_cov a]
    exact (nabla2Rm04Field (I := I) S (t : Real) x₀).map_update_zero _ a
  have hcb_corr :
      (∑ a : Fin 6,
          nabla2Rm04Field (I := I) S (t : Real) x₀
            (Function.update (fun b : Fin 6 => Wcb b x₀) a
              ((cov (fun p : M => Wcb a p) x₀) (X x₀)))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hWcb_cov a]
    exact (nabla2Rm04Field (I := I) S (t : Real) x₀).map_update_zero _ a

  have hWbc_x : (fun a : Fin 6 => Wbc a x₀) =
      metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀) :=
    nabla2SlotSections_apply (I := I) Vb Vc Vm x₀
  have hWcb_x : (fun a : Fin 6 => Wcb a x₀) =
      metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀) :=
    nabla2SlotSections_apply (I := I) Vc Vb Vm x₀
  rw [hbc_corr, sub_zero] at hbc
  rw [hcb_corr, sub_zero] at hcb
  rw [hWbc_x] at hbc
  rw [hWcb_x] at hcb

  rw [hbc, hcb]

  have hmdiff_bc :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          nabla2Rm04Field (I := I) S (t : Real) p (fun a : Fin 6 => Wbc a p)) x₀ :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (nabla2Rm04Field (I := I) S (t : Real)) Wbc x₀).mdifferentiableAt (by simp)
  have hmdiff_cb :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          nabla2Rm04Field (I := I) S (t : Real) p (fun a : Fin 6 => Wcb a p)) x₀ :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (nabla2Rm04Field (I := I) S (t : Real)) Wcb x₀).mdifferentiableAt (by simp)
  rw [← extDerivFun_sub_at (I := I) (X x₀) hmdiff_bc hmdiff_cb]

  have hfield :
      (fun y : M =>
          nabla2Rm04Field (I := I) S (t : Real) y (fun a : Fin 6 => Wbc a y) -
            nabla2Rm04Field (I := I) S (t : Real) y (fun a : Fin 6 => Wcb a y)) =
        fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y) := by
    funext y
    rw [nabla2SlotSections_apply (I := I) Vb Vc Vm y,
      nabla2SlotSections_apply (I := I) Vc Vb Vm y]
    exact rm04_ricciIdentityAt (I := I) S hS t y
      (Vb y) (Vc y) (fun i : Fin 4 => Vm i y)
  rw [hfield]

























omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem nablaLapComm_T1_eq_rm04_raise_leibniz
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀))) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀))) =
      -∑ q : Fin 4,
        (nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀))) +
          S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))) := by
  classical

  rw [nabla3_antisym_eq_covDeriv_curvatureAction_covConst (I := I) S hS t x₀
    X Vb Vc Vm hVb hVc hVm]


  have hKfield :
      (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y)) =
        fun y : M =>
          -∑ q : Fin 4,
            S.base.rm04 (t : Real) y
              (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
                (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                  (rmFrozenSlotField (I := I) S (t : Real) q Vm y))) := by
    funext y
    rw [curvatureAction0SAt_eq_rm04_raise (I := I) (S.base.metric (t : Real))
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) y)
      (solution_rm04LowersRm13At (I := I) S (t : Real) y)
      (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y)]


    rfl
  rw [hKfield]

  set g : Fin 4 → M → Real := fun q y =>
    S.base.rm04 (t : Real) y
      (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
        (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
          (rmFrozenSlotField (I := I) S (t : Real) q Vm y))) with hg_def

  have hmdiff_q : ∀ q : Fin 4,
      MDifferentiableAt I 𝓘(Real, Real) (g q) x₀ := by
    intro q
    have h := (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (S.base.rm04 (t : Real))
      (rmRaiseSlotSections (I := I) S (t : Real) q Vb Vc Vm) x₀).mdifferentiableAt (by simp)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [hg_def]
    dsimp only
    congr 1
    funext a
    fin_cases a <;>
      simp [rmRaiseSlotSections, vec4, rmFrozenSlotSharpSection_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

  have hstep3 :
      extDerivFun (I := I) (fun y : M => -∑ q : Fin 4, g q y) x₀ (X x₀) =
        -∑ q : Fin 4, extDerivFun (I := I) (g q) x₀ (X x₀) := by
    have hsumfun : (fun y : M => ∑ q : Fin 4, g q y) =
        (Finset.univ : Finset (Fin 4)).sum g := by
      funext y; simp [Finset.sum_apply]
    have hneg :
        extDerivFun (I := I) (fun y : M => -∑ q : Fin 4, g q y) x₀ (X x₀) =
          -extDerivFun (I := I) (fun y : M => ∑ q : Fin 4, g q y) x₀ (X x₀) :=
      extDerivFun_neg_at (I := I) (f := fun y : M => ∑ q : Fin 4, g q y) (X x₀)
        (by
          rw [hsumfun]
          exact MDifferentiableAt.sum (𝕜 := Real) (I := I)
            (t := (Finset.univ : Finset (Fin 4))) (fun q _ => hmdiff_q q))
    rw [hneg, hsumfun]
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real (I := I)
      (t := (Finset.univ : Finset (Fin 4))) g (X x₀) (fun q _ => hmdiff_q q)]
  rw [hstep3]

  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hg_def]
  exact rmRaise_summand_covDeriv (I := I) S hS t x₀ q X Vb Vc Vm hVb hVc (fun i => hVm i)









section T1Bound

variable {n : ℕ}




omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem cotangentSharp_orthoBasis_expand'
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    cotangentSharp_gen (I := I) g x β =
      ∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) • basis e := by
  classical
  set gInv : Fin n → Fin n → Real := fun i j => if i = j then 1 else 0 with hgInv
  have hdiag : ∀ i : Fin n, gInv i i = 1 := by intro i; simp [hgInv]
  have hoff : ∀ i k : Fin n, i ≠ k → gInv i k = 0 := by
    intro i k hk; simp [hgInv, hk]
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_single i]
      · rw [hdiag i, one_mul]; exact horth i j
      · intro k _ hk; rw [hoff i k (fun h => hk h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [Finset.sum_eq_single j]
      · rw [hdiag j, mul_one]; exact horth i j
      · intro k _ hk; rw [hoff k j hk, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv β]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [hdiag i, one_mul, cotangentToDual_apply_gen]
  · intro j _ hj; rw [hoff i j (fun h => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h


omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor05_vec5_sum_last
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (A B C D : TangentSpace I x)
    (coef : Fin n → Real) (vecs : Fin n → TangentSpace I x) :
    T (vec5 (I := I) A B C D (∑ e : Fin n, coef e • vecs e)) =
      ∑ e : Fin n, coef e * T (vec5 (I := I) A B C D (vecs e)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec5 (I := I) A B C D Z =
        Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4 Z := by
    intro Z; funext i; fin_cases i <;> simp [vec5, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (∑ e : Fin n, coef e • vecs e)) =
      T.toMultilinearMap (Function.update
        (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (∑ e : Fin n, coef e • vecs e)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show T.toMultilinearMap (Function.update
        (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4 (coef e • vecs e)) =
      T (Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (coef e • vecs e)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]


omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor04_vec4_sum_last'
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (A B C : TangentSpace I x)
    (coef : Fin n → Real) (vecs : Fin n → TangentSpace I x) :
    T (vec4 (I := I) A B C (∑ e : Fin n, coef e • vecs e)) =
      ∑ e : Fin n, coef e * T (vec4 (I := I) A B C (vecs e)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec4 (I := I) A B C Z =
        Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 Z := by
    intro Z; funext i; fin_cases i <;> simp [vec4, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Fin n, coef e • vecs e)) =
      T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Fin n, coef e • vecs e)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 (coef e • vecs e)) =
      T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (coef e • vecs e)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]








omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem abs_tensor05_sharp_last_le
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (A B C D : TangentSpace I x)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    |T (vec5 (I := I) A B C D (cotangentSharp_gen (I := I) g x β))| ≤
      (Fintype.card (Fin n) : Real) *
        (Real.sqrt (∑ e : Fin n, (T (vec5 (I := I) A B C D (basis e))) ^ 2) *
          Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2)) := by
  classical
  set NT : Real := Real.sqrt (∑ e : Fin n, (T (vec5 (I := I) A B C D (basis e))) ^ 2)
    with hNT
  set Nβ : Real := Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2) with hNβ
  have hNTnn : 0 ≤ NT := Real.sqrt_nonneg _
  have hNβnn : 0 ≤ Nβ := Real.sqrt_nonneg _
  rw [cotangentSharp_orthoBasis_expand' (I := I) g basis horth β]
  rw [tensor05_vec5_sum_last (I := I) T A B C D]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin n => NT * Nβ) ?_) ?_
  · intro e _
    rw [abs_mul, mul_comm]
    have hTbnd : |T (vec5 (I := I) A B C D (basis e))| ≤ NT := by
      rw [hNT, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (T (vec5 (I := I) A B C D (basis e'))) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    have hβbnd : |β (fun _ : Fin 1 => basis e)| ≤ Nβ := by
      rw [hNβ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (β (fun _ : Fin 1 => basis e')) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    exact mul_le_mul hTbnd hβbnd (abs_nonneg _) hNTnn
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem abs_tensor04_sharp_last_le
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (A B C : TangentSpace I x)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    |T (vec4 (I := I) A B C (cotangentSharp_gen (I := I) g x β))| ≤
      (Fintype.card (Fin n) : Real) *
        (Real.sqrt (∑ e : Fin n, (T (vec4 (I := I) A B C (basis e))) ^ 2) *
          Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2)) := by
  classical
  set NT : Real := Real.sqrt (∑ e : Fin n, (T (vec4 (I := I) A B C (basis e))) ^ 2)
    with hNT
  set Nβ : Real := Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2) with hNβ
  have hNTnn : 0 ≤ NT := Real.sqrt_nonneg _
  have hNβnn : 0 ≤ Nβ := Real.sqrt_nonneg _
  rw [cotangentSharp_orthoBasis_expand' (I := I) g basis horth β]
  rw [tensor04_vec4_sum_last' (I := I) T A B C]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin n => NT * Nβ) ?_) ?_
  · intro e _
    rw [abs_mul, mul_comm]
    have hTbnd : |T (vec4 (I := I) A B C (basis e))| ≤ NT := by
      rw [hNT, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (T (vec4 (I := I) A B C (basis e'))) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    have hβbnd : |β (fun _ : Fin 1 => basis e)| ≤ Nβ := by
      rw [hNβ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (β (fun _ : Fin 1 => basis e')) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    exact mul_le_mul hTbnd hβbnd (abs_nonneg _) hNTnn
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]





omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem sum_sq_update_le_compNormSqMulti {r : ℕ}
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (idx : Fin r → Fin n) (q : Fin r) :
    (∑ e : Fin n,
        (T (fun p : Fin r => basis (Function.update idx q e p))) ^ 2) ≤
      compNormSqMulti (fun jdx : Fin r → Fin n => T (fun p => basis (jdx p))) := by
  classical
  set F : Fin n → (Fin r → Fin n) := fun e => Function.update idx q e with hF
  set P : (Fin r → Fin n) → Real :=
    fun jdx => (T (fun p => basis (jdx p))) ^ 2 with hP
  have hinj : Set.InjOn F (Finset.univ : Finset (Fin n)) := by
    intro e₁ _ e₂ _ heq
    have := congrFun heq q
    simpa [hF, Function.update_self] using this
  have himg : (∑ e : Fin n, P (F e)) = ∑ jdx ∈ Finset.univ.image F, P jdx :=
    (Finset.sum_image (fun e _ e' _ h => hinj (Finset.mem_univ e) (Finset.mem_univ e') h)).symm
  have hlhs : (∑ e : Fin n,
        (T (fun p : Fin r => basis (Function.update idx q e p))) ^ 2) =
      ∑ e : Fin n, P (F e) := rfl
  rw [hlhs, himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => sq_nonneg _)

end T1Bound







section SolutionT1Bound

variable {n : ℕ}



omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rmFrozenSlot_basis_component
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (e : TangentSpace I x₀) :
    rmFrozenSlotField (I := I) S t q Vm x₀ (fun _ : Fin 1 => e) =
      S.base.rm04 t x₀ (Function.update (fun i : Fin 4 => Vm i x₀) q e) :=
  rmFrozenSlotField_apply_vec (I := I) S t q Vm x₀ e

open TensorLieDeriv in










omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_nablaLapComm_T1_covConst_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (a b c : Fin n) (m : Fin 4 → Fin n)
    (hXa : X x₀ = basis a) (hVb : Vb x₀ = basis b) (hVc : Vc x₀ = basis c)
    (hVm : ∀ i : Fin 4, Vm i x₀ = basis (m i))
    (hXcov : ((S.family.connection (t : Real) (fun p : M => X p) x₀) (X x₀)) = 0)
    (hVbcov : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVccov : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVmcov : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    |nabla3Rm04Field (I := I) S (t : Real) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀))) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀)))| ≤
      (8 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
            S.base.rm04 (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  set g := S.base.metric (t : Real) with hg_def
  set Nnab : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) with hNnab
  set NRm : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
      S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) with hNRm
  have hNnabnn : 0 ≤ Nnab := Real.sqrt_nonneg _
  have hNRmnn : 0 ≤ NRm := Real.sqrt_nonneg _
  have hcardnn : (0 : Real) ≤ (Fintype.card (Fin n) : Real) := by positivity

  rw [nablaLapComm_T1_eq_rm04_raise_leibniz (I := I) S hS t x₀ X Vb Vc Vm
    hVbcov hVccov hVmcov]
  rw [abs_neg]

  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_

  have hper : ∀ q : Fin 4,
      |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀))) +
          S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))| ≤
        (2 : Real) * (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by
    intro q
    refine le_trans (abs_add_le _ _) ?_

    have hT1a :
        |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)))| ≤
          (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by
      have hCS := abs_tensor05_sharp_last_le (I := I) g basis horth
        (nablaRm04Field (I := I) S (t : Real) x₀)
        (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
        (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)
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
              (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀
                (fun _ : Fin 1 => basis e)) ^ 2) ≤ NRm := by
        rw [hNRm]
        refine Real.sqrt_le_sqrt ?_
        have hβ : ∀ e : Fin n,
            (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀
                (fun _ : Fin 1 => basis e)) ^ 2 =
              (S.base.rm04 (t : Real) x₀
                (fun p : Fin 4 => basis ((Function.update m q e) p))) ^ 2 := by
          intro e
          rw [rmFrozenSlot_basis_component (I := I) S (t : Real) q Vm x₀ (basis e)]
          congr 2
          funext p
          by_cases hp : p = q
          · subst hp; simp [Function.update]
          · simp [Function.update, hp, hVm p]
        rw [Finset.sum_congr rfl (fun e _ => hβ e)]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (S.base.rm04 (t : Real) x₀) basis m q
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hf1 hf2 (Real.sqrt_nonneg _) hNnabnn) hcardnn

    have hT1b :
        |S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))| ≤
          (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by
      have hCS := abs_tensor04_sharp_last_le (I := I) g basis horth
        (S.base.rm04 (t : Real) x₀)
        (Vb x₀) (Vc x₀) (Vm q x₀)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
          (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))
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
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)
                (fun _ : Fin 1 => basis e)) ^ 2) ≤ Nnab := by

        have hcomb : ∀ e : Fin n,
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)
                (fun _ : Fin 1 => basis e)) ^ 2 =
              (nablaRm04Field (I := I) S (t : Real) x₀
                (fun p : Fin 5 =>
                  basis ((Function.update (Fin.cons a m : Fin 5 → Fin n) q.succ e) p))) ^ 2 := by
          intro e
          rw [tensor0S_curry_apply_cons]
          have hcons2 :
              (Fin.cons (X x₀) (fun _ : Fin 1 => basis e) : Fin 2 → TangentSpace I x₀) =
                vec2 (I := I) (X x₀) (basis e) := by
            funext p; fin_cases p <;> rfl
          rw [hcons2, nablaRmFrozenSlot_eval (I := I) S hS t q X Vm x₀
            (fun i _ => hVmcov i) (basis e)]
          have htuple :
              (Fin.cons (X x₀)
                  (Function.update (fun i : Fin 4 => Vm i x₀) q (basis e)) :
                    Fin 5 → TangentSpace I x₀) =
                fun p : Fin 5 =>
                  basis ((Function.update (Fin.cons a m : Fin 5 → Fin n) q.succ e) p) := by
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
        rw [hNnab]
        refine Real.sqrt_le_sqrt ?_
        rw [Finset.sum_congr rfl (fun e (_ : e ∈ (Finset.univ : Finset (Fin n))) => hcomb e)]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (nablaRm04Field (I := I) S (t : Real) x₀) basis (Fin.cons a m) q.succ

      refine le_trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hf1 hf2 (Real.sqrt_nonneg _) hNRmnn) hcardnn) ?_
      rw [mul_comm NRm Nnab]
    calc
      |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)))| +
          |S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))|
          ≤ (Fintype.card (Fin n) : Real) * (Nnab * NRm) +
              (Fintype.card (Fin n) : Real) * (Nnab * NRm) := add_le_add hT1a hT1b
      _ = (2 : Real) * (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by ring
  refine le_trans (Finset.sum_le_sum fun q _ => hper q) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

open TensorLieDeriv in








omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_nablaLapComm_T1_orthoBasis_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) (m : Fin 4 → Fin n) :
    |nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTupleF (I := I) frame x₀ a b c m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTupleF (I := I) frame x₀ a c b m)| ≤
      (8 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
            S.base.rm04 (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  have hconn := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)

  obtain ⟨Xa, hXa, hXacov⟩ := exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis a)
  obtain ⟨Vb, hVb, hVbcov⟩ := exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis b)
  obtain ⟨Vc, hVc, hVccov⟩ := exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis c)

  choose Vm hVm hVmcov using fun i : Fin 4 =>
    exists_cov_zero_at_apply (I := I)
      (S.family.connection (t : Real)) hconn x₀ (basis (m i))


  have hmtail : frameTuple (I := I) frame x₀ m = (fun i : Fin 4 => Vm i x₀) := by
    funext i
    show frame (m i) x₀ = Vm i x₀
    rw [hframe (m i), hVm i]
  have htuple_a :
      nabla3FrameTupleF (I := I) frame x₀ a b c m =
        Fin.cons (Xa x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀)) := by
    simp only [nabla3FrameTupleF, nabla3InnerSlotsF, metricTraceInput]
    rw [hframe a, hframe b, hframe c, hXa, hVb, hVc, hmtail]
    rfl
  have htuple_acb :
      nabla3FrameTupleF (I := I) frame x₀ a c b m =
        Fin.cons (Xa x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀)) := by
    simp only [nabla3FrameTupleF, nabla3InnerSlotsF, metricTraceInput]
    rw [hframe a, hframe c, hframe b, hXa, hVc, hVb, hmtail]
    rfl
  rw [htuple_a, htuple_acb]
  exact abs_nablaLapComm_T1_covConst_le (I := I) S hS t x₀ basis horth Xa Vb Vc Vm
    a b c m hXa hVb hVc hVm
    (hXacov Xa) (hVbcov Xa) (hVccov Xa) (fun i => hVmcov i Xa)

end SolutionT1Bound








section ReactionBound

variable {n : ℕ}



private theorem sum_pi_fin_succ {Idx : Type*} [Fintype Idx] {k : ℕ}
    (f : (Fin (k + 1) → Idx) → Real) :
    (∑ idx : Fin (k + 1) → Idx, f idx) =
      ∑ a : Idx, ∑ rest : Fin k → Idx, f (Fin.cons a rest) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Idx)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl



omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem compNormSqMulti_eq_compNormSq4_basis
    {x₀ : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x₀)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀)) :
    compNormSqMulti (fun idx : Fin 4 → Fin n => T (fun p => basis (idx p))) =
      compNormSq4 (fun i j k l : Fin n =>
        T (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) := by
  classical
  set A : (Fin 4 → Fin n) → Real := fun idx => T (fun p => basis (idx p)) with hA
  unfold compNormSqMulti compNormSq4
  rw [sum_pi_fin_succ (fun idx => (A idx) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons i idx)) ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons i (Fin.cons j idx))) ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons i (Fin.cons j (Fin.cons k idx)))) ^ 2)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (default : Fin 0 → Fin n)]
  · have htuple :
        (Fin.cons i (Fin.cons j (Fin.cons k
          (Fin.cons l (default : Fin 0 → Fin n)))) : Fin 4 → Fin n) =
          ![i, j, k, l] := by
      funext p; fin_cases p <;> rfl
    show (A (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (default : Fin 0 → Fin n)))))) ^ 2 = _
    rw [htuple, hA]
    dsimp only
    have hvec : (fun p : Fin 4 => basis ((![i, j, k, l] : Fin 4 → Fin n) p)) =
        vec4 (I := I) (basis i) (basis j) (basis k) (basis l) := by
      funext p; fin_cases p <;> rfl
    rw [hvec]
  · intro y _ hy; exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h











omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_nablaLapCommReactionTermF_orthoBasis_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) (m : Fin 4 → Fin n) :
    |nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a b c m| ≤
      (13 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
            S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  have horth' : ∀ i j : Fin n,
      (S.family.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := horth
  rw [nablaLapCommReactionTermF]
  refine le_trans (abs_add_le _ _) ?_
  have hT1 := abs_nablaLapComm_T1_orthoBasis_le (I := I) S hS t x₀ frame basis hframe
    horth a b c m
  rw [compNormSqMulti_eq_compNormSq4_basis (I := I) (S.base.rm04 (t : Real) x₀) basis] at hT1
  have hT2 := abs_nablaLapComm_T2_orthoBasis_le (I := I) S (t : Real) x₀ frame basis
    hframe horth' a b c m
  have hsum := add_le_add hT1 hT2
  refine le_trans hsum (le_of_eq ?_)
  ring












omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_nablaLapCommReactionTerm_diag_orthoBasis_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (c : Fin n) (m : Fin 4 → Fin n) :
    |∑ a : Fin n, nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m| ≤
      (13 : Real) * (Fintype.card (Fin n) : Real) ^ 2 *
        (Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
            S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  set NRm : Real := Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
      S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))))
    with hNRm
  set Nnab : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) with hNnab

  have hper : ∀ a : Fin n,
      |nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m| ≤
        (13 : Real) * (Fintype.card (Fin n) : Real) * (NRm * Nnab) := by
    intro a
    have h := abs_nablaLapCommReactionTermF_orthoBasis_le (I := I) S hS t x₀
      frame basis hframe horth a a c m
    rw [← hNRm, ← hNnab] at h
    exact h
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun a _ => hper a) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  ring
























omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_spatialCommNablaRm_orthoFrame_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric (t : Real)).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) ∧
      InverseMetricOrthonormalAt (M := M) (Idx := Fin n)
        (deltaInvMetric (M := M)) (t : Real) x₀ ∧
      ∀ (c : Fin n) (m : Fin 4 → Fin n),
        |roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m| ≤
          (13 : Real) * (Fintype.card (Fin n) : Real) ^ 2 *
            (Real.sqrt (rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
                (deltaInvMetric (M := M)) frame (t : Real) x₀) *
              Real.sqrt (nablaRm04NormSqInFrame (M := M)
                (fun s y i j k l p =>
                  nablaRm04Field (I := I) S s y (vec5 (I := I)
                    (frame i y) (frame j y) (frame k y) (frame l y) (frame p y)))
                (deltaInvMetric (M := M)) (t : Real) x₀)) := by
  classical
  obtain ⟨n, frame, basis, hframe, horth⟩ := exists_orthoBasisFrameAt (I := I) S (t : Real) x₀
  refine ⟨n, frame, ?_, deltaInvMetric_orthonormal (M := M) (t : Real) x₀, ?_⟩
  · intro i j; rw [hframe i, hframe j]; exact horth i j
  intro c m

  rw [nablaLapCommF_orthonormalTrace (I := I) S hS t x₀ frame
    (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) (fun i j => rfl) c m]

  have hbnd := abs_nablaLapCommReactionTerm_diag_orthoBasis_le (I := I) S hS t x₀
    frame basis hframe horth c m

  have hRm :
      compNormSq4 (fun i j k l : Fin n =>
          S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) =
        rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
          (deltaInvMetric (M := M)) frame (t : Real) x₀ := by
    rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
      (deltaInvMetric (M := M)) frame (t : Real) x₀
      (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
    rw [hframe i, hframe j, hframe k, hframe l]
  have hNab :
      compNormSqMulti (fun idx : Fin 5 → Fin n =>
          nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))) =
        nablaRm04NormSqInFrame (M := M)
          (fun s y i j k l p =>
            nablaRm04Field (I := I) S s y (vec5 (I := I)
              (frame i y) (frame j y) (frame k y) (frame l y) (frame p y)))
          (deltaInvMetric (M := M)) (t : Real) x₀ := by
    rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) _
      (deltaInvMetric (M := M)) (t : Real) x₀
      (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
    rw [compNormSqMulti_eq_compNormSq5
      (fun idx : Fin 5 → Fin n =>
        nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))]
    refine Finset.sum_congr rfl fun mi _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c' _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    dsimp only
    have htup : (fun p : Fin 5 => basis ((![mi, a, b, c', d] : Fin 5 → Fin n) p)) =
        vec5 (I := I) (frame mi x₀) (frame a x₀) (frame b x₀) (frame c' x₀) (frame d x₀) := by
      funext p; fin_cases p <;> simp [vec5, hframe]
    rw [htup]
  rw [hRm, hNab] at hbnd
  exact hbnd

end ReactionBound

end DifferentialGeometry.PDE.RicciFlow
