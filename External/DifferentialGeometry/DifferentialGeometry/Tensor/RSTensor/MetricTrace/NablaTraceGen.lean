import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false





















namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle Filter
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]





private def freezeTailSlots {s : ℕ}
    (x₀ : M) (σ : Fin 2 → CoordinateIdx (𝕜 := Real) E)
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin (s + 2) → (y : M) → TangentSpace I y :=
  fun q y => metricTraceInput (I := I)
    (coordinateFrameAt (I := I) x₀ (σ 0) y)
    (coordinateFrameAt (I := I) x₀ (σ 1) y)
    (fun b : Fin s => Y b y) q

set_option backward.isDefEq.respectTransparency false in



noncomputable def freezeTailField {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => freezeFirstTwo0S (I := I) (A p) (fun b : Fin s => Y b p)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (fun q : Fin (s + 2) => freezeTailSlots (I := I) x₀ σ Y q y))
        x₀ := by
    let v : Fin (s + 2) → (y : M) → TangentSpace I y :=
      fun q y => freezeTailSlots (I := I) x₀ σ Y q y
    have hv : ∀ q : Fin (s + 2),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v q y)) x₀ := by
      intro q
      refine Fin.cases ?_ (fun i => ?_) q
      ·
        have hframe :
            ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
              (fun y : M =>
                TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y
                  (coordinateFrameAt (I := I) x₀ (σ 0) y)) x₀ :=
          (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
            (coordinateFrameSet_open (I := I) x₀)
            (coordinateFrameAt_mem (I := I) x₀) (σ 0)
        refine hframe.congr_of_eventuallyEq ?_
        filter_upwards with y
        simp [v, freezeTailSlots, metricTraceInput]
      · refine Fin.cases ?_ (fun c => ?_) i
        ·
          have hframe :
              ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
                (fun y : M =>
                  TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y
                    (coordinateFrameAt (I := I) x₀ (σ 1) y)) x₀ :=
            (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
              (coordinateFrameSet_open (I := I) x₀)
              (coordinateFrameAt_mem (I := I) x₀) (σ 1)
          refine hframe.congr_of_eventuallyEq ?_
          filter_upwards with y
          simp only [v, freezeTailSlots, metricTraceInput, Fin.cases_succ,
            Fin.cases_zero]
        ·
          have hYc := (Y c).contMDiff x₀
          refine hYc.congr_of_eventuallyEq ?_
          filter_upwards with y
          simp [v, freezeTailSlots, metricTraceInput]
    have hA := TensorMultilinear.contMDiffAt_section_apply_gen
      (𝕜 := Real) (I := I) (M := M) (n := s + 2)
      (T := fun y : M => A y) (A.contMDiff x₀) v hv
    simpa [v, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hA
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 2 Real E)
      (Bundle.continuousMultilinearMap Real 2 E
        (TangentSpace I : M → Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin (s + 2) => freezeTailSlots (I := I) x₀ σ Y q y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin (s + 2) => freezeTailSlots (I := I) x₀ σ Y q y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 2 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y
          (b (σ a))) =
        vec2 (I := I)
          (coordinateFrameAt (I := I) x₀ (σ 0) y)
          (coordinateFrameAt (I := I) x₀ (σ 1) y) := by
    funext q
    fin_cases q
    · change
        (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
            (b (σ 0)) =
          coordinateFrameAt (I := I) x₀ (σ 0) y
      change e.symmL Real y (b (σ 0)) = e.localFrame b (σ 0) y
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := σ 0) hy]
      rfl
    · change
        (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
            (b (σ 1)) =
          coordinateFrameAt (I := I) x₀ (σ 1) y
      change e.symmL Real y (b (σ 1)) = e.localFrame b (σ 1) y
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := σ 1) hy]
      rfl
  rw [hslot]
  rw [freezeFirstTwo0S_apply]
  rfl

@[simp] theorem freezeTailField_apply {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    freezeTailField (I := I) (M := M) A Y x =
      freezeFirstTwo0S (I := I) (A x) (fun b : Fin s => Y b x) := by
  rfl






private theorem tailFreezeNablaGen {s : ℕ}
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M}
    (hYzero : ∀ b : Fin s, ((cov (fun p : M => Y b p) x) (X x)) = 0)
    (U V : TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (freezeTailField (I := I) (M := M) A Y) x (vec3 (I := I) (X x) U V) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) cov A x
        (Fin.cons (X x) (metricTraceInput (I := I) U V (fun b : Fin s => Y b x))) := by
  classical
  set B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := freezeTailField (I := I) (M := M) A Y with hBdef
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  obtain ⟨Vsec, hVsec, hVcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x V
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
  let Vfull : Fin (s + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    Fin.cons Usec (Fin.cons Vsec Y)
  have hVfullp : ∀ p : M,
      (fun q : Fin (s + 2) => Vfull q p) =
        metricTraceInput (I := I) (Usec p) (Vsec p) (fun b : Fin s => Y b p) := by
    intro p
    funext q
    refine Fin.cases ?_ (fun i => ?_) q
    · rfl
    · refine Fin.cases ?_ (fun c => ?_) i <;> rfl
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X B x (vec2 (I := I) U V)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 2) cov X A x
      (metricTraceInput (I := I) U V (fun b : Fin s => Y b x))
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V2 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X Vfull A x
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin (s + 2) => Vfull a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => V2 a p)) =
          fun p : M => A p (fun a : Fin (s + 2) => Vfull a p) := by
      funext p
      have hV2p :
          (fun a : Fin 2 => V2 a p) = vec2 (I := I) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      rw [hV2p, hVfullp p, hBdef, freezeTailField_apply, freezeFirstTwo0S_apply]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 2,
        B x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [V2, hUcov X, hVcov X, metricTrace_tensor0S_update_zero]
  have hAcorr :
      (∑ a : Fin (s + 2),
        A x
          (Function.update (fun b : Fin (s + 2) => Vfull b x) a
            ((cov (fun p : M => Vfull a p) x) (X x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hz : (cov (fun p : M => Vfull a p) x) (X x) = 0 := by
      refine Fin.cases ?_ (fun i => ?_) a
      · simpa only [Vfull, Fin.cons_zero] using hUcov X
      · refine Fin.cases ?_ (fun c => ?_) i
        · simpa only [Vfull, Fin.cons_succ, Fin.cons_zero] using hVcov X
        · simpa only [Vfull, Fin.cons_succ] using hYzero c
    rw [hz]
    simp [metricTrace_tensor0S_update_zero]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X B x (vec2 (I := I) U V) := by
        simpa [metricTrace_finCons_vec2_eq_vec3 (I := I), hUsec, hVsec] using hBtot
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) cov X A x
        (metricTraceInput (I := I) U V (fun b : Fin s => Y b x)) := by
        have hV2x :
            (fun a : Fin 2 => V2 a x) = vec2 (I := I) U V := by
          funext a
          fin_cases a <;> simp [V2, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec2]
        have hVfullx :
            (fun a : Fin (s + 2) => Vfull a x) =
              metricTraceInput (I := I) U V (fun b : Fin s => Y b x) := by
          rw [hVfullp x, hUsec, hVsec]
        rw [← hV2x, ← hVfullx]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) cov A x
        (Fin.cons (X x)
          (metricTraceInput (I := I) U V (fun b : Fin s => Y b x))) :=
        hAtot.symm





private def traceFirstTwoIdx {s : ℕ}
    (i j : CoordinateIdx (𝕜 := Real) E)
    (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    Fin (s + 2) -> CoordinateIdx (𝕜 := Real) E :=
  Fin.cons i (Fin.cons j σ)

private theorem metricTraceInput_coordFrame {s : ℕ} (x₀ y : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    metricTraceInput (I := I) (coordinateFrameAt (I := I) x₀ i y)
        (coordinateFrameAt (I := I) x₀ j y)
        (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y) =
      fun q : Fin (s + 2) =>
        coordinateFrameAt (I := I) x₀ (traceFirstTwoIdx i j σ q) y := by
  funext q
  refine Fin.cases ?_ (fun c => ?_) q
  · rfl
  · refine Fin.cases ?_ (fun d => ?_) c <;> rfl

private theorem metricTraceFirstTwoEvent {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x₀ : M) (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g (A y)
          (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y (fun q : Fin (s + 2) =>
                coordinateFrameAt (I := I) x₀ (traceFirstTwoIdx i j σ q) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  rw [metricTraceFirstTwo0STensor_apply (I := I) g (A y)
    (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv
    (gInvBasisAt (I := I) g x₀ hy) (A y)
    (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa [basis, coordinateFrameAt_basis_apply] using
    congrArg (fun slots => A y slots)
      (metricTraceInput_coordFrame (I := I) x₀ y i j σ)

private theorem metricTraceFirstTwoCoeff {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x₀ : M) (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g (A y)
          (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)) x₀ := by
  classical
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                A y
                  (fun q : Fin (s + 2) =>
                    coordinateFrameAt (I := I) x₀ (traceFirstTwoIdx i j σ q) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀ (traceFirstTwoIdx i j σ))
  exact hRhs.congr_of_eventuallyEq
    (metricTraceFirstTwoEvent (I := I) g A x₀ σ)

set_option backward.isDefEq.respectTransparency false in



def metricTraceFirstTwoField {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s p :=
    fun p : M => metricTraceFirstTwo0STensor (I := I) g (A p)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff := metricTraceFirstTwoCoeff (I := I) g A x₀ σ
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel s Real E)
      (Bundle.continuousMultilinearMap Real s E
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin s => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g (A y)
      (fun q : Fin s => coordinateFrameAt (I := I) x₀ (σ q) y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin s => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g (A y)
      (fun q : Fin s => coordinateFrameAt (I := I) x₀ (σ q) y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr
  funext q
  change
    (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
        (b (σ q)) =
      coordinateFrameAt (I := I) x₀ (σ q) y
  change e.symmL Real y (b (σ q)) = e.localFrame b (σ q) y
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) (i := σ q) hy]
  rfl

@[simp] theorem metricTraceFirstTwoField_apply {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x : M) :
    metricTraceFirstTwoField (I := I) (M := M) g A x =
      metricTraceFirstTwo0STensor (I := I) g (A x) := by
  rfl



private theorem metricTraceFirstTwo0STensor_eq_pair_freeze {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) g T tail =
      metricTracePair0SAt (I := I) g (freezeFirstTwo0S (I := I) T tail) := by
  classical
  let basis := coordinateFrameAt_toBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x)
  rw [metricTraceFirstTwo0STensor_apply (I := I) g T tail]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv T tail]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv
    (freezeFirstTwo0S (I := I) T tail)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [freezeFirstTwo0S_apply]














theorem nabla_metricTraceFirstTwo0S {s : ℕ}
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (metricTraceFirstTwoField (I := I) (M := M) g A) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (s + 2) cov A x
            (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) := by
  classical
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X
  choose Vtail hVtailx hVtailcov using fun b : Fin s =>
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x (tail b)
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := freezeTailField (I := I) (M := M) A Vtail
  let traceB : M -> Real := fun y => metricTracePair0SAt (I := I) g (B y)
  have htot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov Xsec (metricTraceFirstTwoField (I := I) (M := M) g A) x
      (fun b : Fin s => tail b)
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov Xsec Vtail
      (metricTraceFirstTwoField (I := I) (M := M) g A) x
  have hfun :
      (fun p : M =>
          metricTraceFirstTwoField (I := I) (M := M) g A p
            (fun a : Fin s => Vtail a p)) = traceB := by
    funext p
    simp only [traceB, B, metricTraceFirstTwoField_apply, freezeTailField_apply]
    rw [metricTraceFirstTwo0STensor_eq_pair_freeze (I := I) g p (A p)
      (fun a : Fin s => Vtail a p)]
  have hcorr :
      (∑ a : Fin s,
        metricTraceFirstTwoField (I := I) (M := M) g A x
          (Function.update (fun b : Fin s => Vtail b x) a
            ((cov (fun p : M => Vtail a p) x) (Xsec x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [hVtailcov a Xsec]
    simp [metricTrace_tensor0S_update_zero]
  have hVtailx_fun : (fun a : Fin s => Vtail a x) = fun b : Fin s => tail b := by
    funext a; exact hVtailx a
  have hleft :
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (metricTraceFirstTwoField (I := I) (M := M) g A) x (Fin.cons X tail) =
        differential1FormFun (I := I) traceB x (fun _ : Fin 1 => X) := by
    have hconsX : Fin.cons (Xsec x) (fun b : Fin s => tail b) =
        (Fin.cons X tail : Fin (s + 1) -> TangentSpace I x) := by
      rw [hXsec]
    calc
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (metricTraceFirstTwoField (I := I) (M := M) g A) x (Fin.cons X tail)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov Xsec (metricTraceFirstTwoField (I := I) (M := M) g A) x
          (fun b : Fin s => tail b) := by
          rw [← hconsX]; exact htot
      _ = extDerivFun (I := I) traceB x (Xsec x) := by
          rw [← hVtailx_fun, heval, hcorr, hfun, sub_zero]
      _ = differential1FormFun (I := I) traceB x (fun _ : Fin 1 => X) := by
          simp [differential1FormFun_apply_eq_extDerivFun, hXsec]
  have htrace02 :
      differential1FormFun (I := I) traceB x (fun _ : Fin 1 => X) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov B x (vec3 (I := I) X (basis i) (basis j)) := by
    simpa [traceB] using
      nablaTrace02 (I := I) (M := M) cov g hmc B basis gInv hinv X
  rw [hleft, htrace02]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hfreeze :=
    tailFreezeNablaGen (I := I) (M := M) cov hcov A Xsec Vtail
      (fun b => hVtailcov b Xsec) (basis i) (basis j)
  rw [← hXsec, show tail = (fun b : Fin s => Vtail b x) from (funext hVtailx).symm]
  exact hfreeze





omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem metricTraceInput_apply {x : M} {s : ℕ} (X Y : TangentSpace I x)
    (tail : Fin s -> TangentSpace I x) (i : Fin (s + 2)) :
    metricTraceInput (I := I) X Y tail i =
      if h0 : (i : ℕ) = 0 then X
      else if h1 : (i : ℕ) = 1 then Y
      else tail ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩ := by
  unfold metricTraceInput
  refine Fin.cases ?_ (fun i1 => ?_) i
  · simp
  · refine Fin.cases ?_ (fun r => ?_) i1
    · rw [Fin.cases_succ, Fin.cases_zero,
        dif_neg (by simp), dif_pos (by simp)]
    · rw [Fin.cases_succ, Fin.cases_succ,
        dif_neg (by simp [Fin.val_succ]), dif_neg (by simp [Fin.val_succ])]
      apply congrArg tail
      apply Fin.ext
      simp [Fin.val_succ]



theorem metricTraceFirstTwoField_eq_sum {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x : M) (tail : Fin s -> TangentSpace I x) :
    (metricTraceFirstTwoField (I := I) (M := M) g A) x tail =
      metricTrace0S2InBasis (I := I)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
        (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
            (I := I) g x k l (extChartAt I x x))
        (A x) tail := by
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
      (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
          (I := I) g x k l (extChartAt I x x))
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
      (A x) tail]

set_option backward.isDefEq.respectTransparency false in

theorem metricTraceFirstTwoField_add {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (A + B)
      = metricTraceFirstTwoField (I := I) (M := M) g A
        + metricTraceFirstTwoField (I := I) (M := M) g B := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hsplit :
      ((metricTraceFirstTwoField (I := I) (M := M) g A
          + metricTraceFirstTwoField (I := I) (M := M) g B) x) tail
        = (metricTraceFirstTwoField (I := I) (M := M) g A x) tail
          + (metricTraceFirstTwoField (I := I) (M := M) g B x) tail := rfl
  rw [hsplit, metricTraceFirstTwoField_eq_sum, metricTraceFirstTwoField_eq_sum,
    metricTraceFirstTwoField_eq_sum]
  have hAB : (A + B) x = A x + B x := rfl
  rw [hAB]
  unfold metricTrace0S2InBasis
  simp only [Tensor0SSpace.add_apply, mul_add, Finset.sum_add_distrib]

set_option backward.isDefEq.respectTransparency false in

theorem metricTraceFirstTwoField_smul {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (c : Real)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (c • A)
      = c • metricTraceFirstTwoField (I := I) (M := M) g A := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hsplit :
      ((c • metricTraceFirstTwoField (I := I) (M := M) g A) x) tail
        = c * (metricTraceFirstTwoField (I := I) (M := M) g A x) tail := rfl
  rw [hsplit, metricTraceFirstTwoField_eq_sum, metricTraceFirstTwoField_eq_sum]
  have hcA : (c • A) x = c • A x := rfl
  rw [hcA]
  unfold metricTrace0S2InBasis
  simp only [Tensor0SSpace.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

set_option backward.isDefEq.respectTransparency false in



theorem metricTraceFirstTwoField_domDomCongr_gen {s s' : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (e : Fin (s + 2) ≃ Fin (s' + 2)) (e' : Fin s ≃ Fin s')
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hcompat : forall (x : M) (X Y : TangentSpace I x)
        (tail : Fin s' -> TangentSpace I x),
      metricTraceInput (I := I) X Y tail ∘ e = metricTraceInput (I := I) X Y (tail ∘ e')) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e A)
      = MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e'
          (metricTraceFirstTwoField (I := I) (M := M) g A) := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s'
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hL := metricTraceFirstTwoField_eq_sum (I := I) (M := M) g
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e A) x tail
  have hR := metricTraceFirstTwoField_eq_sum (I := I) (M := M) g A x (tail ∘ e')
  rw [hL]
  change metricTrace0S2InBasis _ _ _ _ =
    (ContinuousMultilinearMap.domDomCongr e'
      ((metricTraceFirstTwoField (I := I) (M := M) g A) x)) tail
  rw [Tensor0SSpace.domDomCongr_apply]
  change _ = ((metricTraceFirstTwoField (I := I) (M := M) g A) x) (tail ∘ e')
  rw [hR]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change (ContinuousMultilinearMap.domDomCongr e (A x)) _ = _
  rw [Tensor0SSpace.domDomCongr_apply]
  exact congrArg (A x) (hcompat x _ _ tail)




theorem metricTraceFirstTwoField_domDomCongr {s s' : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (e : Fin s ≃ Fin s')
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (Tensor0SBundle.frontExtendEquiv (Tensor0SBundle.frontExtendEquiv e)) A)
      = MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e
          (metricTraceFirstTwoField (I := I) (M := M) g A) := by
  refine metricTraceFirstTwoField_domDomCongr_gen (I := I) (M := M) g
    (Tensor0SBundle.frontExtendEquiv (Tensor0SBundle.frontExtendEquiv e)) e A ?_
  intro x X Y tail
  funext q
  refine Fin.cases ?_ (fun q1 => ?_) q
  · simp only [Function.comp_apply, Tensor0SBundle.frontExtendEquiv_zero, metricTraceInput,
      Fin.cases_zero]
  · refine Fin.cases ?_ (fun r => ?_) q1
    · simp only [Function.comp_apply, Tensor0SBundle.frontExtendEquiv_succ,
        Tensor0SBundle.frontExtendEquiv_zero, metricTraceInput, Fin.cases_succ, Fin.cases_zero]
    · simp only [Function.comp_apply, Tensor0SBundle.frontExtendEquiv_succ,
        metricTraceInput, Fin.cases_succ]

set_option backward.isDefEq.respectTransparency false in




theorem metricTraceFirstTwoField_product {k q : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 2))
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (h : k + 2 + q = k + q + 2) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (finCongr h)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := k + 2) (q := q) A B))
      = MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := k) (q := q)
          (metricTraceFirstTwoField (I := I) (M := M) g A) B := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (k + q)
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have fact1 : forall (X Y : TangentSpace I x),
      ((fun i_1 => metricTraceInput (I := I) X Y tail ((finCongr h) i_1)) ∘ Fin.castAdd q)
        = metricTraceInput (I := I) X Y (tail ∘ Fin.castAdd q) := by
    intro X Y
    funext p
    simp only [Function.comp_apply]
    have hv : ((finCongr h) (Fin.castAdd q p) : ℕ) = (p : ℕ) := by
      simp [finCongr_apply, Fin.val_cast, Fin.val_castAdd]
    rw [metricTraceInput_apply, metricTraceInput_apply]
    simp only [hv]
    by_cases h0 : (p : ℕ) = 0
    · simp [h0]
    · by_cases h1 : (p : ℕ) = 1
      · simp [h1]
      · rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1]
        apply congrArg tail
        apply Fin.ext
        simp
  have fact2 : forall (X Y : TangentSpace I x),
      ((fun i_1 => metricTraceInput (I := I) X Y tail ((finCongr h) i_1)) ∘ Fin.natAdd (k + 2))
        = tail ∘ Fin.natAdd k := by
    intro X Y
    funext r
    simp only [Function.comp_apply]
    have hv : ((finCongr h) (Fin.natAdd (k + 2) r) : ℕ) = (k + 2) + (r : ℕ) := by
      simp [finCongr_apply, Fin.val_cast, Fin.val_natAdd]
    rw [metricTraceInput_apply]
    simp only [hv]
    rw [dif_neg (by omega), dif_neg (by omega)]
    apply congrArg tail
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega
  rw [metricTraceFirstTwoField_eq_sum]
  change metricTrace0S2InBasis _ _
      (ContinuousMultilinearMap.domDomCongr (finCongr h)
        ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := k + 2) (q := q) A B) x)) tail =
    Bundle.continuousMultilinearMap.product_fun
      ((metricTraceFirstTwoField (I := I) (M := M) g A) x) (B x) tail
  rw [Bundle.continuousMultilinearMap.product_fun_apply,
    metricTraceFirstTwoField_eq_sum]
  unfold metricTrace0S2InBasis
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply, fact1, fact2]
  ring







set_option backward.isDefEq.respectTransparency false in

theorem metricTraceFirstTwoField_zero {s : ℕ}
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2))
      = 0 := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  rw [metricTraceFirstTwoField_eq_sum]
  unfold metricTrace0S2InBasis
  simp [ContMDiffSection.coe_zero]















def traceNablaShuffle (s : ℕ) : Equiv.Perm (Fin (s + 2 + 1)) :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 1)

private theorem tns_c1 (s : ℕ) : ((1 : Fin (s + 2 + 1)) : ℕ) = 1 := by simp
private theorem tns_c2 (s : ℕ) : ((2 : Fin (s + 2 + 1)) : ℕ) = 2 := by simp

@[simp] theorem traceNablaShuffle_zero (s : ℕ) : traceNablaShuffle s 0 = 2 := by
  have h20 : (2 : Fin (s + 2 + 1)) ≠ 0 := by rw [Ne, Fin.ext_iff, tns_c2, Fin.val_zero]; omega
  have h21 : (2 : Fin (s + 2 + 1)) ≠ 1 := by rw [Ne, Fin.ext_iff, tns_c2, tns_c1]; omega
  simp only [traceNablaShuffle, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne h20 h21]

@[simp] theorem traceNablaShuffle_one (s : ℕ) : traceNablaShuffle s 1 = 0 := by
  have h10 : (1 : Fin (s + 2 + 1)) ≠ 0 := by rw [Ne, Fin.ext_iff, tns_c1, Fin.val_zero]; omega
  have h12 : (1 : Fin (s + 2 + 1)) ≠ 2 := by rw [Ne, Fin.ext_iff, tns_c1, tns_c2]; omega
  simp only [traceNablaShuffle, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne h10 h12, Equiv.swap_apply_right]

@[simp] theorem traceNablaShuffle_two (s : ℕ) : traceNablaShuffle s 2 = 1 := by
  simp only [traceNablaShuffle, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]

theorem traceNablaShuffle_val_ge (s : ℕ) (p : Fin (s + 2 + 1)) (hp : 3 ≤ (p : ℕ)) :
    traceNablaShuffle s p = p := by
  have hp0 : p ≠ 0 := by rw [Ne, Fin.ext_iff, Fin.val_zero]; omega
  have hp1 : p ≠ 1 := by rw [Ne, Fin.ext_iff, tns_c1]; omega
  have hp2 : p ≠ 2 := by rw [Ne, Fin.ext_iff, tns_c2]; omega
  simp only [traceNablaShuffle, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne hp0 hp2, Equiv.swap_apply_of_ne_of_ne hp0 hp1]


theorem traceNablaShuffle_val (s : ℕ) (p : Fin (s + 2 + 1)) :
    ((traceNablaShuffle s p : Fin (s + 2 + 1)) : ℕ) =
      if (p : ℕ) = 0 then 2 else if (p : ℕ) = 1 then 0 else if (p : ℕ) = 2 then 1
        else (p : ℕ) := by
  rcases eq_or_ne (p : ℕ) 0 with h0 | h0
  · rw [show p = 0 from Fin.ext (by rw [Fin.val_zero]; exact h0), traceNablaShuffle_zero, tns_c2,
      Fin.val_zero, if_pos rfl]
  · rcases eq_or_ne (p : ℕ) 1 with h1 | h1
    · rw [show p = 1 from Fin.ext (by rw [tns_c1]; exact h1), traceNablaShuffle_one, Fin.val_zero,
        tns_c1, if_neg (by omega), if_pos rfl]
    · rcases eq_or_ne (p : ℕ) 2 with h2 | h2
      · rw [show p = 2 from Fin.ext (by rw [tns_c2]; exact h2), traceNablaShuffle_two, tns_c1,
          tns_c2, if_neg (by omega), if_neg (by omega), if_pos rfl]
      · rw [traceNablaShuffle_val_ge s p (by omega), if_neg h0, if_neg h1, if_neg h2]



private theorem consPredVal {V : Type*} {n : ℕ} (c : V) (f : Fin n → V) (q : Fin (n + 1))
    (hq : q ≠ 0) : @Fin.cons n (fun _ => V) c f q = f (q.pred hq) := by
  have h := Fin.cons_succ (α := fun _ => V) c f (q.pred hq)
  rw [Fin.succ_pred] at h
  exact h



omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem traceNablaShuffle_metricTraceInput {x : M} {s : ℕ}
    (a b Z : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    metricTraceInput (I := I) a b (Fin.cons Z tail) ∘ traceNablaShuffle s =
      Fin.cons Z (metricTraceInput (I := I) a b tail) := by
  funext p
  simp only [Function.comp_apply]
  change (Fin.cons a (Fin.cons b (Fin.cons Z tail)) : Fin (s + 2 + 1) → TangentSpace I x)
      (traceNablaShuffle s p)
    = (Fin.cons Z (Fin.cons a (Fin.cons b tail)) : Fin (s + 2 + 1) → TangentSpace I x) p
  have hv := traceNablaShuffle_val s p
  rcases eq_or_ne (p : ℕ) 0 with h0 | h0
  · have hp : p = 0 := Fin.ext (by rw [Fin.val_zero]; exact h0)
    have hs : traceNablaShuffle s p ≠ 0 := by
      rw [Ne, Fin.ext_iff, Fin.val_zero, hv, if_pos h0]; omega
    rw [consPredVal a _ _ hs]
    have hs1 : (traceNablaShuffle s p).pred hs ≠ 0 := by
      rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_pred, hv, if_pos h0]; omega
    rw [consPredVal b _ _ hs1]
    rw [show ((traceNablaShuffle s p).pred hs).pred hs1 = 0 from
      Fin.ext (by rw [Fin.val_zero, Fin.val_pred, Fin.val_pred, hv, if_pos h0]), Fin.cons_zero]
    rw [hp, Fin.cons_zero]
  · have hp0 : p ≠ 0 := by rw [Ne, Fin.ext_iff, Fin.val_zero]; exact h0
    rw [consPredVal Z _ _ hp0]
    rcases eq_or_ne (p : ℕ) 1 with h1 | h1
    · rw [show traceNablaShuffle s p = 0 from
        Fin.ext (by rw [Fin.val_zero, hv, if_neg h0, if_pos h1]), Fin.cons_zero]
      rw [show p.pred hp0 = 0 from Fin.ext (by rw [Fin.val_zero, Fin.val_pred]; omega), Fin.cons_zero]
    · rcases eq_or_ne (p : ℕ) 2 with h2 | h2
      · have hs : traceNablaShuffle s p ≠ 0 := by
          rw [Ne, Fin.ext_iff, Fin.val_zero, hv, if_neg h0, if_neg h1, if_pos h2]; omega
        rw [consPredVal a _ _ hs]
        rw [show (traceNablaShuffle s p).pred hs = 0 from
          Fin.ext (by rw [Fin.val_zero, Fin.val_pred, hv, if_neg h0, if_neg h1, if_pos h2]),
          Fin.cons_zero]
        have hp1 : p.pred hp0 ≠ 0 := by rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_pred]; omega
        rw [consPredVal a _ _ hp1]
        rw [show (p.pred hp0).pred hp1 = 0 from
          Fin.ext (by rw [Fin.val_zero, Fin.val_pred, Fin.val_pred]; omega), Fin.cons_zero]
      · have hge : 3 ≤ (p : ℕ) := by omega
        have hs : traceNablaShuffle s p ≠ 0 := by
          rw [Ne, Fin.ext_iff, Fin.val_zero, traceNablaShuffle_val_ge s p hge]; omega
        rw [consPredVal a _ _ hs]
        have hs1 : (traceNablaShuffle s p).pred hs ≠ 0 := by
          rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_pred, traceNablaShuffle_val_ge s p hge]; omega
        rw [consPredVal b _ _ hs1]
        have hs2 : ((traceNablaShuffle s p).pred hs).pred hs1 ≠ 0 := by
          rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_pred, Fin.val_pred,
            traceNablaShuffle_val_ge s p hge]; omega
        rw [consPredVal Z _ _ hs2]
        have hp1 : p.pred hp0 ≠ 0 := by rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_pred]; omega
        rw [consPredVal a _ _ hp1]
        have hp2 : (p.pred hp0).pred hp1 ≠ 0 := by
          rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_pred, Fin.val_pred]; omega
        rw [consPredVal b _ _ hp2]
        congr 1
        have hval : ((traceNablaShuffle s p : Fin (s + 2 + 1)) : ℕ) = (p : ℕ) := by
          rw [traceNablaShuffle_val_ge s p hge]
        rw [Fin.ext_iff]
        simp only [Fin.val_pred, hval]

set_option backward.isDefEq.respectTransparency false in





theorem nablaRealizes_metricTraceFirstTwo {s : ℕ}
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 + 1))
    (hnablaA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) cov A nablaA) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (metricTraceFirstTwoField (I := I) (M := M) g A)
      (metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (traceNablaShuffle s) nablaA)) := by
  classical
  intro X x slots
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    (fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x k l (extChartAt I x x)) with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  rw [← totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (metricTraceFirstTwoField (I := I) (M := M) g A) x slots,
    nabla_metricTraceFirstTwo0S (I := I) (M := M) cov hcov g hmc A basis gInv hinv (X x) slots]
  rw [metricTraceFirstTwoField_eq_sum (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (traceNablaShuffle s) nablaA) x
        (Fin.cons (X x) slots)]
  rw [← hbasis, ← hgInv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change (ContinuousMultilinearMap.domDomCongr (traceNablaShuffle s) (nablaA x)) _ = _
  rw [Tensor0SSpace.domDomCongr_apply,
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) cov X A x (metricTraceInput (I := I) (basis i) (basis j) slots),
    ← hnablaA X x (metricTraceInput (I := I) (basis i) (basis j) slots)]
  exact congrArg _ (traceNablaShuffle_metricTraceInput (I := I) (basis i) (basis j) (X x) slots)

end

end DifferentialGeometry.Integral.Connection
