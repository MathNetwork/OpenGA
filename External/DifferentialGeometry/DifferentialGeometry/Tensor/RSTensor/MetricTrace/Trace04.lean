import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection

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

theorem metricTrace_metricField_eq0S
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.metricTensorField (I := I) g x =
      metricTensor0S (I := I) g x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply Tensor0SBundle.ext0S_basis (I := I) basis
  intro slots
  simp [Tensor0SBundle.component0S_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem metricTrace_finCons_vec2_eq_vec3 {x : M}
    (X Y Z : TangentSpace I x) :
    Fin.cons X (vec2 (I := I) Y Z) = vec3 (I := I) X Y Z := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem metricTrace_finCons_vec3_eq_vec4 {x : M}
    (X Y Z U : TangentSpace I x) :
    Fin.cons X (vec3 (I := I) Y Z U) = vec4 (I := I) X Y Z U := by
  funext a
  fin_cases a <;> rfl



def trace04Perm : Equiv.Perm (Fin 4) where
  toFun q := if q = 0 then 0 else if q = 1 then 2 else if q = 2 then 3 else 1
  invFun q := if q = 0 then 0 else if q = 1 then 3 else if q = 2 then 1 else 2
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

omit [FiniteDimensional ℝ E] in
theorem metricTrace_tensor0S_curry_apply_cons
    {x : M} (s : ℕ)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
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

omit [FiniteDimensional ℝ E] in
theorem metricTrace_tensor0S_update_zero {s : ℕ} {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> TangentSpace I x) (a : Fin s) :
    A (Function.update slots a 0) = 0 := by
  exact A.map_coord_zero a (by simp)

private def trace04Slots
    (i j : CoordinateIdx (𝕜 := Real) E)
    (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    Fin 4 -> CoordinateIdx (𝕜 := Real) E
  | ⟨0, _⟩ => i
  | ⟨1, _⟩ => tail 0
  | ⟨2, _⟩ => tail 1
  | ⟨3, _⟩ => j

private theorem trace04Slots_apply {x₀ y : M}
    (i j : CoordinateIdx (𝕜 := Real) E)
    (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    (fun q : Fin 4 =>
      metricTraceInput (I := I)
          (coordinateFrameAt (I := I) x₀ i y)
          (coordinateFrameAt (I := I) x₀ j y)
          (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y)
        (trace04Perm q)) =
      fun q : Fin 4 =>
        coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y := by
  funext q
  fin_cases q
  · simp [trace04Perm, metricTraceInput, trace04Slots]
  · change
      Fin.cases (coordinateFrameAt (I := I) x₀ i y)
          (fun i : Fin 3 =>
            Fin.cases (coordinateFrameAt (I := I) x₀ j y)
              (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y) i)
          (Fin.succ (Fin.succ 0)) =
        coordinateFrameAt (I := I) x₀ (tail 0) y
    rw [Fin.cases_succ, Fin.cases_succ]
  · change
      Fin.cases (coordinateFrameAt (I := I) x₀ i y)
          (fun i : Fin 3 =>
            Fin.cases (coordinateFrameAt (I := I) x₀ j y)
              (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y) i)
          (Fin.succ (Fin.succ (Fin.succ 0))) =
        coordinateFrameAt (I := I) x₀ (tail 1) y
    rw [Fin.cases_succ, Fin.cases_succ]
    rfl
  · change
      Fin.cases (coordinateFrameAt (I := I) x₀ i y)
          (fun i : Fin 3 =>
            Fin.cases (coordinateFrameAt (I := I) x₀ j y)
              (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y) i)
          (Fin.succ 0) =
        coordinateFrameAt (I := I) x₀ j y
    rw [Fin.cases_succ, Fin.cases_zero]

private theorem trace04Event
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x₀ : M) (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g
          ((A y).domDomCongr trace04Perm)
          (fun q : Fin 2 =>
            coordinateFrameAt (I := I) x₀ (tail q) y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y
                (fun q : Fin 4 =>
                  coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have htrace :=
    metricTraceFirstTwo0STensor_apply (I := I) g
      ((A y).domDomCongr trace04Perm)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y)
  have hsum :=
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv
      (gInvBasisAt (I := I) g x₀ hy)
      ((A y).domDomCongr trace04Perm)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y)
  calc
    metricTraceFirstTwo0STensor (I := I) g
        ((A y).domDomCongr trace04Perm)
        (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (tail q) y)
        =
      metricTraceFirstTwo0SAt (I := I) g
        ((A y).domDomCongr trace04Perm)
        (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (tail q) y) := htrace
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            ((A y).domDomCongr trace04Perm)
              (metricTraceInput (I := I) (basis i) (basis j)
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (tail q) y)) := hsum
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x₀ i j
              (extChartAt I x₀ y) *
            A y
              (fun q : Fin 4 =>
                coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [ContinuousMultilinearMap.domDomCongr_apply]
        simpa [basis, coordinateFrameAt_basis_apply] using
          congrArg (fun slots => A y slots)
            (trace04Slots_apply (I := I) (x₀ := x₀) (y := y) i j tail)

private theorem trace04Coeff
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x₀ : M) (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g
          ((A y).domDomCongr trace04Perm)
          (fun q : Fin 2 =>
            coordinateFrameAt (I := I) x₀ (tail q) y)) x₀ := by
  classical
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                A y
                  (fun q : Fin 4 =>
                    coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (trace04Slots i j tail))
  exact hRhs.congr_of_eventuallyEq
    (trace04Event (I := I) g A x₀ tail)

set_option backward.isDefEq.respectTransparency false in


def trace04Field
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M =>
      metricTraceFirstTwo0STensor (I := I) g
        ((A p).domDomCongr trace04Perm)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff := trace04Coeff (I := I) g A x₀ σ
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 2 Real E)
      (Bundle.continuousMultilinearMap Real 2 E
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g
      ((A y).domDomCongr trace04Perm)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (σ q) y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g
      ((A y).domDomCongr trace04Perm)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (σ q) y)
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

@[simp] theorem trace04Field_apply
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) :
    trace04Field (I := I) (M := M) g A x =
      metricTraceFirstTwo0STensor (I := I) g
      ((A x).domDomCongr trace04Perm) := by
  rfl

end

end DifferentialGeometry.Integral.Connection
