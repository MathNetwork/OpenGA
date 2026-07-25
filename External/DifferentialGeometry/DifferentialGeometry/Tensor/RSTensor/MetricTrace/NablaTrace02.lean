import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Trace04

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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem metricTrace_input_vec2_eq_vec4 {x : M}
    (X Y Z U : TangentSpace I x) :
    metricTraceInput (I := I) X Y (vec2 (I := I) Z U) =
      vec4 (I := I) X Y Z U := by
  funext a
  fin_cases a <;> rfl

private def freezeHead03Slots
    (x₀ : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Fin 3 -> (y : M) -> TangentSpace I y
  | ⟨0, _⟩ => fun y => Y y
  | ⟨1, _⟩ => coordinateFrameAt (I := I) x₀ (σ 0)
  | ⟨2, _⟩ => coordinateFrameAt (I := I) x₀ (σ 1)

private theorem freezeHead03Slots_vec3
    (x₀ y : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    (fun q : Fin 3 => freezeHead03Slots (I := I) x₀ σ Y q y) =
      vec3 (I := I) (Y y)
        (coordinateFrameAt (I := I) x₀ (σ 0) y)
        (coordinateFrameAt (I := I) x₀ (σ 1) y) := by
  funext q
  fin_cases q <;> rfl

set_option backward.isDefEq.respectTransparency false in


noncomputable def freezeHead03Field
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 p (A p) (Y p)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (fun q : Fin 3 => freezeHead03Slots (I := I) x₀ σ Y q y))
        x₀ := by
    let v : Fin 3 -> (y : M) -> TangentSpace I y :=
      fun q y => freezeHead03Slots (I := I) x₀ σ Y q y
    have hv : ∀ q : Fin 3,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v q y)) x₀ := by
      intro q
      fin_cases q
      · exact Y.contMDiff x₀
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 0)
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 1)
    have hA := TensorMultilinear.contMDiffAt_section_apply_gen
      (𝕜 := Real) (I := I) (M := M) (n := 3)
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
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 3 => freezeHead03Slots (I := I) x₀ σ Y q y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 3 => freezeHead03Slots (I := I) x₀ σ Y q y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y
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
  rw [metricTrace_tensor0S_curry_apply_cons]
  rw [metricTrace_finCons_vec2_eq_vec3]
  rw [freezeHead03Slots_vec3]

@[simp] theorem freezeHead03Field_apply
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    freezeHead03Field (I := I) (M := M) A Y x =
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x (A x) (Y x) := by
  rfl

private def freezeTail04Slots
    (x₀ : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Fin 4 -> (y : M) -> TangentSpace I y
  | ⟨0, _⟩ => coordinateFrameAt (I := I) x₀ (σ 0)
  | ⟨1, _⟩ => coordinateFrameAt (I := I) x₀ (σ 1)
  | ⟨2, _⟩ => fun y => Y y
  | ⟨3, _⟩ => fun y => Z y

private theorem freezeTail04Slots_vec4
    (x₀ y : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y) =
      vec4 (I := I)
        (coordinateFrameAt (I := I) x₀ (σ 0) y)
        (coordinateFrameAt (I := I) x₀ (σ 1) y)
        (Y y) (Z y) := by
  funext q
  fin_cases q <;> rfl

set_option backward.isDefEq.respectTransparency false in



noncomputable def freezeTail04Field
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => freezeFirstTwo0S (I := I) (A p)
      (vec2 (I := I) (Y p) (Z p))
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y))
        x₀ := by
    let v : Fin 4 -> (y : M) -> TangentSpace I y :=
      fun q y => freezeTail04Slots (I := I) x₀ σ Y Z q y
    have hv : ∀ q : Fin 4,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v q y)) x₀ := by
      intro q
      fin_cases q
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 0)
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 1)
      · exact Y.contMDiff x₀
      · exact Z.contMDiff x₀
    have hA := TensorMultilinear.contMDiffAt_section_apply_gen
      (𝕜 := Real) (I := I) (M := M) (n := 4)
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
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y
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
  rw [metricTrace_input_vec2_eq_vec4]
  rw [freezeTail04Slots_vec4]

@[simp] theorem freezeTail04Field_apply
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    freezeTail04Field (I := I) (M := M) A Y Z x =
      freezeFirstTwo0S (I := I) (A x) (vec2 (I := I) (Y x) (Z x)) := by
  rfl

private def freezeMiddle04Slots
    (x₀ : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Fin 4 -> (y : M) -> TangentSpace I y
  | ⟨0, _⟩ => coordinateFrameAt (I := I) x₀ (σ 0)
  | ⟨1, _⟩ => fun y => Y y
  | ⟨2, _⟩ => fun y => Z y
  | ⟨3, _⟩ => coordinateFrameAt (I := I) x₀ (σ 1)

private theorem freezeMiddle04Slots_vec4
    (x₀ y : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    (fun q : Fin 4 => freezeMiddle04Slots (I := I) x₀ σ Y Z q y) =
      vec4 (I := I)
        (coordinateFrameAt (I := I) x₀ (σ 0) y)
        (Y y) (Z y)
        (coordinateFrameAt (I := I) x₀ (σ 1) y) := by
  funext q
  fin_cases q <;> rfl

set_option backward.isDefEq.respectTransparency false in



noncomputable def freezeMiddle04Field
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => freezeFirstTwo0S (I := I)
      ((A p).domDomCongr trace04Perm)
      (vec2 (I := I) (Y p) (Z p))
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (fun q : Fin 4 => freezeMiddle04Slots (I := I) x₀ σ Y Z q y))
        x₀ := by
    let v : Fin 4 -> (y : M) -> TangentSpace I y :=
      fun q y => freezeMiddle04Slots (I := I) x₀ σ Y Z q y
    have hv : ∀ q : Fin 4,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v q y)) x₀ := by
      intro q
      fin_cases q
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 0)
      · exact Y.contMDiff x₀
      · exact Z.contMDiff x₀
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 1)
    have hA := TensorMultilinear.contMDiffAt_section_apply_gen
      (𝕜 := Real) (I := I) (M := M) (n := 4)
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
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 4 => freezeMiddle04Slots (I := I) x₀ σ Y Z q y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 4 => freezeMiddle04Slots (I := I) x₀ σ Y Z q y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y
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
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [metricTrace_input_vec2_eq_vec4]
  rw [freezeMiddle04Slots_vec4]
  congr 1
  funext q
  fin_cases q <;> simp [trace04Perm, DifferentialGeometry.Integral.Connection.vec4]

@[simp] theorem freezeMiddle04Field_apply
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    freezeMiddle04Field (I := I) (M := M) A Y Z x =
      freezeFirstTwo0S (I := I)
        ((A x).domDomCongr trace04Perm)
        (vec2 (I := I) (Y x) (Z x)) := by
  rfl




theorem nablaTrace02
    [T2Space M] [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X : TangentSpace I x) :
    let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
    let nablaA :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov A x
    let dTrace := differential1FormFun (I := I) traceA x
    dTrace (fun _ : Fin 1 => X) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaA (vec3 (I := I) X (basis i) (basis j)) := by
  classical
  let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
  let nablaA :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov A x
  let dTrace := differential1FormFun (I := I) traceA x
  let Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x X).choose
  have hXsec : Xsec x = X :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x X).choose_spec
  have hinner :=
    inner0S_two_nabla (I := I) cov g hmc
      (Tensor0SBundle.metricTensorField (I := I) g) A Xsec x
  have hmetric :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov Xsec
        (Tensor0SBundle.metricTensorField (I := I) g) x = 0 :=
    Tensor0SBundle.nabla_metric_zero (I := I) cov g hmc Xsec x
  have htrace :
      extDerivFun (I := I) traceA x (Xsec x) =
        metricTracePair0SAt (I := I) g
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec A x) := by
    have hfun :
        traceA =
          fun y : M =>
            inner0S (I := I) g y 2
              (Tensor0SBundle.metricTensorField (I := I) g y) (A y) := by
      funext y
      simp [traceA, metricTracePair0SAt, metricTrace_metricField_eq0S]
    have hzero :
        inner0S (I := I) g x 2
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
          (A x) = 0 := by
      change (((tensor0SMetricData (I := I) g x 2).flat)
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x))
          (A x) = 0
      have hflat :
          (tensor0SMetricData (I := I) g x 2).flat
            (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 x) = 0 := by
        exact LinearMap.map_zero
          ((tensor0SMetricData (I := I) g x 2).flat.toLinearMap :
            Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 x →ₗ[Real]
            Module.Dual Real
              (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 x))
      rw [hflat]
      rfl
    rw [hfun]
    rw [hinner, hmetric]
    rw [hzero]
    simp [metricTracePair0SAt, metricTrace_metricField_eq0S]
  have hnabla :
      ∀ i j : Idx,
        nablaA (vec3 (I := I) X (basis i) (basis j)) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec A x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    have h :=
      totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Xsec A x
        (vec2 (I := I) (basis i) (basis j))
    simpa [nablaA, hXsec, metricTrace_finCons_vec2_eq_vec3 (I := I)] using h
  calc
    dTrace (fun _ : Fin 1 => X)
        = extDerivFun (I := I) traceA x X := by
            simp [dTrace, differential1FormFun_apply_eq_extDerivFun]
    _ = extDerivFun (I := I) traceA x (Xsec x) := by
            rw [hXsec]
    _ = metricTracePair0SAt (I := I) g
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec A x) := htrace
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov Xsec A x (vec2 (I := I) (basis i) (basis j)) := by
            exact metricTracePair0SAt_eq_sum_basis
              (I := I) g basis gInv hinv
              (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 cov Xsec A x)
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaA (vec3 (I := I) X (basis i) (basis j)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [hnabla i j]



theorem dTrace02_eq
    [T2Space M] [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
    differential1FormFun (I := I) traceA x (fun _ : Fin 1 => X x) =
      metricTracePair0SAt (I := I) g
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x) := by
  classical
  let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
  let basis := coordinateFrameAt_toBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j
        (extChartAt I x x)
  have hinv :
      MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x)
  have htrace :=
    nablaTrace02 (I := I) (M := M) cov g hmc A basis gInv hinv (X x)
  have htot :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov A x (vec3 (I := I) (X x) (basis i) (basis j)) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    have h :=
      totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov X A x
        (vec2 (I := I) (basis i) (basis j))
    simpa [metricTrace_finCons_vec2_eq_vec3 (I := I)] using h
  have hsum :
      metricTracePair0SAt (I := I) g
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x) =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j *
              nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 cov X A x (vec2 (I := I) (basis i) (basis j)) := by
    exact metricTracePair0SAt_eq_sum_basis
      (I := I) g basis gInv hinv
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X A x)
  dsimp [traceA] at htrace ⊢
  calc
    differential1FormFun (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (A y)) x
        (fun _ : Fin 1 => X x)
        =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov A x (vec3 (I := I) (X x) (basis i) (basis j)) := htrace
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov X A x (vec2 (I := I) (basis i) (basis j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [htot i j]
    _ =
      metricTracePair0SAt (I := I) g
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x) := hsum.symm


end

end DifferentialGeometry.Integral.Connection
