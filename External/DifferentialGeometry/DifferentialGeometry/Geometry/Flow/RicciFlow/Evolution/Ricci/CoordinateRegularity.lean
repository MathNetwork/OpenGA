import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Commutator

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

section CoordinateFrameRicciEvolution

open DifferentialGeometry.Tensor.Coordinates



theorem coordInvMdiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => coordInv (I := I) S x₀ t y a b) x₀ := by
  simpa [coordInv] using
    DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt (I := I) (S.family.metric t) x₀ a b



theorem coordInvMdiffOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => coordInv (I := I) S x₀ t y a b) x := by
  simpa [coordInv] using
    DifferentialGeometry.Integral.Connection.coordGInvMdiff (I := I) (S.family.metric t) x₀ hx a b



omit [SigmaCompactSpace M] [T2Space M] in
theorem coordMetricMdiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          t y a b) x₀ := by
  simpa [metricCompInFrame, DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame] using
    DifferentialGeometry.Tensor.Coordinates.metricComp_mdiffAt (I := I) (S.family.metric t)
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) a b



omit [SigmaCompactSpace M] [T2Space M] in
theorem coordMetricMdiffOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          t y a b) x := by
  simpa [metricCompInFrame, DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame] using
    DifferentialGeometry.Tensor.Coordinates.metricComp_mdiffAt (I := I) (S.family.metric t)
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀)
      hx a b



theorem coordInvCovZero
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (d k l : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricCovDerivCompInFrame (I := I) (coordInv (I := I) S x₀)
      (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (t : Real) x₀ d k l = 0 := by
  exact invCovZeroLocal
    (I := I) S (coordInv (I := I) S x₀)
    (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordInvLocal (I := I) S x₀) (t : Real)
    (DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.metricCompatibleAt_regular
      (I := I) S.family t)
    (coordinateFrameSet_open (I := I) x₀)
    (coordinateFrameAt_mem (I := I) x₀)
    (fun a b => coordInvMdiff (I := I) S x₀ (t : Real) a b)
    (fun a b => coordMetricMdiff (I := I) S x₀ (t : Real) a b)
    d k l



theorem coordInvCovZeroOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (d k l : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricCovDerivCompInFrame (I := I) (coordInv (I := I) S x₀)
      (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (t : Real) x d k l = 0 := by
  exact invCovZeroLocal
    (I := I) S (coordInv (I := I) S x₀)
    (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordInvLocal (I := I) S x₀) (t : Real)
    (DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.metricCompatibleAt_regular
      (I := I) S.family t)
    (coordinateFrameSet_open (I := I) x₀)
    hx
    (fun a b => coordInvMdiffOn (I := I) S x₀ (t : Real) x hx a b)
    (fun a b => coordMetricMdiffOn (I := I) S x₀ (t : Real) x hx a b)
    d k l



omit [SigmaCompactSpace M] in
theorem coordRicciMdiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          t y a b) x := by
  let Idx := CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x₀
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    simpa [frame] using
      (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hx r
  let V : Fin 2 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else frame b y
  have hV : ∀ q : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt b
  have hslots : ∀ y,
      (fun q : Fin 2 => V q y) =
        DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame a y) (frame b y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hfun :
      (fun y : M => S.ricci t y (fun q : Fin 2 => V q y)) =
        fun y : M =>
          ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
            t y a b := by
    funext y
    rw [hslots y]
    rfl
  have hEval :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.ricci t y (fun q : Fin 2 => V q y)) x :=
    tensor0SField_eval_C1_slots_mdiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (S.ricci t) V x
      (fun q => (hV q).of_le (by simp))
  simpa [hfun] using hEval



omit [SigmaCompactSpace M] in
theorem coordNablaReg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
          t y a i j) x₀ := by
  let Idx := CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x₀
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) hcov (S.ricci t)
  let V : Fin 3 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else if q = 1 then frame i y else frame j y
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
      simpa [frame] using
        (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) r
    exact htop.of_le (by simp)
  have hV_at : ∀ q : Fin 3,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt i
    · simpa [V] using hframeAt j
  have hslots : ∀ y,
      (fun q : Fin 3 => V q y) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a y) (frame i y) (frame j y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hmdiff :=
    tensor0SField_eval_C1_slots_mdiffAt
      (I := I) (M := M) (α := derivs.nablaA) (V := V) x₀ hV_at
  have hfun :
      (fun y : M => derivs.nablaA y (fun q : Fin 3 => V q y)) =
        fun y : M =>
          nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t y a i j := by
    funext y
    rw [hslots y]
    simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection,
      frame]
  simpa [hfun] using hmdiff



omit [SigmaCompactSpace M] in
theorem coordNablaRegOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
          t y a i j) x := by
  let Idx := CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x₀
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) hcov (S.ricci t)
  let V : Fin 3 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else if q = 1 then frame i y else frame j y
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
      simpa [frame] using
        (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀) hx r
    exact htop.of_le (by simp)
  have hV_at : ∀ q : Fin 3,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt i
    · simpa [V] using hframeAt j
  have hslots : ∀ y,
      (fun q : Fin 3 => V q y) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a y) (frame i y) (frame j y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hmdiff :=
    tensor0SField_eval_C1_slots_mdiffAt
      (I := I) (M := M) (α := derivs.nablaA) (V := V) x hV_at
  have hfun :
      (fun y : M => derivs.nablaA y (fun q : Fin 3 => V q y)) =
        fun y : M =>
          nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t y a i j := by
    funext y
    rw [hslots y]
    simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection,
      frame]
  simpa [hfun] using hmdiff



omit [SigmaCompactSpace M] in
theorem coordNablaReal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (d a b : CoordinateIdx (𝕜 := Real) E) :
    nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ d a b =
      ricciCovDerivCompInFrame
        (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ d a b := by
  classical
  let Idx := CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x₀
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame
      (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) hcov (S.ricci t)
  let V : Fin 2 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else frame b y
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x₀ (frame d x₀)).choose
  have hX : X x₀ = frame d x₀ := by
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x₀ (frame d x₀)).choose_spec
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
      simpa [frame] using
        (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) r
    exact htop.of_le (by simp)
  have hV_at : ∀ q : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt b
  have hslots : ∀ y,
      (fun q : Fin 2 => V q y) =
        DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame a y) (frame b y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
  have heval :=
    TotalNabla0SRealizes.eval_C1_slots (I := I) (s := 2)
      (h := (derivs.first)) X V x₀ hV_at
  have hcons :
      Fin.cons (X x₀) (fun q : Fin 2 => V q x₀) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame d x₀) (frame a x₀) (frame b x₀) := by
    rw [hX, hslots x₀]
    funext q
    fin_cases q <;> rfl
  rw [hcons] at heval
  rw [hX] at heval
  have hleft :
      derivs.nablaA x₀
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame d x₀) (frame a x₀) (frame b x₀)) =
        nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ d a b := by
    simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection,
      frame]
  have hfun :
      (fun p : M => S.ricci t p (fun a : Fin 2 => V a p)) =
        fun p : M => ricciCompInFrame (I := I) S frame t p a b := by
    funext p
    rw [hslots p]
    rfl
  have hterm0 :
      S.ricci t x₀
          (Function.update (fun q : Fin 2 => V q x₀) (0 : Fin 2)
            ((S.family.connection t) (V 0) x₀ (frame d x₀))) =
        S.ricciAt t x₀
          (DifferentialGeometry.Integral.Connection.vec2
            ((S.family.connection t) (frame a) x₀ (frame d x₀))
            (frame b x₀)) := by
    have harg :
        Function.update (fun q : Fin 2 => V q x₀) (0 : Fin 2)
            ((S.family.connection t) (V 0) x₀ (frame d x₀)) =
          DifferentialGeometry.Integral.Connection.vec2
            ((S.family.connection t) (frame a) x₀ (frame d x₀))
            (frame b x₀) := by
      funext q
      fin_cases q <;> simp [Function.update, V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [harg]
    simp [SolutionOn.ricciAt_eq]
  have hterm1 :
      S.ricci t x₀
          (Function.update (fun q : Fin 2 => V q x₀) (1 : Fin 2)
            ((S.family.connection t) (V 1) x₀ (frame d x₀))) =
        S.ricciAt t x₀
          (DifferentialGeometry.Integral.Connection.vec2
            (frame a x₀)
            ((S.family.connection t) (frame b) x₀ (frame d x₀))) := by
    have harg :
        Function.update (fun q : Fin 2 => V q x₀) (1 : Fin 2)
            ((S.family.connection t) (V 1) x₀ (frame d x₀)) =
          DifferentialGeometry.Integral.Connection.vec2
            (frame a x₀)
            ((S.family.connection t) (frame b) x₀ (frame d x₀)) := by
      funext q
      fin_cases q <;> simp [Function.update, V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [harg]
    simp [SolutionOn.ricciAt_eq]
  rw [hleft, hfun] at heval
  rw [Fin.sum_univ_two, hterm0, hterm1] at heval
  simpa [ricciCovDerivCompInFrame, frame, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    using heval



omit [SigmaCompactSpace M] in
theorem coordNablaRealOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) :
    NablaRicciComponentsByConnectionInFrameOn
      (I := I) S (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀)
      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)) := by
  classical
  intro t x hx d a b
  let Idx := CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x₀
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame
      (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) hcov (S.ricci t)
  let V : Fin 2 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else frame b y
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (frame d x)).choose
  have hX : X x = frame d x := by
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (frame d x)).choose_spec
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
      simpa [frame] using
        (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀) hx r
    exact htop.of_le (by simp)
  have hV_at : ∀ q : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt b
  have hslots : ∀ y,
      (fun q : Fin 2 => V q y) =
        DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame a y) (frame b y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
  have heval :=
    TotalNabla0SRealizes.eval_C1_slots (I := I) (s := 2)
      (h := (derivs.first)) X V x hV_at
  have hcons :
      Fin.cons (X x) (fun q : Fin 2 => V q x) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame d x) (frame a x) (frame b x) := by
    rw [hX, hslots x]
    funext q
    fin_cases q <;> rfl
  rw [hcons] at heval
  rw [hX] at heval
  have hleft :
      derivs.nablaA x
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame d x) (frame a x) (frame b x)) =
        nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b := by
    simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection,
      frame]
  have hfun :
      (fun p : M => S.ricci t p (fun a : Fin 2 => V a p)) =
        fun p : M => ricciCompInFrame (I := I) S frame t p a b := by
    funext p
    rw [hslots p]
    rfl
  have hterm0 :
      S.ricci t x
          (Function.update (fun q : Fin 2 => V q x) (0 : Fin 2)
            ((S.family.connection t) (V 0) x (frame d x))) =
        S.ricciAt t x
          (DifferentialGeometry.Integral.Connection.vec2
            ((S.family.connection t) (frame a) x (frame d x))
            (frame b x)) := by
    have harg :
        Function.update (fun q : Fin 2 => V q x) (0 : Fin 2)
            ((S.family.connection t) (V 0) x (frame d x)) =
          DifferentialGeometry.Integral.Connection.vec2
            ((S.family.connection t) (frame a) x (frame d x))
            (frame b x) := by
      funext q
      fin_cases q <;> simp [Function.update, V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [harg]
    simp [SolutionOn.ricciAt_eq]
  have hterm1 :
      S.ricci t x
          (Function.update (fun q : Fin 2 => V q x) (1 : Fin 2)
            ((S.family.connection t) (V 1) x (frame d x))) =
        S.ricciAt t x
          (DifferentialGeometry.Integral.Connection.vec2
            (frame a x)
            ((S.family.connection t) (frame b) x (frame d x))) := by
    have harg :
        Function.update (fun q : Fin 2 => V q x) (1 : Fin 2)
            ((S.family.connection t) (V 1) x (frame d x)) =
          DifferentialGeometry.Integral.Connection.vec2
            (frame a x)
            ((S.family.connection t) (frame b) x (frame d x)) := by
      funext q
      fin_cases q <;> simp [Function.update, V, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [harg]
    simp [SolutionOn.ricciAt_eq]
  rw [hleft, hfun] at heval
  rw [Fin.sum_univ_two, hterm0, hterm1] at heval
  simpa [ricciCovDerivCompInFrame, frame, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    using heval







theorem coordNab2Can
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x0 : M)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 3 (S.family.connection t) nablaA nabla2A)
    (hnabla : ∀ y a i j,
      nablaA y
          (DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (coordinateFrameAt (I := I) x0 a y)
            (coordinateFrameAt (I := I) x0 i y)
            (coordinateFrameAt (I := I) x0 j y)) =
        nablaRicComp (I := I) S
          (coordinateFrameAt (I := I) x0) t y a i j) :
    ∀ d a i j,
      nabla2A x0
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (coordinateFrameAt (I := I) x0 d x0)
            (coordinateFrameAt (I := I) x0 a x0)
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0)) =
        coordNab2Ric (I := I) S x0 t x0 d a i j := by
  classical
  intro d a i j
  let Idx := CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x0
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame
      (coordinateFrameSet (I := I) x0) :=
    coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hx0 : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  let V : Fin 3 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else if q = 1 then frame i y else frame j y
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x0 (frame d x0)).choose
  have hX : X x0 = frame d x0 := by
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x0 (frame d x0)).choose_spec
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x0 := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x0 := by
      simpa [frame] using
        (coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffAt
          (coordinateFrameSet_open (I := I) x0)
          (coordinateFrameAt_mem (I := I) x0) r
    exact htop.of_le (by simp)
  have hV_at : ∀ q : Fin 3,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x0 := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt i
    · simpa [V] using hframeAt j
  have hslots3 : ∀ y,
      (fun q : Fin 3 => V q y) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a y) (frame i y) (frame j y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hslots4 :
      Fin.cons (X x0) (fun q : Fin 3 => V q x0) =
        DifferentialGeometry.Integral.Connection.vec4 (I := I) (frame d x0) (frame a x0) (frame i x0)
          (frame j x0) := by
    rw [hX, hslots3 x0]
    funext q
    fin_cases q <;> rfl
  have hfun :
      (fun y : M => nablaA y (fun q : Fin 3 => V q y)) =
        fun y : M =>
          nablaRicComp (I := I) S (coordinateFrameAt (I := I) x0)
            t y a i j := by
    funext y
    rw [hslots3 y]
    simpa [frame] using hnabla y a i j
  have heval :=
    TotalNabla0SRealizes.eval_C1_slots (I := I) h2 X V x0 hV_at
  rw [hslots4, hfun, hX] at heval
  let Γ : Idx -> Idx -> Idx -> Real :=
    fun u v p =>
      christoffelSymbolInFrame
        (S.family.connection t) frame hframe x0 u v p
  let N : Idx -> Idx -> Idx -> Real :=
    fun u v w =>
      nablaRicComp (I := I) S (coordinateFrameAt (I := I) x0)
        t x0 u v w
  have hterm0 :
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            ((S.family.connection t) (V 0) x0 (frame d x0))) =
        ∑ p : Idx, Γ d a p * N p i j := by
    have hV0 : V 0 = frame a := by
      funext y
      simp [V]
    have hcov :
        (S.family.connection t) (V 0) x0 (frame d x0) =
          ∑ p : Idx, Γ d a p • frame p x0 := by
      rw [hV0]
      simpa [Γ] using
        covariantDerivative_eq_sum_christoffel
          (𝕜 := Real) (I := I) (cov := S.family.connection t)
          (frame := frame) (hframe := hframe) hx0 d a
    have hsum := (nablaA x0).toMultilinearMap.map_update_sum
      (Finset.univ : Finset Idx) (0 : Fin 3)
      (fun p : Idx => Γ d a p • frame p x0)
      (fun b : Fin 3 => V b x0)
    change
      (nablaA x0)
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            (∑ p : Idx, Γ d a p • frame p x0)) =
        ∑ p : Idx,
          (nablaA x0)
            (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
              (Γ d a p • frame p x0)) at hsum
    calc
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            ((S.family.connection t) (V 0) x0 (frame d x0))) =
        nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            (∑ p : Idx, Γ d a p • frame p x0)) := by
          rw [hcov]
      _ = ∑ p : Idx,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
                (Γ d a p • frame p x0)) := by
          simpa only [ContinuousMultilinearMap.map_update_smul,
            Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ = ∑ p : Idx, Γ d a p * N p i j := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [(nablaA x0).map_update_smul]
          have hslot :
              Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3) (frame p x0) =
                DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame p x0) (frame i x0) (frame j x0) := by
            funext q
            fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
          rw [hslot]
          rw [hnabla x0 p i j]
          simp [N, smul_eq_mul]
  have hterm1 :
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            ((S.family.connection t) (V 1) x0 (frame d x0))) =
        ∑ p : Idx, Γ d i p * N a p j := by
    have hV1 : V 1 = frame i := by
      funext y
      simp [V]
    have hcov :
        (S.family.connection t) (V 1) x0 (frame d x0) =
          ∑ p : Idx, Γ d i p • frame p x0 := by
      rw [hV1]
      simpa [Γ] using
        covariantDerivative_eq_sum_christoffel
          (𝕜 := Real) (I := I) (cov := S.family.connection t)
          (frame := frame) (hframe := hframe) hx0 d i
    have hsum := (nablaA x0).toMultilinearMap.map_update_sum
      (Finset.univ : Finset Idx) (1 : Fin 3)
      (fun p : Idx => Γ d i p • frame p x0)
      (fun b : Fin 3 => V b x0)
    change
      (nablaA x0)
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            (∑ p : Idx, Γ d i p • frame p x0)) =
        ∑ p : Idx,
          (nablaA x0)
            (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
              (Γ d i p • frame p x0)) at hsum
    calc
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            ((S.family.connection t) (V 1) x0 (frame d x0))) =
        nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            (∑ p : Idx, Γ d i p • frame p x0)) := by
          rw [hcov]
      _ = ∑ p : Idx,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
                (Γ d i p • frame p x0)) := by
          simpa only [ContinuousMultilinearMap.map_update_smul,
            Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ = ∑ p : Idx, Γ d i p * N a p j := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [(nablaA x0).map_update_smul]
          have hslot :
              Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3) (frame p x0) =
                DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x0) (frame p x0) (frame j x0) := by
            funext q
            fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
          rw [hslot]
          rw [hnabla x0 a p j]
          simp [N, smul_eq_mul]
  have hterm2 :
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            ((S.family.connection t) (V 2) x0 (frame d x0))) =
        ∑ p : Idx, Γ d j p * N a i p := by
    have hV2 : V 2 = frame j := by
      funext y
      simp [V]
    have hcov :
        (S.family.connection t) (V 2) x0 (frame d x0) =
          ∑ p : Idx, Γ d j p • frame p x0 := by
      rw [hV2]
      simpa [Γ] using
        covariantDerivative_eq_sum_christoffel
          (𝕜 := Real) (I := I) (cov := S.family.connection t)
          (frame := frame) (hframe := hframe) hx0 d j
    have hsum := (nablaA x0).toMultilinearMap.map_update_sum
      (Finset.univ : Finset Idx) (2 : Fin 3)
      (fun p : Idx => Γ d j p • frame p x0)
      (fun b : Fin 3 => V b x0)
    change
      (nablaA x0)
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            (∑ p : Idx, Γ d j p • frame p x0)) =
        ∑ p : Idx,
          (nablaA x0)
            (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
              (Γ d j p • frame p x0)) at hsum
    calc
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            ((S.family.connection t) (V 2) x0 (frame d x0))) =
        nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            (∑ p : Idx, Γ d j p • frame p x0)) := by
          rw [hcov]
      _ = ∑ p : Idx,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
                (Γ d j p • frame p x0)) := by
          simpa only [ContinuousMultilinearMap.map_update_smul,
            Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ = ∑ p : Idx, Γ d j p * N a i p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [(nablaA x0).map_update_smul]
          have hslot :
              Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3) (frame p x0) =
                DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x0) (frame i x0) (frame p x0) := by
            funext q
            fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
          rw [hslot]
          rw [hnabla x0 a i p]
          simp [N, smul_eq_mul]
  have hcorr :
      (∑ q : Fin 3,
          nablaA x0
            (Function.update (fun b : Fin 3 => V b x0) q
            ((S.family.connection t) (V q) x0 (frame d x0)))) =
        (∑ p : Idx, Γ d a p * N p i j) +
          (∑ p : Idx, Γ d i p * N a p j) +
            (∑ p : Idx, Γ d j p * N a i p) := by
    rw [Fin.sum_univ_three]
    rw [hterm0, hterm1, hterm2]
  calc
    nabla2A x0
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) (frame d x0) (frame a x0) (frame i x0)
          (frame j x0)) =
        extDerivFun (I := I)
          (fun y : M =>
            nablaRicComp (I := I) S (coordinateFrameAt (I := I) x0)
              t y a i j) x0 (frame d x0) -
          (∑ q : Fin 3,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) q
                ((S.family.connection t) (V q) x0 (frame d x0)))) := heval
    _ = coordNab2Ric (I := I) S x0 t x0 d a i j := by
          rw [coordNab2Ric]
          dsimp [frame, Γ, N]
          rw [hcorr]
          ring



omit [SigmaCompactSpace M] in
theorem coordMetricDeriv
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) :
    forall a b : CoordinateIdx (𝕜 := Real) E,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
        D.carrier D.regular (coordinateFrameSet (I := I) x₀)
        (fun s x =>
          metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
            s x a b)
        (fun t x => (-2 : Real) *
          ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
            t x a b) := by
  intro a b
  apply fixedBaseOnReg_of_timeDerivWithin
  · exact D.regular_subset
  · exact fun {_t} ht => D.regular_mem_nhds ht
  · intro t ht x hx
    exact
      (coordMetricSmoothAt (I := I) S hS x₀ ⟨t, ht⟩ x hx a b).of_le
        (WithTop.coe_le_coe.mpr le_top)
  · intro s hs x hx
    exact coordMetricMdiffOn (I := I) S x₀ s x hx a b
  · intro t ht x hx
    simpa [smul_eq_mul] using
      (coordRicciMdiff (I := I) S x₀ t x hx a b).const_smul (-2 : Real)
  · intro t ht x
    exact
      metricCompInFrame_hasDerivWithinAt
        (I := I) S hS (coordinateFrameAt (I := I) x₀)
        ⟨t, ht⟩ x a b



omit [SigmaCompactSpace M] in
theorem coordMetricMix
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (hmix :
      forall a b : CoordinateIdx (𝕜 := Real) E,
        FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
          D.carrier D.regular (coordinateFrameSet (I := I) x₀)
          (fun s x =>
            metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
              s x a b)
          (fun t x => (-2 : Real) *
            ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
              t x a b)) :
    MetricCovDerivDerivativeComponentsInFrameOnLocal
      (I := I) S (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀)
      (fun t x d a b =>
        (-2 : Real) *
          nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
            t x d a b) := by
  exact metricCovDerivOfMix
    (I := I) S hS (coordinateFrameAt (I := I) x₀)
    (fun t x hx a b => coordRicciMdiff (I := I) S x₀ t x hx a b)
    hmix
    (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
    (coordNablaRealOn (I := I) S x₀)



theorem coordGammaEvol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (fun t x d a b =>
          (-2 : Real) *
            nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
              t x d a b)) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)) := by
  exact gammaEvolLocal
    (I := I) S hS (coordInv (I := I) S x₀)
    (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀)
    (fun t x d a b =>
      (-2 : Real) *
        nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b)
    (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
    (coordInvLocal (I := I) S x₀)
    (coordInvEvol (I := I) S hS x₀)
    hmetric
    (metricCovDerivDerivativeIsRicciFlowInFrame_neg_two
      (M := M)
      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)))



omit [SigmaCompactSpace M] [T2Space M] in
theorem coordGammaForm
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (s : Real) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame
        (S.family.connection s) (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k =
      DifferentialGeometry.Integral.Connection.leviCivitaChristoffelModelRHS
        (I := I) (S.family.metric s) x₀ i j k (extChartAt I x₀ x) := by
  simpa [SolutionOn.family, SolutionFamily.connection] using
    (DifferentialGeometry.Integral.Connection.leviCivitaChristoffelModelRHS_eq_christoffel_of_mem
      (I := I) (g := S.family.metric s) x₀ hx i j k).symm



omit [SigmaCompactSpace M] [T2Space M] in
theorem coordGammaMdiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (s : Real) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        christoffelSymbolInFrame
          (S.family.connection s) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀) y i j k) x := by
  let e := coordinateTrivializationAt (I := I) x₀
  let b := Module.finBasis Real E
  have hcont :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          e.localFrame_coeff I b k y
            ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
                (I := I) (S.family.metric s) (e.localFrame b j) y)
              (e.localFrame b i y))) x := by
    simpa [e, b] using
      DifferentialGeometry.Integral.Connection.lc_christoffel_contMDiffAt
        (I := I) (e := coordinateTrivializationAt (I := I) x₀)
        (b := Module.finBasis Real E) (g := S.family.metric s)
        (x := x) hx i j k
  have hmdiff := hcont.mdifferentiableAt (by simp)
  have heq :
      (fun y : M =>
        christoffelSymbolInFrame
          (S.family.connection s) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀) y i j k)
        =ᶠ[nhds x]
      fun y : M =>
        e.localFrame_coeff I b k y
          ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric s) (e.localFrame b j) y)
            (e.localFrame b i y)) := by
    filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds hx] with y hy
    have hye : y ∈ e.baseSet := by
      simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hy
    have hye' : y ∈ (coordinateTrivializationAt (I := I) x₀).baseSet := by
      simpa [e] using hye
    let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
    have hbasis :
        hframe.toBasisAt hy =
          e.basisAt b hye := by
      ext r
      rw [IsLocalFrameOn.toBasisAt_coe]
      simpa [hframe, e, b, coordinateFrameAt] using
        (Bundle.Trivialization.localFrame_apply_of_mem_baseSet e b
          (i := r) hye)
    simp only [christoffelSymbolInFrame, coordinateFrameAt,
      SolutionOn.family, SolutionFamily.connection, e, b]
    let V : (z : M) -> TangentSpace I z :=
      fun z =>
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
            (I := I) (S.family.metric s) (e.localFrame b j) z)
          (e.localFrame b i z)
    change
      hframe.coeff k y (V y) =
        e.localFrame_coeff I b k y (V y)
    rw [hframe.coeff_apply_of_mem hy V k]
    rw [Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
      (I := I) e b hye V k]
    rw [hbasis]
  exact hmdiff.congr_of_eventuallyEq heq.symm



theorem coordGammaRhsMd
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        christoffelEvolutionRHSInFrame
          (M := M) (coordInv (I := I) S x₀)
          (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
          t y i j k) x := by
  classical
  unfold christoffelEvolutionRHSInFrame
  have hsum :
      MDifferentiableAt I 𝓘(Real, Real)
        (∑ l : CoordinateIdx (𝕜 := Real) E,
          fun y : M =>
            coordInv (I := I) S x₀ t y k l *
              christoffelVariationLoweredRHSInFrame
                (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
                t y i j l) x := by
    refine MDifferentiableAt.sum (𝕜 := Real) (I := I) (M := M) (E' := Real)
      (z := x) (t := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
      (f := fun l y =>
        coordInv (I := I) S x₀ t y k l *
          christoffelVariationLoweredRHSInFrame
            (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
            t y i j l) ?_
    intro l _
    have hg :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => coordInv (I := I) S x₀ t y k l) x :=
      coordInvMdiffOn (I := I) S x₀ t x hx k l
    have h₁ :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M =>
            nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
              t y i j l) x :=
      coordNablaRegOn (I := I) S x₀ t x hx i j l
    have h₂ :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M =>
            nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
              t y j i l) x :=
      coordNablaRegOn (I := I) S x₀ t x hx j i l
    have h₃ :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M =>
            nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)
              t y l i j) x :=
      coordNablaRegOn (I := I) S x₀ t x hx l i j
    simpa [christoffelVariationLoweredRHSInFrame] using
      hg.mul (((h₁.neg).sub h₂).add h₃)
  exact hsum.congr_of_eventuallyEq (by
    filter_upwards with y
    simp [Finset.sum_apply])



omit [SigmaCompactSpace M] in
private theorem coordDgSmAt
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        fderivWithin Real
          (DifferentialGeometry.Integral.Connection.metricFlatModelInChart_component
            (I := I) (S.family.metric p.1) x₀ i j)
          (Set.range I) (extChartAt I x₀ p.2)
          ((Module.finBasis Real E) a))
      ((t : Real), x) := by
  let frame := coordinateFrameAt (I := I) x₀
  let F : Real × M -> Real := fun p =>
    metricCompInFrame (I := I) S frame p.1 p.2 i j
  let X : (y : M) -> TangentSpace I y := frame a
  have hF :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞) F ((t : Real), x) :=
    coordMetricSmoothAt (I := I) S hS x₀ t x hx i j
  have hX :
      ContMDiffAt I (I.prod 𝓘(Real, E))
        (∞ : WithTop ℕ∞) (T% X) x :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx a
  have hD :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun p : Real × M =>
          extDerivFun (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
        ((t : Real), x) :=
    prodExtDerivAt_inf (I := I) (F := F) (X := X) hF hX
  have heq :
      (fun p : Real × M =>
        fderivWithin Real
          (DifferentialGeometry.Integral.Connection.metricFlatModelInChart_component
            (I := I) (S.family.metric p.1) x₀ i j)
          (Set.range I) (extChartAt I x₀ p.2)
          ((Module.finBasis Real E) a))
        =ᶠ[nhds ((t : Real), x)]
      fun p : Real × M =>
        extDerivFun (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2) := by
    have hopen :
        IsOpen {p : Real × M | p.2 ∈ coordinateFrameSet (I := I) x₀} :=
      (coordinateFrameSet_open (I := I) x₀).preimage continuous_snd
    filter_upwards [hopen.mem_nhds hx] with p hp
    have hflat :=
      DifferentialGeometry.Integral.Connection.metricFlatModelInChart_component_deriv_of_mem
        (I := I) (g := S.family.metric p.1) x₀ hp a i j
    simpa [F, X, frame, metricCompInFrame, DifferentialGeometry.Integral.Connection.directionalDeriv] using hflat
  exact hD.congr_of_eventuallyEq heq



private theorem gammaRhsSm
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        DifferentialGeometry.Integral.Connection.leviCivitaChristoffelModelRHS
          (I := I) (S.family.metric p.1) x₀ i j k (extChartAt I x₀ p.2))
      ((t : Real), x) := by
  classical
  unfold DifferentialGeometry.Integral.Connection.leviCivitaChristoffelModelRHS
  refine contMDiffAt_const.mul ?_
  refine ContMDiffAt.sum fun l _ => ?_
  have hInv :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          coordInv (I := I) S x₀ p.1 p.2 k l) ((t : Real), x) :=
    coordInvSmoothAt (I := I) S hS x₀ t x hx k l
  have hInv' :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          (Module.finBasis Real E).coord k
            ((ContinuousLinearMap.inverse
                (DifferentialGeometry.Integral.Connection.metricFlatModelInChart
                  (I := I) (S.family.metric p.1) x₀
                  (extChartAt I x₀ p.2)))
              (LinearMap.toContinuousLinearMap
                ((Module.finBasis Real E).coord l)))) ((t : Real), x) := by
    simpa [coordInv] using hInv
  have h₁ := coordDgSmAt (I := I) S hS x₀ t x hx i j l
  have h₂ := coordDgSmAt (I := I) S hS x₀ t x hx j i l
  have h₃ := coordDgSmAt (I := I) S hS x₀ t x hx l i j
  exact hInv'.mul ((h₁.add h₂).sub h₃)







theorem coordGammaSmoothInf
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        christoffelSymbolInFrame
          (S.family.connection p.1) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀) p.2 i j k)
      ((t : Real), x) := by
  have hmodel := gammaRhsSm (I := I) S hS x₀ t x hx i j k
  have heq :
      (fun p : Real × M =>
        christoffelSymbolInFrame
          (S.family.connection p.1) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀) p.2 i j k)
        =ᶠ[nhds ((t : Real), x)]
      fun p : Real × M =>
        DifferentialGeometry.Integral.Connection.leviCivitaChristoffelModelRHS
          (I := I) (S.family.metric p.1) x₀ i j k (extChartAt I x₀ p.2) := by
    have hopen :
        IsOpen {p : Real × M | p.2 ∈ coordinateFrameSet (I := I) x₀} :=
      (coordinateFrameSet_open (I := I) x₀).preimage continuous_snd
    filter_upwards [hopen.mem_nhds hx] with p hp
    exact coordGammaForm (I := I) S x₀ p.1 hp i j k
  exact hmodel.congr_of_eventuallyEq heq


theorem coordGammaSmoothAt
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
      (fun p : Real × M =>
        christoffelSymbolInFrame
          (S.family.connection p.1) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀) p.2 i j k)
      ((t : Real), x) := by
  exact (coordGammaSmoothInf (I := I) S hS x₀ t x hx i j k).of_le
    (WithTop.coe_le_coe.mpr le_top)



theorem coordGammaMix
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (hGamma :
      ChristoffelEvolutionEquationInFrameOn
        (I := I) S (coordInv (I := I) S x₀)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))) :
    ChristoffelVariationMixedDerivativeInFrameOnRegular
      (I := I) S (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (christoffelEvolutionRHSInFrame
        (M := M) (coordInv (I := I) S x₀)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))) := by
  intro i j k
  refine fixedBaseOnRegLocal
    (I := I) (timeSet := D.carrier) (regularSet := D.regular)
    (u := coordinateFrameSet (I := I) x₀)
    (F := fun s x =>
      christoffelSymbolInFrame
        (S.family.connection s) (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k)
    (Ft := fun t x =>
      christoffelEvolutionRHSInFrame
        (M := M) (coordInv (I := I) S x₀)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
        t x i j k)
    (coordinateFrameSet_open (I := I) x₀) D.regular_subset
    (fun {_t} ht => D.regular_mem_nhds ht) ?_ ?_ ?_ ?_
  · intro t ht x hx
    exact coordGammaSmoothAt (I := I) S hS x₀ ⟨t, ht⟩ x hx i j k
  · intro s _hs x hx
    exact coordGammaMdiff (I := I) S x₀ s x hx i j k
  · intro t _ht x hx
    exact coordGammaRhsMd (I := I) S x₀ t x hx i j k
  · intro t ht x hx
    exact hGamma ⟨t, ht⟩ x hx i j k



theorem coordNab2At
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (d a i j : CoordinateIdx (𝕜 := Real) E) :
    coordNab2Ric (I := I) S x₀ t x₀ d a i j =
      ricciSecondCovDerivCompInFrame
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
        t x₀ d a i j := by
  rfl



theorem coordNab2On
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) :
    Nabla2RicciComponentsByConnectionInFrameOn
      (I := I) S (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
      (coordNab2Ric (I := I) S x₀) := by
  intro t x _hx d a i j
  rfl

end CoordinateFrameRicciEvolution

end Components

end DifferentialGeometry.PDE.RicciFlow
