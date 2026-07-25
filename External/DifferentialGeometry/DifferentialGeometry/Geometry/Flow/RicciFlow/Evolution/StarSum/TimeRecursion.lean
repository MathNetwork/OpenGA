import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.SpatialMember
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq

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

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}






omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRicReal_frame
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M} {u : Set M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (frame : Idx → (y : M) → TangentSpace I y)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) (hx : x ∈ u)
    (d a b : Idx) :
    nablaRicComp (I := I) S frame t x d a b = ricciCovDerivCompInFrame (I := I) S frame t x d a b := by
  classical
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) hcov (S.ricci t)
  let V : Fin 2 → (y : M) → TangentSpace I y :=
    fun q y => if q = 0 then frame a y else frame b y
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (frame d x)).choose
  have hX : X x = frame d x :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (frame d x)).choose_spec
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        x :=
    hframe.contMDiffAt hu hx r
  have hV_at : ∀ q : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _)))
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
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec2]
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
        nablaRicComp (I := I) S frame t x d a b := by
    simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection]
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
      fin_cases q <;> simp [Function.update, V, DifferentialGeometry.Integral.Connection.vec2]
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
      fin_cases q <;> simp [Function.update, V, DifferentialGeometry.Integral.Connection.vec2]
    rw [harg]
    simp [SolutionOn.ricciAt_eq]
  rw [hleft, hfun] at heval
  rw [Fin.sum_univ_two, hterm0, hterm1] at heval
  simpa [ricciCovDerivCompInFrame, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    using heval














omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem ricciCovDeriv_trace_nablaRm
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M} {u : Set M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (frame : Idx → (y : M) → TangentSpace I y)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) (hx : x ∈ u)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hbasis : ∀ i, frame i x = basis i)
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (d a b : Idx) :
    ricciCovDerivCompInFrame (I := I) S frame t x d a b
      = ∑ e : Idx, nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) (frame d x) (frame e x) (frame a x) (frame b x) (frame e x)) := by
  classical

  have hcollapse : ∀ f : Idx → Idx → Real,
      (∑ i : Idx, ∑ j : Idx, identityInvMetric i j * f i j) = ∑ e : Idx, f e e := by
    intro f
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro j _ hj
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hj h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

  have hk : ∀ e : Idx,
      nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) (frame d x) (frame e x) (frame a x) (frame b x) (frame e x))
        = totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            4 (S.family.connection t) (S.base.rm04 t) x
            (vec5 (I := I) (frame d x) (frame e x) (frame a x) (frame b x) (frame e x)) := by
    intro e
    rw [nablaKRm04Field_succ, totalNabla0S_apply, nablaKRm04Field_zero]

  rw [← nablaRicReal_frame S t frame hframe hu hx d a b, nablaRicComp_apply]
  simp_rw [hk]

  simp only [hbasis]

  have hinv :=
    metricInverseInBasis_identity_of_orthonormal (I := I) (S.family.metric t) basis horth
  have heq :=
    (canBianchiCore (I := I) (S.family.metric t) basis identityInvMetric hinv).2.2
      (frame d x) (frame a x) (frame b x)
  simp only [hbasis] at heq
  exact heq.trans
    (hcollapse fun i j => totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (S.base.rm04 t) x
      (vec5 (I := I) (basis d) (basis i) (basis a) (basis b) (basis j)))

























def lfBase
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Fin 3 → (y : M) → TangentSpace I y) :
    Real → M → (Fin 4 → Fin 3) → Real :=
  fun s => frameComp0S (I := I) (S.base.rm04 s) frame




def lfChr
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Fin 3 → (y : M) → TangentSpace I y) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) :
    Real → M → Fin 3 → Fin 3 → Fin 3 → Real :=
  fun s y =>
    christoffelSymbolInFrame (S.family.connection s) frame hframe y






omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem traceOrthoEq
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M) {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s → TangentSpace I x) :
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Idx)) T tail
      = metricTraceFirstTwo0STensor (I := I) g T tail := by
  rw [metricTrace0S2TensorInBasis_apply, metricTraceFirstTwo0STensor_apply]
  exact metricTrace0S2InBasis_eq_metricTrace (I := I) g basis (identityInvMetric (Idx := Idx))
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) T tail

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in


def gammaStarCost (k : ℕ) : Real :=
  9 * (12 + 3 * k)









omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
private theorem gammaStarU
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {u : Set M}
    (frame : Fin 3 → (y : M) → TangentSpace I y)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    (horthU : ∀ y : M, y ∈ u → ∀ i j : Fin 3,
      (S.base.metric t).inner y (frame i y) (frame j y) = if i = j then (1 : Real) else 0)
    (chrDt : Real → M → Fin 3 → Fin 3 → Fin 3 → Real)
    (hchrIdU : ∀ y : M, y ∈ u → ∀ i j p : Fin 3,
      chrDt t y i j p =
        - ricciCovDerivCompInFrame (I := I) S frame t y i j p
        - ricciCovDerivCompInFrame (I := I) S frame t y j i p
        + ricciCovDerivCompInFrame (I := I) S frame t y p i j) :
    ∃ Tgamma : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + (k + 1)),
      StarSum2Cost (I := I) (Fin 3) S t (k + 1) Tgamma (gammaStarCost k) ∧
      ∀ (y : M), y ∈ u → ∀ I0 : Fin (4 + (k + 1)) → Fin 3,
        covDerivStepDt (chrDt t y)
            (fun m : Fin (4 + k) → Fin 3 =>
              nablaKRm04Field (I := I) S t k y (fun q => frame (m q) y)) I0
          = tensor0SComponent (I := I) (Tgamma y) (fun i => frame i y) I0 := by
  classical
  let TA := ∑ q : Fin (4 + k), starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic1 k q)
  let TB := ∑ q : Fin (4 + k), starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic2 k q)
  let TC := ∑ q : Fin (4 + k), starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic3 k q)
  refine ⟨(-1 : Real) • TA + (-1 : Real) • TB + TC, ?_, ?_⟩
  · have hTA : StarSum2Cost (I := I) (Fin 3) S t (k + 1) TA
        (∑ _q : Fin (4 + k), (9 : Real)) := by
      dsimp only [TA]
      refine starSum2Cost_sum (I := I) (Idx := Fin 3) (S := S) (t := t) Finset.univ
        (fun q => starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic1 k q))
        (fun _q => 9) ?_
      intro q _
      convert StarSum2Cost.base (I := I) (Idx := Fin 3) (k + 1) 1 k 0 (sigmaRic1 k q) using 1
      norm_num
    have hTB : StarSum2Cost (I := I) (Fin 3) S t (k + 1) TB
        (∑ _q : Fin (4 + k), (9 : Real)) := by
      dsimp only [TB]
      refine starSum2Cost_sum (I := I) (Idx := Fin 3) (S := S) (t := t) Finset.univ
        (fun q => starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic2 k q))
        (fun _q => 9) ?_
      intro q _
      convert StarSum2Cost.base (I := I) (Idx := Fin 3) (k + 1) 1 k 0 (sigmaRic2 k q) using 1
      norm_num
    have hTC : StarSum2Cost (I := I) (Fin 3) S t (k + 1) TC
        (∑ _q : Fin (4 + k), (9 : Real)) := by
      dsimp only [TC]
      refine starSum2Cost_sum (I := I) (Idx := Fin 3) (S := S) (t := t) Finset.univ
        (fun q => starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic3 k q))
        (fun _q => 9) ?_
      intro q _
      convert StarSum2Cost.base (I := I) (Idx := Fin 3) (k + 1) 1 k 0 (sigmaRic3 k q) using 1
      norm_num
    convert ((hTA.smul (-1)).add (hTB.smul (-1))).add hTC using 1
    simp only [abs_neg, abs_one, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, gammaStarCost]
    push_cast
    ring
  · intro y hy I0
    have hbasis_y : ∀ i : Fin 3, frame i y = (hframe.toBasisAt hy) i :=
      fun i => (hframe.toBasisAt_coe hy i).symm
    have horth_y : ∀ i j : Fin 3,
        (S.family.metric t).inner y ((hframe.toBasisAt hy) i) ((hframe.toBasisAt hy) j)
          = if i = j then (1 : Real) else 0 := by
      intro i j
      rw [← hbasis_y i, ← hbasis_y j, SolutionOn.family_metric]
      exact horthU y hy i j
    have hbridge_y : ∀ d a b : Fin 3,
        ricciCovDerivCompInFrame (I := I) S frame t y d a b
          = ∑ e : Fin 3, nablaKRm04Field (I := I) S t 1 y
              (vec5 (I := I) (frame d y) (frame e y) (frame a y) (frame b y) (frame e y)) :=
      fun d a b =>
        ricciCovDeriv_trace_nablaRm (I := I) S t frame hframe hu hy
          (hframe.toBasisAt hy) hbasis_y horth_y d a b
    have hLHS_y : ∀ I0' : Fin (4 + (k + 1)) → Fin 3,
        covDerivStepDt (chrDt t y)
            (fun m : Fin (4 + k) → Fin 3 =>
              nablaKRm04Field (I := I) S t k y (fun q => (hframe.toBasisAt hy) (m q))) I0'
          = ∑ s : Fin (4 + k), ∑ p : Fin 3,
              (( - ∑ e : Fin 3, nablaKRm04Field (I := I) S t 1 y
                    (vec5 (I := I) (frame (I0' 0) y) (frame e y)
                      (frame (Fin.tail I0' s) y) (frame p y) (frame e y)))
               - (∑ e : Fin 3, nablaKRm04Field (I := I) S t 1 y
                    (vec5 (I := I) (frame (Fin.tail I0' s) y) (frame e y)
                      (frame (I0' 0) y) (frame p y) (frame e y)))
               + (∑ e : Fin 3, nablaKRm04Field (I := I) S t 1 y
                    (vec5 (I := I) (frame p y) (frame e y)
                      (frame (I0' 0) y) (frame (Fin.tail I0' s) y) (frame e y))))
              * nablaKRm04Field (I := I) S t k y
                  (fun q => (hframe.toBasisAt hy) (Function.update (Fin.tail I0') s p q)) := by
      intro I0'
      simp only [covDerivStepDt]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => ?_
      rw [hchrIdU y hy (I0' 0) (Fin.tail I0' s) p,
        hbridge_y (I0' 0) (Fin.tail I0' s) p,
        hbridge_y (Fin.tail I0' s) (I0' 0) p,
        hbridge_y p (I0' 0) (Fin.tail I0' s)]
    simp only [hbasis_y]
    rw [hLHS_y I0]
    have hDeq : ∀ (s : Fin (4 + k)) (p : Fin 3),
        (fun q' : Fin (4 + k) => (hframe.toBasisAt hy) (Function.update (Fin.tail I0) s p q')) =
          Function.update (fun p' : Fin (4 + k) => (hframe.toBasisAt hy) (I0 p'.succ)) s
            ((hframe.toBasisAt hy) p) := by
      intro s p
      funext q'
      rw [Function.update_apply, Function.update_apply]
      rcases eq_or_ne q' s with h | h
      · simp [h]
      · simp [h, Fin.tail]
    have hTAp : (TA y) (fun p => (hframe.toBasisAt hy) (I0 p)) =
        ∑ q : Fin (4 + k),
          (starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic1 k q) y)
            (fun p => (hframe.toBasisAt hy) (I0 p)) := by
      dsimp only [TA]
      let Sset : Finset (Fin (4 + k)) := Finset.univ
      change (((∑ q ∈ Sset,
          starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic1 k q)) :
          Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (4 + (k + 1))) y) (fun p => (hframe.toBasisAt hy) (I0 p)) =
        ∑ q ∈ Sset,
          (starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic1 k q) y)
            (fun p => (hframe.toBasisAt hy) (I0 p))
      induction Sset using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
          rw [ih]
    have hTBp : (TB y) (fun p => (hframe.toBasisAt hy) (I0 p)) =
        ∑ q : Fin (4 + k),
          (starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic2 k q) y)
            (fun p => (hframe.toBasisAt hy) (I0 p)) := by
      dsimp only [TB]
      let Sset : Finset (Fin (4 + k)) := Finset.univ
      change (((∑ q ∈ Sset,
          starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic2 k q)) :
          Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (4 + (k + 1))) y) (fun p => (hframe.toBasisAt hy) (I0 p)) =
        ∑ q ∈ Sset,
          (starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic2 k q) y)
            (fun p => (hframe.toBasisAt hy) (I0 p))
      induction Sset using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
          rw [ih]
    have hTCp : (TC y) (fun p => (hframe.toBasisAt hy) (I0 p)) =
        ∑ q : Fin (4 + k),
          (starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic3 k q) y)
            (fun p => (hframe.toBasisAt hy) (I0 p)) := by
      dsimp only [TC]
      let Sset : Finset (Fin (4 + k)) := Finset.univ
      change (((∑ q ∈ Sset,
          starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic3 k q)) :
          Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (4 + (k + 1))) y) (fun p => (hframe.toBasisAt hy) (I0 p)) =
        ∑ q ∈ Sset,
          (starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic3 k q) y)
            (fun p => (hframe.toBasisAt hy) (I0 p))
      induction Sset using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
          rw [ih]
    simp only [tensor0SComponent_apply, ContMDiffSection.coe_add, Pi.add_apply,
      Tensor0SSpace.add_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SSpace.smul_apply, hTAp, hTBp, hTCp]
    rw [Finset.smul_sum, Finset.smul_sum]
    simp only [neg_one_smul]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [slotRic1 (I := I) S t k s (hframe.toBasisAt hy) horth_y I0,
      slotRic2 (I := I) S t k s (hframe.toBasisAt hy) horth_y I0,
      slotRic3 (I := I) S t k s (hframe.toBasisAt hy) horth_y I0]
    simp only [hbasis_y, hDeq, Finset.sum_mul, sub_mul, add_mul, neg_mul,
      ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [show Fin.tail I0 s = I0 s.succ from rfl]
    ring



omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem frameExtGerm {Idx : Type*} {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    {A1 A2 : M → (Fin r → Idx) → Real} {y : M}
    (hfield : A1 =ᶠ[nhds y] A2) :
    frameExtData (I := I) frame A1 y = frameExtData (I := I) frame A2 y := by
  funext m d
  simp only [frameExtData]
  exact extDerivFun_eventuallyEq_congr (I := I) (frame d y) (hfield.mono fun z hz => congrFun hz m)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in



def resStarCost : ℕ → Real
  | 0 => 108
  | k + 1 => 2 * resStarCost k + commStarCost 3 k + gammaStarCost k

open DifferentialGeometry.Dim3Reaction in









omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem resStarLFU
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D)
    {u : Set M}
    (frame : Fin 3 → (y : M) → TangentSpace I y)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (hdim : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3)
    (horthU : ∀ y : M, y ∈ u → ∀ i j : Fin 3,
      (S.base.metric (t : Real)).inner y (frame i y) (frame j y) = if i = j then (1 : Real) else 0)


    (hbase : ∀ (y : M) (bas : Module.Basis (Fin 3) Real (TangentSpace I y))
        (_horth : ∀ i j : Fin 3,
          (S.base.metric (t : Real)).inner y (bas i) (bas j) = if i = j then (1 : Real) else 0)
        (I0 : Fin 4 → Fin 3),
        HasDerivWithinAt
          (fun r : Real => S.base.rm04 r y (fun p => bas (I0 p)))
          (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) bas (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : Real) 2 y)) (fun i => bas i) I0
            + (-2 * (Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 1) (I0 2) (I0 3)
                    - Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 1) (I0 3) (I0 2)
                    + Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 2) (I0 1) (I0 3)
                    - Bt (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 3) (I0 1) (I0 2))
                - drift (fun i j => S.ricciAt (t : Real) y (vec2 (I := I) (bas i) (bas j)))
                      (I0 0) (I0 1) (I0 2) (I0 3)))
          D.carrier (t : Real))


    (baseDt : Real → M → (Fin 4 → Fin 3) → Real)
    (chrDt : Real → M → Fin 3 → Fin 3 → Fin 3 → Real)
    (hrm : ∀ (y : M), y ∈ u → ∀ m : Fin 4 → Fin 3,
      HasDerivWithinAt (fun s : Real => lfBase (I := I) S frame s y m)
        (baseDt (t : Real) y m) D.carrier (t : Real))
    (hchr : ∀ (y : M), y ∈ u → ∀ i a p : Fin 3,
      HasDerivWithinAt (fun s : Real => lfChr (I := I) S frame hframe s y i a p)
        (chrDt (t : Real) y i a p) D.carrier (t : Real))




    (hchrId : ∀ (y : M), y ∈ u → ∀ i j p : Fin 3,
      chrDt (t : Real) y i j p =
        - ricciCovDerivCompInFrame (I := I) S frame (t : Real) y i j p
        - ricciCovDerivCompInFrame (I := I) S frame (t : Real) y j i p
        + ricciCovDerivCompInFrame (I := I) S frame (t : Real) y p i j)
    (hswap : ∀ (y : M), y ∈ u → ∀ (k' : ℕ) (d : Fin 3) (m : Fin (4 + k') → Fin 3),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun z : M =>
              iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe) (lfBase (I := I) S frame)
                k' s z m) y (frame d y))
        (extDerivFun (I := I)
          (fun z : M =>
            iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
              (lfBase (I := I) S frame) baseDt k' (t : Real) z m) y (frame d y))
        D.carrier (t : Real)) :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k),
      StarSum2Cost (I := I) (Fin 3) S (t : Real) k T (resStarCost k) ∧
      ∀ (y : M) (hy : y ∈ u) (I0 : Fin (4 + k) → Fin 3),
        HasDerivWithinAt
          (fun r : Real =>
            tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k y) (fun i => frame i y) I0)
          (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : Real) (k + 2) y) + T y)
            (fun i => frame i y) I0)
          D.carrier (t : Real) := by
  classical
  induction k with
  | zero =>

      refine ⟨e0Field (I := I) S (t : Real), ?_, fun y hy I0 => ?_⟩
      · simpa [resStarCost] using e0Field_cost (I := I) S (t : Real)
      obtain ⟨_, _, hcomp⟩ := residualStarSum_zero (I := I) S t hdim hbase

      have horthy : ∀ i j : Fin 3,
          (S.base.metric (t : Real)).inner y ((hframe.toBasisAt hy) i) ((hframe.toBasisAt hy) j)
            = if i = j then (1 : Real) else 0 := by
        intro i j
        rw [hframe.toBasisAt_coe hy i, hframe.toBasisAt_coe hy j]
        exact horthU y hy i j
      have hb := hcomp y (hframe.toBasisAt hy) horthy I0
      simpa only [hframe.toBasisAt_coe hy] using hb
  | succ k _ih =>

      obtain ⟨Tk, hTk, hIH⟩ := _ih

      obtain ⟨Tcomm, hTcomm, hcomm⟩ := spatialCommStarSum (I := I) S hS t k (Idx := Fin 3)
      obtain ⟨Tgamma, hTgamma, hgamma⟩ :=
        gammaStarU (I := I) S (t : Real) k frame hframe hu horthU chrDt hchrId

      refine ⟨stNabla (I := I) S (t : Real) Tk + (-1 : Real) • Tcomm + (-1 : Real) • Tgamma, ?_, ?_⟩
      · convert ((hTk.nabla).add (hTcomm.smul (-1))).add (hTgamma.smul (-1)) using 1
        simp only [abs_neg, abs_one, one_mul, Fintype.card_fin, resStarCost]
      · intro y hy I0

        have hLHSfun : (fun r : Real =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r (k + 1) y) (fun i => frame i y) I0)
            = (fun s : Real =>
              iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe) (lfBase (I := I) S frame)
                (k + 1) s y I0) := by
          funext s
          rw [show iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe)
                (lfBase (I := I) S frame) (k + 1) s y I0
              = nablaKRm04Field (I := I) S s (k + 1) y (frameTuple (I := I) frame y I0) from
            iterRmLF_eq_nabla (I := I) S s frame hframe hu (k + 1) hy I0]
          rfl

        have hderiv :=
          iteratedRmComp_hasDerivWithinAt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
            (lfBase (I := I) S frame) baseDt y (hrm y hy) (hchr y hy) (hswap y hy) (k + 1) I0
        rw [hLHSfun]

        have hval :
            tensor0SComponent (I := I)
                (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                    (identityInvMetric (Idx := Fin 3))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 1 + 2) y)
                  + (stNabla (I := I) S (t : Real) Tk
                      + (-1 : Real) • Tcomm + (-1 : Real) • Tgamma) y)
                (fun i => frame i y) I0
              = iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
                  (lfBase (I := I) S frame) baseDt (k + 1) (t : Real) y I0 := by
          have hmem : D.carrier ∈ nhds (t : Real) := D.regular_mem_nhds t.2


          have hfieldU : ∀ z, z ∈ u →
              (fun m : Fin (4 + k) → Fin 3 =>
                iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
                  (lfBase (I := I) S frame) baseDt k (t : Real) z m)
                = frameComp0S (I := I)
                    (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                        (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk) frame z := by
            intro z hz
            funext m
            have hfun_z : (fun s : Real =>
                  iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe)
                    (lfBase (I := I) S frame) k s z m)
                = (fun r : Real =>
                  tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k z)
                    (fun i => frame i z) m) := by
              funext s
              rw [show iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe)
                    (lfBase (I := I) S frame) k s z m
                  = nablaKRm04Field (I := I) S s k z (frameTuple (I := I) frame z m) from
                  iterRmLF_eq_nabla (I := I) S s frame hframe hu k hz m]
              rfl
            have hd1 := iteratedRmComp_hasDerivWithinAt (I := I) frame
              (lfChr (I := I) S frame hframe) chrDt (lfBase (I := I) S frame) baseDt z
              (hrm z hz) (hchr z hz) (hswap z hz) k m
            rw [hfun_z] at hd1
            have huniq := (hd1.hasDerivAt hmem).unique ((hIH z hz m).hasDerivAt hmem)
            have horth_z : ∀ i j : Fin 3,
                (S.base.metric (t : Real)).inner z ((hframe.toBasisAt hz) i) ((hframe.toBasisAt hz) j)
                  = if i = j then (1 : Real) else 0 := by
              intro i j
              rw [hframe.toBasisAt_coe hz i, hframe.toBasisAt_coe hz j]
              exact horthU z hz i j
            rw [huniq, frameComp0S_apply]
            simp only [tensor0SComponent_apply, Tensor0SSpace.add_apply,
              ContMDiffSection.coe_add, Pi.add_apply, metricTraceFirstTwoField_apply]
            rw [traceOrthoEq (I := I) (S.base.metric (t : Real)) (hframe.toBasisAt hz) horth_z
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) z) (fun a => frame (m a) z)]

          have horth_y : ∀ i j : Fin 3,
              (S.base.metric (t : Real)).inner y ((hframe.toBasisAt hy) i) ((hframe.toBasisAt hy) j)
                = if i = j then (1 : Real) else 0 := by
            intro i j
            rw [hframe.toBasisAt_coe hy i, hframe.toBasisAt_coe hy j]
            exact horthU y hy i j

          have hgam : covDerivStepDt (chrDt (t : Real) y)
                (iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe)
                  (lfBase (I := I) S frame) k (t : Real) y) I0
              = tensor0SComponent (I := I) (Tgamma y) (fun i => frame i y) I0 := by
            have hiter : (iteratedRmComp (I := I) frame (lfChr (I := I) S frame hframe)
                  (lfBase (I := I) S frame) k (t : Real) y)
                = (fun m : Fin (4 + k) → Fin 3 =>
                    nablaKRm04Field (I := I) S (t : Real) k y (fun q => frame (m q) y)) := by
              funext m
              exact iterRmLF_eq_nabla (I := I) S (t : Real) frame hframe hu k hy m
            rw [hiter]
            exact hgamma y hy I0

          have hExtEq : (fun z : M =>
                iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
                  (lfBase (I := I) S frame) baseDt k (t : Real) z)
              =ᶠ[nhds y] frameComp0S (I := I)
                  (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                      (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk) frame := by
            filter_upwards [hu.mem_nhds hy] with z hz
            exact hfieldU z hz

          have hcs : covDerivStepComp
                (frameExtData (I := I) frame
                  (fun z : M => iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe)
                    chrDt (lfBase (I := I) S frame) baseDt k (t : Real) z) y)
                (lfChr (I := I) S frame hframe (t : Real) y)
                (iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
                  (lfBase (I := I) S frame) baseDt k (t : Real) y) I0
              = tensor0SComponent (I := I)
                  (stNabla (I := I) S (t : Real)
                    (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                        (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk) y)
                  (fun i => frame i y) I0 := by
            rw [frameExtGerm (I := I) frame hExtEq,
              show (iteratedRmCompDt (I := I) frame (lfChr (I := I) S frame hframe) chrDt
                    (lfBase (I := I) S frame) baseDt k (t : Real) y)
                  = frameComp0S (I := I)
                      (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                          (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk) frame y from
                hfieldU y hy]
            exact covDerivStepComp_frameComp_eq (I := I) (S.family.connection (t : Real))
              (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk)
              (stNabla (I := I) S (t : Real)
                (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk))
              (stNabla_realizes (I := I) S (t : Real) _) frame hframe hu hy I0

          have hsplit : tensor0SComponent (I := I)
                (stNabla (I := I) S (t : Real)
                  (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                      (nablaKRm04Field (I := I) S (t : Real) (k + 2)) + Tk) y)
                (fun i => frame i y) I0
              = tensor0SComponent (I := I)
                  (stNabla (I := I) S (t : Real)
                    (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                        (nablaKRm04Field (I := I) S (t : Real) (k + 2))) y)
                  (fun i => frame i y) I0
                + tensor0SComponent (I := I) (stNabla (I := I) S (t : Real) Tk y)
                    (fun i => frame i y) I0 := by
            rw [stNabla_add]
            simp [tensor0SComponent_apply]

          have hc' : tensor0SComponent (I := I)
                (metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 3) y)) (fun i => frame i y) I0
              - tensor0SComponent (I := I)
                (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k)
                  (S.family.connection (t : Real))
                  (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 2))) y) (fun i => frame i y) I0
              = tensor0SComponent (I := I) (Tcomm y) (fun i => frame i y) I0 := by
            have hc := hcomm y (hframe.toBasisAt hy) (identityInvMetric (Idx := Fin 3))
              (metricInverseInBasis_identity_of_orthonormal (I := I) (S.base.metric (t : Real))
                (hframe.toBasisAt hy) horth_y) horth_y I0
            simpa only [tensor0SComponent_apply, hframe.toBasisAt_coe hy] using hc

          have htrace : tensor0SComponent (I := I)
                (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                  (identityInvMetric (Idx := Fin 3))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 1 + 2) y)) (fun i => frame i y) I0
              = tensor0SComponent (I := I)
                (metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 3) y)) (fun i => frame i y) I0 := by
            simp only [tensor0SComponent_apply]
            exact traceOrthoEq (I := I) (S.base.metric (t : Real)) (hframe.toBasisAt hy) horth_y
              (nablaKRm04Field (I := I) S (t : Real) (k + 1 + 2) y) (fun a => frame (I0 a) y)

          have hLHS : tensor0SComponent (I := I)
                (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                    (identityInvMetric (Idx := Fin 3))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 1 + 2) y)
                  + (stNabla (I := I) S (t : Real) Tk + (-1 : Real) • Tcomm
                      + (-1 : Real) • Tgamma) y)
                (fun i => frame i y) I0
              = tensor0SComponent (I := I)
                    (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                      (identityInvMetric (Idx := Fin 3))
                      (nablaKRm04Field (I := I) S (t : Real) (k + 1 + 2) y))
                    (fun i => frame i y) I0
                + tensor0SComponent (I := I) (stNabla (I := I) S (t : Real) Tk y)
                    (fun i => frame i y) I0
                + (-1 : Real) * tensor0SComponent (I := I) (Tcomm y) (fun i => frame i y) I0
                + (-1 : Real) * tensor0SComponent (I := I) (Tgamma y) (fun i => frame i y) I0 := by
            simp only [tensor0SComponent_apply]
            simp
            ring

          have hMfeval : tensor0SComponent (I := I)
                (stNabla (I := I) S (t : Real)
                  (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 2))) y) (fun i => frame i y) I0
              = tensor0SComponent (I := I)
                (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k)
                  (S.family.connection (t : Real))
                  (metricTraceFirstTwoField (I := I) (S.base.metric (t : Real))
                    (nablaKRm04Field (I := I) S (t : Real) (k + 2))) y) (fun i => frame i y) I0 := rfl


          rw [hLHS, htrace, iteratedRmCompDt_succ, Pi.sub_apply, hcs, hgam, hsplit, hMfeval]
          linarith [hc']
        rw [hval]
        exact hderiv

end DifferentialGeometry.PDE.RicciFlow
