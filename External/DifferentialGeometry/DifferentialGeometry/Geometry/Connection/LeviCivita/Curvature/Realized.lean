import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Topology Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]
















omit [I.Boundaryless] in
omit [IsManifold I 1 M] in
omit [SigmaCompactSpace M] in
theorem canScalTrace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let scalar : M -> Real :=
      fun y => metricTracePair0SAt (I := I) g (Ric y)
    let nablaRic :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric x
    let dScalar := differential1FormFun (I := I) scalar x
    DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
  classical
  dsimp [DScalarTraceAt]
  intro X
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let scalar : M -> Real :=
    fun y => metricTracePair0SAt (I := I) g (Ric y)
  let nablaRic :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric x
  let dScalar := differential1FormFun (I := I) scalar x
  simpa [cov, hcov, Ric, scalar, nablaRic, dScalar] using
    nablaTrace02 (I := I) (M := M) cov g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      Ric basis gInv hinv X


theorem canScalHess
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (i j : Idx) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let nablaRic :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov hcov Ric)
    let nabla2Ric :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaRic x
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * nabla2Ric (vec4 (I := I) (basis i) (basis j)
          (basis k) (basis l))) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * nabla2Ric (vec4 (I := I) (basis j) (basis i)
          (basis k) (basis l)) := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (1 : WithTop ℕ∞) := by
    simpa [cov] using
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) g)
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let scalar : M -> Real := fun y => metricTracePair0SAt (I := I) g (Ric y)
  let hscalar : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) scalar :=
    trace02_smooth (I := I) g Ric
  let Hess := hessianSec (I := I) cov hcov scalar hscalar
  let nablaRic :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        2 cov hcov Ric)
  let nabla2Ric :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov nablaRic x
  have hleft :=
    nabla2Trace02 (I := I) (M := M) cov hcov hcov1 g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      Ric basis gInv hinv (basis i) (basis j)
  have hright :=
    nabla2Trace02 (I := I) (M := M) cov hcov hcov1 g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      Ric basis gInv hinv (basis j) (basis i)
  have hsymm :=
    DifferentialGeometry.Integral.Connection.hessSymm (I := I) (M := M) g scalar hscalar (basis i) (basis j)
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * nabla2Ric (vec4 (I := I) (basis i) (basis j)
          (basis k) (basis l)))
        =
      Hess x (vec2 (I := I) (basis i) (basis j)) := by
        simpa [cov, hcov, hcov1, Ric, scalar, hscalar, Hess, nablaRic, nabla2Ric]
          using hleft.symm
    _ =
      Hess x (vec2 (I := I) (basis j) (basis i)) := by
        simpa [cov, hcov, hcov1, Ric, scalar, hscalar, Hess] using hsymm
    _ =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * nabla2Ric (vec4 (I := I) (basis j) (basis i)
          (basis k) (basis l)) := by
        simpa [cov, hcov, hcov1, Ric, scalar, hscalar, Hess, nablaRic, nabla2Ric]
          using hright

private theorem update_comp_perm {s : ℕ} {β : Type*}
    (σ : Equiv.Perm (Fin s)) (base : Fin s -> β) (a : Fin s) (u : β) :
    (fun q : Fin s => Function.update base a u (σ q)) =
      Function.update (fun q : Fin s => base (σ q)) (σ.symm a) u := by
  funext q
  by_cases hq : q = σ.symm a
  · subst q
    rw [Equiv.apply_symm_apply]
    simp
  · have hne : σ q ≠ a := by
      intro h
      apply hq
      exact σ.injective (by simpa using h)
    simp [Function.update, hq, hne]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0S_update_zero {s : ℕ} {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> TangentSpace I x) (a : Fin s) :
    A (Function.update slots a 0) = 0 := by
  exact A.map_coord_zero a (by simp)

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nabla0SFun_perm
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (σ : Equiv.Perm (Fin s)) (c : Real)
    (hperm : ∀ y : M, ∀ slots : Fin s -> TangentSpace I y,
      A y slots = c * A y (fun q : Fin s => slots (σ q)))
    (slots : Fin s -> TangentSpace I x) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov X A x) slots =
      c * (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X A x) (fun q : Fin s => slots (σ q)) := by
  classical
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose
  have hV : ∀ a : Fin s, V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose_spec
  let Vσ : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (σ a)
  have hslots : (fun a : Fin s => V a x) = slots := by
    funext a
    exact hV a
  have hslotsσ : (fun a : Fin s => Vσ a x) =
      fun a : Fin s => slots (σ a) := by
    funext a
    exact hV (σ a)
  have hleft := nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    cov X V A x
  have hright := nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    cov X Vσ A x
  have hfσ : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => A p (fun a : Fin s => Vσ a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      A Vσ x).mdifferentiableAt (by simp)
  have hfun :
      (fun p : M => A p (fun a : Fin s => V a p)) =
        fun p : M => c * A p (fun a : Fin s => Vσ a p) := by
    funext p
    simpa [Vσ] using hperm p (fun a : Fin s => V a p)
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin s => V a p)) x (X x) =
        c * extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin s => Vσ a p)) x (X x) := by
    rw [hfun]
    have hmul := extDerivFun_const_mul
      (I := I) c (f := fun p : M => A p (fun a : Fin s => Vσ a p))
      (x := x) hfσ
    exact congrArg (fun L : TangentSpace I x →L[Real] Real => L (X x)) hmul
  let termR : Fin s -> Real := fun a =>
    A x
      (Function.update (fun b : Fin s => Vσ b x) a
        ((cov (fun p : M => Vσ a p) x) (X x)))
  have hsum :
      (∑ a : Fin s,
        A x
          (Function.update (fun b : Fin s => V b x) a
            ((cov (fun p : M => V a p) x) (X x)))) =
        c * ∑ a : Fin s, termR a := by
    calc
      (∑ a : Fin s,
        A x
          (Function.update (fun b : Fin s => V b x) a
            ((cov (fun p : M => V a p) x) (X x)))) =
          ∑ a : Fin s,
            c * A x
              (fun q : Fin s =>
                Function.update (fun b : Fin s => V b x) a
                  ((cov (fun p : M => V a p) x) (X x)) (σ q)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hperm x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (fun p : M => V a p) x) (X x)))]
      _ = c *
          ∑ a : Fin s,
            A x
              (fun q : Fin s =>
                Function.update (fun b : Fin s => V b x) a
                  ((cov (fun p : M => V a p) x) (X x)) (σ q)) := by
            rw [Finset.mul_sum]
      _ = c * ∑ a : Fin s, termR a := by
            congr 1
            calc
              (∑ a : Fin s,
                A x
                  (fun q : Fin s =>
                    Function.update (fun b : Fin s => V b x) a
                      ((cov (fun p : M => V a p) x) (X x)) (σ q))) =
                  ∑ a : Fin s, termR (σ.symm a) := by
                    refine Finset.sum_congr rfl fun a _ => ?_
                    have hslots_update :=
                      update_comp_perm (s := s) σ
                        (fun b : Fin s => V b x) a
                        ((cov (fun p : M => V a p) x) (X x))
                    simpa [termR, Vσ] using
                      congrArg (fun slots : Fin s -> TangentSpace I x => A x slots)
                        hslots_update
              _ = ∑ a : Fin s, termR a := by
                    simpa using (Equiv.sum_comp σ.symm termR)
  rw [← hslots]
  change
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X A x) (fun a : Fin s => V a x)) =
      c * ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X A x) (fun a : Fin s => Vσ a x))
  rw [hleft, hright, hderiv, hsum]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem finCons_vec4_eq_vec5 {x : M}
    (A W X Y Z : TangentSpace I x) :
    Fin.cons A (vec4 (I := I) W X Y Z) =
      vec5 (I := I) A W X Y Z := by
  funext q
  fin_cases q <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem slots4_eq_vec4 {x : M}
    (slots : Fin 4 -> TangentSpace I x) :
    slots = vec4 (I := I) (slots 0) (slots 1) (slots 2) (slots 3) := by
  funext q
  fin_cases q <;> rfl



omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nabla4OutSkew
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (x : M)
    (hskew : ∀ y : M, Rm04OutputSkewAt (I := I) (Rm04 y)) :
    ∀ W Y Z U : TangentSpace I x,
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X Rm04 x) (vec4 (I := I) W Y Z U) =
        - (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 cov X Rm04 x) (vec4 (I := I) W Y U Z) := by
  intro W Y Z U
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  have hperm : ∀ y : M, ∀ slots : Fin 4 -> TangentSpace I y,
      Rm04 y slots = (-1 : Real) * Rm04 y (fun q : Fin 4 => slots (σ q)) := by
    intro y slots
    rw [slots4_eq_vec4 (I := I) (fun q : Fin 4 => slots (σ q))]
    rw [slots4_eq_vec4 (I := I) slots]
    have h := hskew y (slots 0) (slots 1) (slots 2) (slots 3)
    simpa [σ, vec4, Equiv.swap_apply_def] using h
  have h := nabla0SFun_perm (I := I)
    cov X Rm04 x σ (-1 : Real) hperm (vec4 (I := I) W Y Z U)
  rw [slots4_eq_vec4 (I := I) (fun q : Fin 4 => vec4 (I := I) W Y Z U (σ q))] at h
  simpa [σ, vec4, Equiv.swap_apply_def] using h



omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nabla4InSkew
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (x : M)
    (hskew : ∀ y : M, ∀ W Y Z U : TangentSpace I y,
      Rm04 y (vec4 (I := I) Y W Z U) =
        -Rm04 y (vec4 (I := I) W Y Z U)) :
    ∀ W Y Z U : TangentSpace I x,
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X Rm04 x) (vec4 (I := I) Y W Z U) =
        - (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 cov X Rm04 x) (vec4 (I := I) W Y Z U) := by
  intro W Y Z U
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  have hperm : ∀ y : M, ∀ slots : Fin 4 -> TangentSpace I y,
      Rm04 y slots = (-1 : Real) * Rm04 y (fun q : Fin 4 => slots (σ q)) := by
    intro y slots
    rw [slots4_eq_vec4 (I := I) (fun q : Fin 4 => slots (σ q))]
    rw [slots4_eq_vec4 (I := I) slots]
    have h := hskew y (slots 1) (slots 0) (slots 2) (slots 3)
    simpa [σ, vec4, Equiv.swap_apply_def] using h
  have h := nabla0SFun_perm (I := I)
    cov X Rm04 x σ (-1 : Real) hperm (vec4 (I := I) Y W Z U)
  rw [slots4_eq_vec4 (I := I) (fun q : Fin 4 => vec4 (I := I) Y W Z U (σ q))] at h
  simpa [σ, vec4, Equiv.swap_apply_def] using h



omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nabla4Pair
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (x : M)
    (hpair : ∀ y : M, ∀ W Y Z U : TangentSpace I y,
      Rm04 y (vec4 (I := I) W Y Z U) =
        Rm04 y (vec4 (I := I) Z U W Y)) :
    ∀ W Y Z U : TangentSpace I x,
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X Rm04 x) (vec4 (I := I) W Y Z U) =
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 cov X Rm04 x) (vec4 (I := I) Z U W Y) := by
  intro W Y Z U
  let σ : Equiv.Perm (Fin 4) := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
  have hperm : ∀ y : M, ∀ slots : Fin 4 -> TangentSpace I y,
      Rm04 y slots = (1 : Real) * Rm04 y (fun q : Fin 4 => slots (σ q)) := by
    intro y slots
    rw [slots4_eq_vec4 (I := I) (fun q : Fin 4 => slots (σ q))]
    rw [slots4_eq_vec4 (I := I) slots]
    have h := hpair y (slots 0) (slots 1) (slots 2) (slots 3)
    simpa [σ, vec4, Equiv.swap_apply_def] using h
  have h := nabla0SFun_perm (I := I)
    cov X Rm04 x σ (1 : Real) hperm (vec4 (I := I) W Y Z U)
  rw [slots4_eq_vec4 (I := I) (fun q : Fin 4 => vec4 (I := I) W Y Z U (σ q))] at h
  simpa [σ, vec4, Equiv.swap_apply_def] using h


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem canRmSymm
    (g : SmoothRiemannianMetric I M)
    {x : M} :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    let nablaRm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x
    NablaRmSymmAt (I := I) nablaRm04 := by
  classical
  dsimp [NablaRmSymmAt]
  constructor
  · intro A W X Y Z
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let hcov1 :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    obtain ⟨Asec, hAsec⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x A
    have hsymm :=
      nabla4OutSkew (I := I) cov Asec Rm04 x
        (fun y =>
          DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
            (I := I) g Rm04
            (DifferentialGeometry.Integral.Connection.rm04Section_realizes
              (I := I) g cov hcov) (x := y))
        W X Y Z
    have hleft :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Asec Rm04 x (vec4 (I := I) W X Y Z)
    have hright :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Asec Rm04 x (vec4 (I := I) W X Z Y)
    rw [← hAsec]
    rw [show vec5 (I := I) (Asec x) W X Y Z =
        Fin.cons (Asec x) (vec4 (I := I) W X Y Z) by
        rw [finCons_vec4_eq_vec5]]
    rw [show vec5 (I := I) (Asec x) W X Z Y =
        Fin.cons (Asec x) (vec4 (I := I) W X Z Y) by
        rw [finCons_vec4_eq_vec5]]
    rw [hleft, hright]
    exact hsymm
  constructor
  · intro A W X Y Z
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    obtain ⟨Asec, hAsec⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x A
    have hsymm :=
      nabla4InSkew (I := I) cov Asec Rm04 x
        (fun y =>
          DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
            (I := I) g Rm04
            (DifferentialGeometry.Integral.Connection.rm04Section_realizes
              (I := I) g cov hcov) (x := y))
        W X Y Z
    have hleft :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Asec Rm04 x (vec4 (I := I) X W Y Z)
    have hright :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Asec Rm04 x (vec4 (I := I) W X Y Z)
    rw [← hAsec]
    rw [show vec5 (I := I) (Asec x) X W Y Z =
        Fin.cons (Asec x) (vec4 (I := I) X W Y Z) by
        rw [finCons_vec4_eq_vec5]]
    rw [show vec5 (I := I) (Asec x) W X Y Z =
        Fin.cons (Asec x) (vec4 (I := I) W X Y Z) by
        rw [finCons_vec4_eq_vec5]]
    rw [hleft, hright]
    exact hsymm
  · intro A W X Y Z
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let hcov1 :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    obtain ⟨Asec, hAsec⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x A
    have hsymm :=
      nabla4Pair (I := I) cov Asec Rm04 x
        (fun y =>
          DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
            (I := I) g Rm04
            (DifferentialGeometry.Integral.Connection.rm04Section_realizes
              (I := I) g cov hcov) (x := y))
        W X Y Z
    have hleft :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Asec Rm04 x (vec4 (I := I) W X Y Z)
    have hright :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Asec Rm04 x (vec4 (I := I) Y Z W X)
    rw [← hAsec]
    rw [show vec5 (I := I) (Asec x) W X Y Z =
        Fin.cons (Asec x) (vec4 (I := I) W X Y Z) by
        rw [finCons_vec4_eq_vec5]]
    rw [show vec5 (I := I) (Asec x) Y Z W X =
        Fin.cons (Asec x) (vec4 (I := I) Y Z W X) by
        rw [finCons_vec4_eq_vec5]]
    rw [hleft, hright]
    exact hsymm



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem canRmSecond
    (g : SmoothRiemannianMetric I M)
    {x : M} :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    let nablaRm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x
    SecondBianchiAt (I := I) nablaRm04 := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let hcov1 :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 x
  dsimp [SecondBianchiAt]
  intro A X Y Z W
  obtain ⟨Asec, hAsec, hcovA⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 x A
  obtain ⟨Xsec, hXsec, hcovX⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 x X
  obtain ⟨Ysec, hYsec, hcovY⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 x Y
  obtain ⟨Zsec, hZsec, hcovZ⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 x Z
  obtain ⟨Wsec, hWsec, hcovW⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 x W
  let Rsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ⟨fun p : M =>
      connectionRiemannCurvatureField (I := I) cov
        (fun q : M => Xsec q) (fun q : M => Ysec q)
        (fun q : M => Zsec q) p,
      by
        intro p
        exact DifferentialGeometry.Integral.Connection.CovariantDerivative.curvField_contMDiffAt
          (I := I) cov hcov Xsec Ysec Zsec p⟩
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have term_eq
      (D : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
      (D0 : TangentSpace I x) (hD : D x = D0)
      (P Q R : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
      (hcovP : ∀ V : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _), (cov (fun p => P p) x) (V x) = 0)
      (hcovQ : ∀ V : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _), (cov (fun p => Q p) x) (V x) = 0)
      (hcovR : ∀ V : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _), (cov (fun p => R p) x) (V x) = 0) :
      nablaRm04 (vec5 (I := I) D0 (P x) (Q x) (R x) W) =
        g.inner x W
          (curvCovDerivOpAt (I := I) cov D P Q R x) := by
    let Rcurv : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
      ⟨fun p : M =>
        connectionRiemannCurvatureField (I := I) cov
          (fun q : M => P q) (fun q : M => Q q) (fun q : M => R q) p,
        by
          intro p
          exact DifferentialGeometry.Integral.Connection.CovariantDerivative.curvField_contMDiffAt
            (I := I) cov hcov P Q R p⟩
    have htotal :=
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov D Rm04 x (vec4 (I := I) (P x) (Q x) (R x) W)
    have heval :=
      nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov D
        (fun a : Fin 4 =>
          match a with
          | ⟨0, _⟩ => P
          | ⟨1, _⟩ => Q
          | ⟨2, _⟩ => R
          | ⟨3, _⟩ => Wsec)
        Rm04 x
    have hderiv :
        extDerivFun (I := I)
            (fun p : M =>
              Rm04 p
                (fun a : Fin 4 =>
                  (match a with
                    | ⟨0, _⟩ => P
                    | ⟨1, _⟩ => Q
                    | ⟨2, _⟩ => R
                    | ⟨3, _⟩ => Wsec) p))
            x (D x) =
          g.inner x W ((cov (fun p : M => Rcurv p) x) (D x)) := by
      have hfun :
          (fun p : M =>
              Rm04 p
                (fun a : Fin 4 =>
                  (match a with
                    | ⟨0, _⟩ => P
                    | ⟨1, _⟩ => Q
                    | ⟨2, _⟩ => R
                    | ⟨3, _⟩ => Wsec) p)) =
            fun p : M => g.inner p (Wsec p) (Rcurv p) := by
        funext p
        simpa [Rcurv, Rm04, vec4, DifferentialGeometry.Integral.Connection.vec4] using
          DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section_apply_smooth
            (I := I) g cov hcov P Q R Wsec p
      have hDmd : MDiffAt (T% fun p : M => D p) x :=
        (D.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
      have hWmd : MDiffAt (T% fun p : M => Wsec p) x :=
        (Wsec.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
      have hRmd : MDiffAt (T% fun p : M => Rcurv p) x :=
        (Rcurv.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
      have hmetric :=
        DifferentialGeometry.Integral.Connection.metric_compatible_apply
          (I := I) (x := x) hmc (fun p : M => D p) (fun p : M => Wsec p)
          (fun p : M => Rcurv p) hDmd hWmd hRmd
      rw [hfun]
      rw [extDerivFun_real_eq_mfderiv]
      rw [hmetric]
      rw [hcovW D]
      simp [hWsec]
    have hcorr :
        (∑ a : Fin 4,
          Rm04 x
            (Function.update
              (fun b : Fin 4 =>
                (match b with
                  | ⟨0, _⟩ => P
                  | ⟨1, _⟩ => Q
                  | ⟨2, _⟩ => R
                  | ⟨3, _⟩ => Wsec) x) a
              ((cov
                (fun p : M =>
                  (match a with
                    | ⟨0, _⟩ => P
                    | ⟨1, _⟩ => Q
                    | ⟨2, _⟩ => R
                    | ⟨3, _⟩ => Wsec) p) x) (D x)))) = 0 := by
      rw [Fin.sum_univ_four]
      simp [hcovW D, hcovP D, hcovQ D, hcovR D, tensor0S_update_zero]
    have hop :
        curvCovDerivOpAt (I := I) cov D P Q R x =
          (cov (fun p : M => Rcurv p) x) (D x) := by
      let Z0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _) := 0
      let DP : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _) :=
        ⟨fun p : M => (cov (fun q : M => P q) p) (D p), by
          intro p
          exact DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
            (I := I) cov hcov D P p⟩
      let DQ : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _) :=
        ⟨fun p : M => (cov (fun q : M => Q q) p) (D p), by
          intro p
          exact DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
            (I := I) cov hcov D Q p⟩
      let DR : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _) :=
        ⟨fun p : M => (cov (fun q : M => R q) p) (D p), by
          intro p
          exact DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
            (I := I) cov hcov D R p⟩
      have hzero_first
          (U V T : ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M -> Type _)) (hU : U x = 0) :
          connectionRiemannCurvatureField (I := I) cov
              (fun p : M => U p) (fun p : M => V p) (fun p : M => T p) x = 0 := by
        let Φ : ((p : M) -> TangentSpace I p) -> TangentSpace I x := fun X =>
          connectionRiemannCurvatureField (I := I) cov
            X (fun p : M => V p) (fun p : M => T p) x
        have hTens : TensorialAt I E Φ x :=
          DifferentialGeometry.Integral.Connection.CovariantDerivative.connectionRiemannCurvatureField_tensorial_left
            (I := I) cov hcov V T x
        have hUmd : MDiffAt (T% fun p : M => U p) x :=
          (U.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
        have hZmd : MDiffAt (T% fun p : M => Z0 p) x :=
          (Z0.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
        calc
          connectionRiemannCurvatureField (I := I) cov
              (fun p : M => U p) (fun p : M => V p) (fun p : M => T p) x
              = Φ (fun p : M => Z0 p) := by
                exact TensorialAt.pointwise (I := I) (F := E) hTens hUmd hZmd hU
          _ = 0 := by
                simpa [Φ, Z0] using TensorialAt.zero (I := I) (F := E) hTens
      have hzero_mid
          (U V T : ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M -> Type _)) (hV : V x = 0) :
          connectionRiemannCurvatureField (I := I) cov
              (fun p : M => U p) (fun p : M => V p) (fun p : M => T p) x = 0 := by
        let Φ : ((p : M) -> TangentSpace I p) -> TangentSpace I x := fun Y =>
          connectionRiemannCurvatureField (I := I) cov
            (fun p : M => U p) Y (fun p : M => T p) x
        have hTens : TensorialAt I E Φ x :=
          DifferentialGeometry.Integral.Connection.CovariantDerivative.connectionRiemannCurvatureField_tensorial_middle
            (I := I) cov hcov U T x
        have hVmd : MDiffAt (T% fun p : M => V p) x :=
          (V.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
        have hZmd : MDiffAt (T% fun p : M => Z0 p) x :=
          (Z0.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
        calc
          connectionRiemannCurvatureField (I := I) cov
              (fun p : M => U p) (fun p : M => V p) (fun p : M => T p) x
              = Φ (fun p : M => Z0 p) := by
                exact TensorialAt.pointwise (I := I) (F := E) hTens hVmd hZmd hV
          _ = 0 := by
                simpa [Φ, Z0] using TensorialAt.zero (I := I) (F := E) hTens
      have hzero_right
          (U V T : ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M -> Type _)) (hT : T x = 0) :
          connectionRiemannCurvatureField (I := I) cov
              (fun p : M => U p) (fun p : M => V p) (fun p : M => T p) x = 0 := by
        have hcong :=
          DifferentialGeometry.Integral.Connection.CovariantDerivative.connectionRiemannCurvatureField_congr_point
            (I := I) cov hcov U U V V T Z0 rfl rfl hT
        have hz :
            connectionRiemannCurvatureField (I := I) cov
              (fun p : M => U p) (fun p : M => V p) (fun p : M => Z0 p) x = 0 := by
          simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField,
            DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
          have hV0 :
              (fun y : M => (cov (fun p : M => Z0 p) y) (V y)) =
                fun y : M => 0 := by
            funext y
            have hzeroCov :
                cov (fun p : M => Z0 p) y = 0 := by
              change cov (0 : (p : M) -> TangentSpace I p) y = 0
              exact cov.isCovariantDerivativeOnUniv.zero
            simp [hzeroCov]
          have hU0 :
              (fun y : M => (cov (fun p : M => Z0 p) y) (U y)) =
                fun y : M => 0 := by
            funext y
            have hzeroCov :
                cov (fun p : M => Z0 p) y = 0 := by
              change cov (0 : (p : M) -> TangentSpace I p) y = 0
              exact cov.isCovariantDerivativeOnUniv.zero
            simp [hzeroCov]
          rw [hV0, hU0]
          have hzeroCov :
              cov (fun y : M => (0 : TangentSpace I y)) x = 0 := by
            change cov (0 : (y : M) -> TangentSpace I y) x = 0
            exact cov.isCovariantDerivativeOnUniv.zero
          have hzeroCovZ :
              cov (fun p : M => Z0 p) x = 0 := by
            change cov (0 : (p : M) -> TangentSpace I p) x = 0
            exact cov.isCovariantDerivativeOnUniv.zero
          rw [hzeroCov]
          rw [hzeroCovZ]
          simp
        exact hcong.trans hz
      have hDPx : DP x = 0 := by
        simpa [DP] using hcovP D
      have hDQx : DQ x = 0 := by
        simpa [DQ] using hcovQ D
      have hDRx : DR x = 0 := by
        simpa [DR] using hcovR D
      have hPterm :
          connectionRiemannCurvatureField (I := I) cov
            (fun p : M => (cov (fun q : M => P q) p) (D p))
            (fun p : M => Q p) (fun p : M => R p) x = 0 := by
        simpa [DP] using hzero_first DP Q R hDPx
      have hQterm :
          connectionRiemannCurvatureField (I := I) cov
            (fun p : M => P p)
            (fun p : M => (cov (fun q : M => Q q) p) (D p))
            (fun p : M => R p) x = 0 := by
        simpa [DQ] using hzero_mid P DQ R hDQx
      have hRterm :
          connectionRiemannCurvatureField (I := I) cov
            (fun p : M => P p) (fun p : M => Q p)
            (fun p : M => (cov (fun q : M => R q) p) (D p)) x = 0 := by
        simpa [DR] using hzero_right P Q DR hDRx
      unfold curvCovDerivOpAt
      simp [Rcurv, hPterm, hQterm, hRterm]
    calc
      nablaRm04 (vec5 (I := I) D0 (P x) (Q x) (R x) W)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 cov D Rm04 x (vec4 (I := I) (P x) (Q x) (R x) W) := by
            rw [← hD]
            rw [show vec5 (I := I) (D x) (P x) (Q x) (R x) W =
                Fin.cons (D x) (vec4 (I := I) (P x) (Q x) (R x) W) by
                rw [finCons_vec4_eq_vec5]]
            exact htotal
      _ =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 cov D Rm04 x
            (fun a : Fin 4 =>
              (match a with
                | ⟨0, _⟩ => P
                | ⟨1, _⟩ => Q
                | ⟨2, _⟩ => R
                | ⟨3, _⟩ => Wsec) x) := by
            rw [show vec4 (I := I) (P x) (Q x) (R x) W =
                (fun a : Fin 4 =>
                  (match a with
                    | ⟨0, _⟩ => P
                    | ⟨1, _⟩ => Q
                    | ⟨2, _⟩ => R
                    | ⟨3, _⟩ => Wsec) x) by
                funext a
                fin_cases a <;> simp [hWsec, vec4, DifferentialGeometry.Integral.Connection.vec4]]
      _ =
          extDerivFun (I := I)
            (fun p : M =>
              Rm04 p
                (fun a : Fin 4 =>
                  (match a with
                    | ⟨0, _⟩ => P
                    | ⟨1, _⟩ => Q
                    | ⟨2, _⟩ => R
                    | ⟨3, _⟩ => Wsec) p))
            x (D x) -
          (∑ a : Fin 4,
            Rm04 x
              (Function.update
                (fun b : Fin 4 =>
                  (match b with
                    | ⟨0, _⟩ => P
                    | ⟨1, _⟩ => Q
                    | ⟨2, _⟩ => R
                    | ⟨3, _⟩ => Wsec) x) a
                ((cov
                  (fun p : M =>
                    (match a with
                      | ⟨0, _⟩ => P
                      | ⟨1, _⟩ => Q
                      | ⟨2, _⟩ => R
                      | ⟨3, _⟩ => Wsec) p) x) (D x)))) := heval
      _ = g.inner x W ((cov (fun p : M => Rcurv p) x) (D x)) := by
            rw [hderiv, hcorr]
            simp
      _ = g.inner x W (curvCovDerivOpAt (I := I) cov D P Q R x) := by
            rw [hop]
  have h1 :
      nablaRm04 (vec5 (I := I) A X Y Z W) =
        g.inner x W (curvCovDerivOpAt (I := I) cov Asec Xsec Ysec Zsec x) := by
    simpa [hXsec, hYsec, hZsec] using
      term_eq Asec A hAsec Xsec Ysec Zsec hcovX hcovY hcovZ
  have h2 :
      nablaRm04 (vec5 (I := I) X Y A Z W) =
        g.inner x W (curvCovDerivOpAt (I := I) cov Xsec Ysec Asec Zsec x) := by
    simpa [hAsec, hYsec, hZsec] using
      term_eq Xsec X hXsec Ysec Asec Zsec hcovY hcovA hcovZ
  have h3 :
      nablaRm04 (vec5 (I := I) Y A X Z W) =
        g.inner x W (curvCovDerivOpAt (I := I) cov Ysec Asec Xsec Zsec x) := by
    simpa [hAsec, hXsec, hZsec] using
      term_eq Ysec Y hYsec Asec Xsec Zsec hcovA hcovX hcovZ
  have hb :=
    curvSecondBianchi (I := I) cov hcov
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g)
      Asec Xsec Ysec Zsec x
  have hinner :
      g.inner x W
        (curvCovDerivOpAt (I := I) cov Asec Xsec Ysec Zsec x +
          curvCovDerivOpAt (I := I) cov Xsec Ysec Asec Zsec x +
            curvCovDerivOpAt (I := I) cov Ysec Asec Xsec Zsec x) = 0 := by
    rw [hb]
    simp
  rw [h1, h2, h3]
  simpa [add_assoc] using hinner

set_option backward.isDefEq.respectTransparency false in


omit [I.Boundaryless] in
theorem canRicField
    (g : SmoothRiemannianMetric I M) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    Ric = trace04Field (I := I) (M := M) g Rm04 := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  have hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13 := by
    intro y
    simp [Ric, Rm13,
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection_eq_trace
        (I := I) (M := M) cov hcov y)]
  have hRm13 : Rm13RealizesConnection (I := I) cov Rm13 := by
    simpa [Rm13] using
      (rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov))
  have hRm04 : Rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04] using
      (rm04Section_realizes (I := I) (M := M) g (cov := cov) (hcov := hcov))
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  dsimp
  apply ContMDiffSection.ext
  intro y
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) y
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g y k l (extChartAt I y y)
  have hinv :
      MetricInverseInBasis_gen (I := I) (M := M) g y basis gInv := by
    simpa [basis, gInv] using
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g y)
  have hInvSym : ∀ i j, gInv i j = gInv j i := by
    intro i j
    simpa [gInv] using
      (DifferentialGeometry.Tensor.Coordinates.gInvChart_symm (I := I) g y
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) y) i j)
  have hLower :
      Rm04LowersRm13At (I := I) g y (Rm13 y) (Rm04 y) :=
    rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 y
  have hTrace :
      RicciRealizesRm04FirstTraceAt (I := I) (Ric y) (Rm04 y) gInv basis := by
    exact ricciFirstTraceAt_of_rm13_section (I := I) g basis gInv hinv
      Ric Rm13 Rm04 hRic13 hLower hInvSym
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun a : Fin 2 => basis (slots a)) =
        vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2]
  rw [component0S_apply, component0S_apply]
  rw [hslots]
  calc
    Ric y (vec2 (I := I) (basis (slots 0)) (basis (slots 1)))
        =
      ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            Rm04 y (vec4 (I := I) (basis i) (basis (slots 0))
              (basis (slots 1)) (basis j)) := by
        simpa using hTrace (slots 0) (slots 1)
    _ =
      metricTraceFirstTwo0SAt (I := I) g
        ((Rm04 y).domDomCongr trace04Perm)
        (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) := by
        rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        congr 1
    _ =
      trace04Field (I := I) (M := M) g Rm04 y
        (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) := by
        simp [metricTraceFirstTwo0STensor_apply, metricTraceFirstTwo0SAt]



theorem canRicTrace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let nablaRm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x
    let nablaRic :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric x
    NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 x
  let nablaRic :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric x
  dsimp
  intro A B C
  have hRicField : Ric = trace04Field (I := I) (M := M) g Rm04 := by
    simpa [cov, hcov, Rm04, Ric] using
      (canRicField (I := I) (M := M) g)
  have hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (1 : WithTop ℕ∞) := by
    simpa [cov] using
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) g)
  have htrace :=
    nablaTrace04 (I := I) (M := M) cov hcov1 g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      Rm04 basis gInv hinv A B C
  simpa [cov, hcov, Rm04, Ric, nablaRm04, nablaRic, hRicField,
    finCons_vec4_eq_vec5] using htrace





theorem canBianchiCore
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let nablaRm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x
    let nablaRic :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric x
    SecondBianchiAt (I := I) nablaRm04 ∧
      NablaRmSymmAt (I := I) nablaRm04 ∧
        NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 x
  let nablaRic :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric x
  have hSecond : SecondBianchiAt (I := I) nablaRm04 := by
    simpa [cov, hcov, Rm04, nablaRm04] using
      canRmSecond (I := I) (M := M) g (x := x)
  have hSymm : NablaRmSymmAt (I := I) nablaRm04 := by
    simpa [cov, hcov, Rm04, nablaRm04] using
      canRmSymm (I := I) (M := M) g (x := x)
  have hTrace : NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic := by
    simpa [cov, hcov, Rm04, Ric, nablaRm04, nablaRic] using
      canRicTrace (I := I) (M := M) g basis gInv hinv
  exact ⟨hSecond, hSymm, hTrace⟩







theorem canSecondBianchi
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let scalar : M -> Real :=
      fun y => metricTracePair0SAt (I := I) g (Ric y)
    let nablaRm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x
    let nablaRic :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric x
    let dScalar := differential1FormFun (I := I) scalar x
    SecondBianchiAt (I := I) nablaRm04 ∧
      NablaRmSymmAt (I := I) nablaRm04 ∧
        NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic ∧
          DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let scalar : M -> Real :=
    fun y => metricTracePair0SAt (I := I) g (Ric y)
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 x
  let nablaRic :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric x
  let dScalar := differential1FormFun (I := I) scalar x
  have hcore :
      SecondBianchiAt (I := I) nablaRm04 ∧
        NablaRmSymmAt (I := I) nablaRm04 ∧
          NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic := by
    simpa [cov, hcov, Rm04, Ric, nablaRm04, nablaRic] using
      canBianchiCore (I := I) (M := M) g basis gInv hinv
  have hscalar :
      DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
    simpa [cov, hcov, Ric, scalar, nablaRic, dScalar] using
      canScalTrace (I := I) (M := M) g basis gInv hinv
  exact ⟨hcore.1, hcore.2.1, hcore.2.2, hscalar⟩



theorem metricBianchiAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv) :
    let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Ric : Tensor02Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let scalar : M -> Real :=
      fun y => metricTracePair0SAt (I := I) g (Ric y)
    let nablaRic :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric x
    let dScalar := differential1FormFun (I := I) scalar x
    ∃ nablaRm04 :
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x,
      SecondBianchiAt (I := I) nablaRm04 ∧
        NablaRmSymmAt (I := I) nablaRm04 ∧
          NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic ∧
            DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let scalar : M -> Real :=
    fun y => metricTracePair0SAt (I := I) g (Ric y)
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 x
  refine ⟨nablaRm04, ?_⟩
  simpa [cov, hcov, Rm04, Ric, scalar, nablaRm04] using
    canSecondBianchi (I := I) (M := M) g basis gInv hinv


end DifferentialGeometry.Integral.Connection
