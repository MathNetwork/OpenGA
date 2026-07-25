import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionRestrictOpen

set_option autoImplicit false
set_option linter.style.longLine false




























noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Connection.CovariantDerivative

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M]






omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private theorem covDerivOfField_succ_eval
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    covDerivOfField (I := I) gRef A0 (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => covDerivOfField (I := I) gRef A0 a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          covDerivOfField (I := I) gRef A0 a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [covDerivOfField_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V
    (covDerivOfField (I := I) gRef A0 a) x









omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_restrictOpen
    (gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (A0U : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := U) (n := (∞ : WithTop ℕ∞)) 2)
    (A0M : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (hA0 : ∀ (x : U) (slots : Fin 2 → TangentSpace I x),
      A0U x slots = A0M (x : M) slots) :
    ∀ a : Nat, ∀ x : U, ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a x slots =
        covDerivOfField (I := I) gRef A0M a (x : M) slots := by
  classical
  intro a
  induction a with
  | zero =>
      intro x slots
      exact hA0 x slots
  | succ a ih =>
      intro x slots

      obtain ⟨X, hX⟩ :=
        ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
          (n := (⊤ : ℕ∞)) (x : M) (slots 0)
      let V : Fin (a + 2) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
        fun q =>
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose
      have hV : ∀ q : Fin (a + 2), V q (x : M) = slots q.succ := by
        intro q
        exact
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose_spec

      let XU : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U → Type _) :=
        restrictOpenTangentSection (I := I) U X
      let VU : Fin (a + 2) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U → Type _) :=
        fun q => restrictOpenTangentSection (I := I) U (V q)
      have hsmooth :
          covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U (a + 1) x
              (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x)) =
            covDerivOfField (I := I) gRef A0M (a + 1) (x : M)
              (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M))) := by
        have hleft :=
          covDerivOfField_succ_eval (I := I) (gRef.restrictOpen (I := I) U) A0U a XU VU x
        have hright :=
          covDerivOfField_succ_eval (I := I) gRef A0M a X V (x : M)
        rw [hleft, hright]

        have hderiv :
            extDerivFun (I := I)
                (fun y : U => covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a y
                  (fun q : Fin (a + 2) => VU q y)) x (XU x) =
              extDerivFun (I := I)
                (fun z : M => covDerivOfField (I := I) gRef A0M a z
                  (fun q : Fin (a + 2) => V q z)) (x : M) (X (x : M)) := by
          have hscalar :
              (fun y : U => covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a y
                (fun q : Fin (a + 2) => VU q y)) =
                fun y : U => (fun z : M => covDerivOfField (I := I) gRef A0M a z
                  (fun q : Fin (a + 2) => V q z)) (y : M) := by
            funext y
            simpa [VU, restrictOpenTangentSection_apply] using
              ih y (fun q : Fin (a + 2) => VU q y)
          have hf : MDifferentiableAt I 𝓘(ℝ, ℝ)
              (fun z : M => covDerivOfField (I := I) gRef A0M a z
                (fun q : Fin (a + 2) => V q z)) (x : M) :=
            (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
              (I := I) (covDerivOfField (I := I) gRef A0M a)
              (fun q : Fin (a + 2) => V q) (x : M)).mdifferentiableAt (by simp)
          rw [hscalar]
          have hXU : XU x = X (x : M) := restrictOpenTangentSection_apply (I := I) U X x
          rw [hXU]
          exact extDerivFun_restrictOpen (I := I) U
            (fun z : M => covDerivOfField (I := I) gRef A0M a z
              (fun q : Fin (a + 2) => V q z)) x (X (x : M)) hf

        have hsum :
            (∑ p : Fin (a + 2),
              covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a x
                (Function.update (fun q : Fin (a + 2) => VU q x) p
                  (((leviCivitaConnectionOfMetric (I := I) (gRef.restrictOpen (I := I) U))
                      (fun y : U => VU p y) x) (XU x)))) =
              ∑ p : Fin (a + 2),
                covDerivOfField (I := I) gRef A0M a (x : M)
                  (Function.update (fun q : Fin (a + 2) => V q (x : M)) p
                    (((leviCivitaConnectionOfMetric (I := I) gRef)
                        (fun z : M => V p z) (x : M)) (X (x : M)))) := by
          apply Finset.sum_congr rfl
          intro p _

          set covL : TangentSpace I x :=
            ((leviCivitaConnectionOfMetric (I := I) (gRef.restrictOpen (I := I) U))
              (fun y : U => VU p y) x) (XU x) with hcovL_def
          set covR : TangentSpace I (x : M) :=
            ((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun z : M => V p z) (x : M)) (X (x : M)) with hcovR_def

          have hcov : covL = covR := by
            have hcov' := metricCov_restrictOpen_globalSection (I := I) gRef U (V p) x (X (x : M))


            rw [hcovL_def, hcovR_def]
            have hXU : XU x = X (x : M) := restrictOpenTangentSection_apply (I := I) U X x
            rw [hXU]
            exact hcov'

          have hslots : (fun q : Fin (a + 2) =>
              Function.update (fun q : Fin (a + 2) => VU q x) p covL q) =
              (fun q : Fin (a + 2) =>
                Function.update (fun q : Fin (a + 2) => V q (x : M)) p covR q) := by
            funext q
            by_cases hqp : q = p
            · subst q
              simp only [Function.update_self]
              exact hcov
            · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
              simp only [VU, restrictOpenTangentSection_apply]

          have hih := ih x (Function.update (fun q : Fin (a + 2) => VU q x) p covL)
          calc
            covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a x
                (Function.update (fun q : Fin (a + 2) => VU q x) p covL)
                = covDerivOfField (I := I) gRef A0M a (x : M)
                    (Function.update (fun q : Fin (a + 2) => VU q x) p covL) := hih
            _ = covDerivOfField (I := I) gRef A0M a (x : M)
                    (Function.update (fun q : Fin (a + 2) => V q (x : M)) p covR) :=
                  congrArg _ hslots
        rw [hderiv, hsum]

      have hslotsU :
          slots = Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      have hXUx : XU x = slots 0 := by
        rw [restrictOpenTangentSection_apply]; exact hX
      have hVUx : ∀ q : Fin (a + 2), VU q x = slots q.succ := by
        intro q; rw [restrictOpenTangentSection_apply]; exact hV q
      have hcons :
          (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x)
              : Fin (a + 1 + 2) → TangentSpace I x) = slots := by
        rw [hslotsU]
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero, Fin.cons_zero, hXUx]
        · rw [Fin.cons_succ, Fin.cons_succ, hVUx]
      have hconsM :
          (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M))
              : Fin (a + 1 + 2) → TangentSpace I (x : M)) = slots := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero, hX]
        · rw [Fin.cons_succ, hV]
      rw [hcons, hconsM] at hsmooth
      exact hsmooth






omit [I.Boundaryless] in
omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciSection_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 2 → TangentSpace I x) :
    CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          (g.restrictOpen (I := I) U)) x slots
      = CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
          (x : M) slots := by


  have hLHS :
      CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
            (g.restrictOpen (I := I) U)) x slots
        = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (slots 0) (slots 1) := by
    have hvecU : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i; fin_cases i <;> rfl
    rw [hvecU]
    exact ricciSection_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (slots 0) (slots 1)
  have hRHS :
      CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
          (x : M) slots
        = ricciTensor (I := I) (M := M) g (x : M) (slots 0) (slots 1) := by
    have hvecM : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i; fin_cases i <;> rfl
    rw [hvecM]
    exact ricciSection_eq_ricciTensor (I := I) g (x : M) (slots 0) (slots 1)
  rw [hLHS, hRHS]
  exact ricciTensor_restrictOpen (I := I) g U x (slots 0) (slots 1)





omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem covDerivOfField_apply_eq_iterCov'
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (m : ℕ) (x : M) (slots : Fin (m + 2) → TangentSpace I x) :
    covDerivOfField (I := I) gRef A0 m x slots
      = iterCov (I := I) gRef 2 A0 m x (slots ∘ ⇑(acEquiv m)) := by
  rw [covDerivOfField_eq_iterCov]
  rfl







omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricCovTower_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (s : ℕ) (x : U) (slots : Fin (2 + s) → TangentSpace I x) :
    ricCovTower (I := I) (g.restrictOpen (I := I) U)
        (g.restrictOpen (I := I) U) s x slots
      = ricCovTower (I := I) g g s (x : M) slots := by
  have hrestrict := covDerivOfField_restrictOpen (I := I) g U
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
        (g.restrictOpen (I := I) U)))
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
    (ricciSection_restrictOpen (I := I) g U) s x (slots ∘ (acEquiv s).symm)
  rw [covDerivOfField_apply_eq_iterCov', covDerivOfField_apply_eq_iterCov'] at hrestrict


  convert hrestrict using 2 <;>
    · funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]






omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricCovTower_normSq0S_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (s : ℕ) (x : U) :
    Tensor0SBundle.normSq0S (I := I) (g.restrictOpen (I := I) U) x (2 + s)
        (ricCovTower (I := I) (g.restrictOpen (I := I) U)
          (g.restrictOpen (I := I) U) s x)
      = Tensor0SBundle.normSq0S (I := I) g (x : M) (2 + s)
          (ricCovTower (I := I) g g s (x : M)) := by
  rw [normSq0S_restrictOpen_apply (I := I) g U (2 + s) x
    (ricCovTower (I := I) (g.restrictOpen (I := I) U) (g.restrictOpen (I := I) U) s x)]

  have htensor :
      ricCovTower (I := I) (g.restrictOpen (I := I) U) (g.restrictOpen (I := I) U) s x
        = ricCovTower (I := I) g g s (x : M) := by
    ext slots
    exact ricCovTower_restrictOpen (I := I) g U s x slots
  rw [htensor]







omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem movingShiBoundOn_restrictOpen
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (U₀ : Set M) (β ψ : ℝ) (Nord : ℕ) (KShi : ℝ) (V : Set U)
    (hV : ∀ x ∈ V, (x : M) ∈ U₀)
    (hShi : MovingShiBoundOn (I := I) U₀ β ψ gSeq Nord KShi) :
    MovingShiBoundOn (I := I) V β ψ
      (fun i t => (gSeq i t).restrictOpen (I := I) U) Nord KShi := by
  intro s hs i t ht x hx
  rw [ricCovTower_normSq0S_restrictOpen (I := I) (gSeq i t) U s x]
  exact hShi s hs i t ht (x : M) (hV x hx)

end HCGCompactness
end DifferentialGeometry

end
