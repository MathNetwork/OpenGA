import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0STimeDeriv
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]









omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_hasDerivWithinAt
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T R : Set Real) (N : ℕ)
    (hbase : ∀ t ∈ R, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) T R ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ R, ∀ x : M,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivWithinAt
          (fun r : Real => (covDerivOfField (I := I) gRef (A r) p) x v)
          ((covDerivOfField (I := I) gRef (B t) p) x v) T t := by
  intro p
  induction p with
  | zero =>
      intro _ t ht x v
      exact hbase t ht x v
  | succ p ih =>
      intro hpN t ht x v

      have hext : ∀ a : Fin (p + 3),
          ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
            σ x = v a :=
        fun a => ContMDiffSection.exists_eq_at_gen x (v a)
      choose σ hσ using hext

      have hcl := Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt (I := I)
        (leviCivitaConnectionOfMetric (I := I) gRef)
        (σ 0) (fun a : Fin (p + 2) => σ a.succ)
        (fun r => covDerivOfField (I := I) gRef (A r) p)
        (fun t' => covDerivOfField (I := I) gRef (B t') p)
        T x t
        ((hswap p (by omega) (fun a : Fin (p + 2) => σ a.succ) x) t ht x
          (Set.mem_singleton x) (σ 0 x))
        (fun a => ih (by omega) t ht x
          (Function.update (fun b : Fin (p + 2) => σ b.succ x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun q : M => σ a.succ q) x) (σ 0 x))))

      have hv : (Fin.cons (σ 0 x) (fun a : Fin (p + 2) => σ a.succ x) :
          Fin (p + 3) → TangentSpace I x) = v := by
        funext b
        refine Fin.cases ?_ ?_ b
        · simpa using hσ 0
        · intro a
          simpa using hσ a.succ
      rw [hv] at hcl
      exact hcl







omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_swapReg
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T R : Set Real) (hRT : R ⊆ T)
    (hRnhds : ∀ {t : Real}, t ∈ R → T ∈ 𝓝 t)
    (N : ℕ)
    (hbase : ∀ t ∈ R, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ R, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M => (covDerivOfField (I := I) gRef (A q.1) p) q.2
          (fun a : Fin (p + 2) => V a q.2)) (t, x))
    (hFdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ s ∈ T, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (covDerivOfField (I := I) gRef (A s) p) y
          (fun a : Fin (p + 2) => V a y)) x)
    (hFtdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ R, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (covDerivOfField (I := I) gRef (B t) p) y
          (fun a : Fin (p + 2) => V a y)) x) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) T R ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p')) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ihp =>
    intro hpN V x₀
    refine fixedBaseOnReg_of_timeDerivWithin (I := I) hRT
      (fun {t} ht => hRnhds ht)
      (fun t ht x _ => hSmooth p hpN V t ht x)
      (fun s hs x _ => hFdiff p hpN V s hs x)
      (fun t ht x _ => hFtdiff p hpN V t ht x) ?_
    intro t ht x'
    exact covDerivOfField_eval_hasDerivWithinAt (I := I) gRef A B T R p hbase
      (fun q hq => ihp q hq (lt_trans hq hpN))
      p le_rfl t ht x' (fun a : Fin (p + 2) => V a x')








omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_contMDiffAt
    (gRef : SmoothRiemannianMetric I M)
    (A : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {t : Real} {x : M}
    (hbase : ∀ V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => (A q.1) q.2 (fun a : Fin 2 => V a q.2)) (t, x)) :
    ∀ p : ℕ, ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x) := by
  intro p
  induction p with
  | zero => intro V; exact hbase V
  | succ p ih =>
      intro V
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩

      have hWsec : ∀ a : Fin (p + 2),
          ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
            (fun y : M =>
              (⟨y, ((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a.succ q) y) ((V 0) y)⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
        intro a
        simpa [TensorLieDeriv.covariantDeriv_vectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (V 0) (V a.succ)
      let W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun a =>
        ⟨fun y : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef)
            (fun q : M => V a.succ q) y) ((V 0) y), hWsec a⟩

      have hdec : ∀ q : Real × M,
          (covDerivOfField (I := I) gRef (A q.1) (p + 1)) q.2
              (fun a : Fin (p + 3) => V a q.2)
            = extDerivFun (I := I)
                (fun y : M => (covDerivOfField (I := I) gRef (A q.1) p) y
                  (fun a : Fin (p + 2) => V a.succ y)) q.2 ((V 0) q.2)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef (A q.1) p) q.2
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b q.2) := by
        intro q
        have hv : (fun a : Fin (p + 3) => V a q.2)
            = Fin.cons ((V 0) q.2) (fun a : Fin (p + 2) => V a.succ q.2) := by
          funext b
          refine Fin.cases ?_ ?_ b
          · simp
          · intro a
            simp
        have hupd : ∀ a : Fin (p + 2),
            (fun b : Fin (p + 2) =>
              (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a)) b q.2)
              = Function.update (fun b : Fin (p + 2) => V b.succ q.2) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun z : M => V a.succ z) q.2) ((V 0) q.2)) := by
          intro a
          funext b
          by_cases hba : b = a
          · subst hba
            simp [W]
          · simp [Function.update_of_ne hba]
        rw [covDerivOfField_succ, metricCovDerivStep_apply, hv,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hupd a]
      have h1 := prodExtDerivAt_inf (I := I)
        (F := fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) p) q.2
            (fun a : Fin (p + 2) => V a.succ q.2))
        (X := fun y : M => (V 0) y) (t := t) (x := x)
        (ih (fun a : Fin (p + 2) => V a.succ))
        ((V 0).contMDiff.contMDiffAt)
      have h2 : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun q : Real × M =>
            ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef (A q.1) p) q.2
                (fun b : Fin (p + 2) =>
                  (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                    b q.2)) (t, x) :=
        ContMDiffAt.sum fun a _ =>
          ih (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
      have hfun : (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) (p + 1)) q.2
            (fun a : Fin (p + 3) => V a q.2))
          = fun q : Real × M =>
              extDerivFun (I := I)
                (fun y : M => (covDerivOfField (I := I) gRef (A q.1) p) y
                  (fun a : Fin (p + 2) => V a.succ y)) q.2 ((V 0) q.2)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef (A q.1) p) q.2
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b q.2) :=
        funext hdec
      rw [hfun]
      exact h1.sub h2






omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_smoothAt
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {x : M}
    (hbase : ∀ V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => A0 y (fun a : Fin 2 => V a y)) x) :
    ∀ p : ℕ, ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (covDerivOfField (I := I) gRef A0 p) y
            (fun a : Fin (p + 2) => V a y)) x := by
  intro p
  induction p with
  | zero => intro V; exact hbase V
  | succ p ih =>
      intro V
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩
      have hWsec : ∀ a : Fin (p + 2),
          ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
            (fun y : M =>
              (⟨y, ((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a.succ q) y) ((V 0) y)⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
        intro a
        simpa [TensorLieDeriv.covariantDeriv_vectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (V 0) (V a.succ)
      let W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun a =>
        ⟨fun y : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef)
            (fun q : M => V a.succ q) y) ((V 0) y), hWsec a⟩
      have hdec : ∀ y : M,
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (fun a : Fin (p + 3) => V a y)
            = extDerivFun (I := I)
                (fun z : M => (covDerivOfField (I := I) gRef A0 p) z
                  (fun a : Fin (p + 2) => V a.succ z)) y ((V 0) y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b y) := by
        intro y
        have hv : (fun a : Fin (p + 3) => V a y)
            = Fin.cons ((V 0) y) (fun a : Fin (p + 2) => V a.succ y) := by
          funext b
          refine Fin.cases ?_ ?_ b
          · simp
          · intro a
            simp
        have hupd : ∀ a : Fin (p + 2),
            (fun b : Fin (p + 2) =>
              (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a)) b y)
              = Function.update (fun b : Fin (p + 2) => V b.succ y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun z : M => V a.succ z) y) ((V 0) y)) := by
          intro a
          funext b
          by_cases hba : b = a
          · subst hba
            simp [W]
          · simp [Function.update_of_ne hba]
        rw [covDerivOfField_succ, metricCovDerivStep_apply, hv,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hupd a]
      have h1 := extDerivFun_apply_contMDiffAt I
        (f := fun z : M => (covDerivOfField (I := I) gRef A0 p) z
          (fun a : Fin (p + 2) => V a.succ z))
        (x₀ := x)
        (ih (fun a : Fin (p + 2) => V a.succ))
        (V 0)
      have h2 : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef A0 p) y
                (fun b : Fin (p + 2) =>
                  (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                    b y)) x :=
        ContMDiffAt.sum fun a _ =>
          ih (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
      have hfun : (fun y : M =>
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
            (fun a : Fin (p + 3) => V a y))
          = fun y : M =>
              extDerivFun (I := I)
                (fun z : M => (covDerivOfField (I := I) gRef A0 p) z
                  (fun a : Fin (p + 2) => V a.succ z)) y ((V 0) y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b y) :=
        funext hdec
      rw [hfun]
      exact h1.sub h2




omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_mdiffAt
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        (covDerivOfField (I := I) gRef A0 p) y
          (fun a : Fin (p + 2) => V a y)) x :=
  (covDerivOfField_eval_smoothAt (I := I) gRef A0
    (fun W => Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
      (I := I) A0 W x)
    p V).mdifferentiableAt (by simp)




noncomputable def solnMetricField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (r : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  Tensor0SBundle.metricTensorField (I := I) (S.family.metric r)




noncomputable def solnRicField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  CovariantDerivative.ricciSection (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) (S.family.metric t))
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) (S.family.metric t))


noncomputable def solnEvolField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  (-2 : Real) • solnRicField (I := I) S t




omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solnRicField_eq_ricciAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (solnRicField (I := I) S t) x = S.ricciAt t x := by
  have h := CovariantDerivative.ricciSection_apply (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) (S.family.metric t))
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) (S.family.metric t)) x
  exact h



omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solnMetricDeriv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ D.regular, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt
        (fun r : Real => (solnMetricField (I := I) S r) x v)
        ((solnEvolField (I := I) S t) x v)
        D.carrier t := by
  intro t ht x v
  have heq := metric_derivWithin_eq_neg_two_ricci (I := I) S hS ⟨t, ht⟩ x (v 0) (v 1)
  have hvec : vec2 (I := I) (v 0) (v 1) = v := by
    funext i
    fin_cases i <;> simp [vec2]
  rw [hvec] at heq
  have hfun : (fun r : Real => (solnMetricField (I := I) S r) x v)
      = fun s : Real => (S.family.metric s).inner x (v 0) (v 1) := by
    funext r
    exact Tensor0SBundle.metricTensorField_apply (I := I) (S.family.metric r) x v
  have hval : (solnEvolField (I := I) S t) x v
      = (-2 : Real) * S.ricciAt t x v := by
    simp only [solnEvolField]
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, solnRicField_eq_ricciAt]
    rw [Tensor0SSpace.smul_apply]
    simp [smul_eq_mul]
  rw [hfun, hval]
  exact heq







omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solnTower_hasDerivAt
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ D.regular, ∀ x : M,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivAt
          (fun r : Real =>
            (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) x v)
          ((covDerivOfField (I := I) gRef (solnEvolField (I := I) S t) p) x v) t := by
  intro p hp t ht x v
  have h := covDerivOfField_eval_hasDerivWithinAt (I := I) gRef
    (fun r => solnMetricField (I := I) S r)
    (fun t' => solnEvolField (I := I) S t')
    D.carrier D.regular N
    (solnMetricDeriv (I := I) S hS) hswap p hp t ht x v
  exact h.hasDerivAt (D.regular_mem_nhds ht)






omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solnTowerSwap_of_smooth
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (solnMetricField (I := I) S q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x))
    (hFdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ s ∈ D.carrier, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (covDerivOfField (I := I) gRef (solnMetricField (I := I) S s) p) y
            (fun a : Fin (p + 2) => V a y)) x)
    (hFtdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (covDerivOfField (I := I) gRef (solnEvolField (I := I) S t) p) y
            (fun a : Fin (p + 2) => V a y)) x) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  covDerivOfField_swapReg (I := I) gRef
    (fun r => solnMetricField (I := I) S r)
    (fun t => solnEvolField (I := I) S t)
    D.carrier D.regular D.regular_subset
    (fun ht => D.regular_mem_nhds ht) N
    (solnMetricDeriv (I := I) S hS) hSmooth hFdiff hFtdiff








omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem solnMetricJointAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t : Real} {x : M}
    (hDreg : D.regular ∈ 𝓝 t)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        (solnMetricField (I := I) S q.1) q.2 (fun a : Fin 2 => V a q.2))
      (t, x) := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he
  set b := Module.finBasis Real E with hb
  have hxe : x ∈ e.baseSet := by simp [he]

  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) e b
  have hcompOn := hS.smoothMetric.frameCompSmooth (e.localFrame b) hframe
  have hmemProd : (D.regular ×ˢ e.baseSet : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds hDreg (e.open_baseSet.mem_nhds hxe)
  have hcompAt : ∀ i j, ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        (S.family.metric q.1).inner q.2 (e.localFrame b i q.2) (e.localFrame b j q.2))
      (t, x) := fun i j =>
    (hcompOn i j).contMDiffAt hmemProd

  have hcoeff : ∀ (a : Fin 2) i, ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M => e.localFrame_coeff I b i y ((V a) y)) x := fun a i =>
    _root_.contMDiffAt_localFrame_coeff (I := I) b hxe
      ((V a).contMDiff.contMDiffAt) i

  have hsum : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        ∑ i, ∑ j,
          (e.localFrame_coeff I b i q.2 ((V 0) q.2)) *
            (e.localFrame_coeff I b j q.2 ((V 1) q.2)) *
            (S.family.metric q.1).inner q.2 (e.localFrame b i q.2)
              (e.localFrame b j q.2)) (t, x) := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (((hcoeff 0 i).comp (t, x) contMDiffAt_snd).mul
      ((hcoeff 1 j).comp (t, x) contMDiffAt_snd)).mul (hcompAt i j)

  refine hsum.congr_of_eventuallyEq ?_
  have hev0 := Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul
    (I := I) e b (s := fun y => (V 0) y) hxe
  have hev1 := Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul
    (I := I) e b (s := fun y => (V 1) y) hxe
  have hev : ∀ᶠ q : Real × M in 𝓝 (t, x),
      ((V 0) q.2 = ∑ i, e.localFrame_coeff I b i q.2 ((V 0) q.2) • e.localFrame b i q.2) ∧
      ((V 1) q.2 = ∑ i, e.localFrame_coeff I b i q.2 ((V 1) q.2) • e.localFrame b i q.2) :=
    (continuous_snd.tendsto (t, x)).eventually (hev0.and hev1)
  filter_upwards [hev] with q hq
  have h0 := hq.1
  have h1 := hq.2
  have happ : (solnMetricField (I := I) S q.1) q.2 (fun a : Fin 2 => V a q.2)
      = (S.family.metric q.1).inner q.2 ((V 0) q.2) ((V 1) q.2) :=
    Tensor0SBundle.metricTensorField_apply (I := I) (S.family.metric q.1) q.2 _
  have hexp : (S.family.metric q.1).inner q.2 ((V 0) q.2) ((V 1) q.2)
      = (S.family.metric q.1).inner q.2
          (∑ i, (Trivialization.localFrame_coeff I e b i q.2) ((V 0) q.2)
            • e.localFrame b i q.2)
          (∑ j, (Trivialization.localFrame_coeff I e b j q.2) ((V 1) q.2)
            • e.localFrame b j q.2) := by
    rw [← h0, ← h1]
  rw [happ, hexp]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring






omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solnTowerSwap_of_joint
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (solnMetricField (I := I) S q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x)) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  solnTowerSwap_of_smooth (I := I) gRef S hS N hSmooth
    (fun p _ V s _ x =>
      covDerivOfField_eval_mdiffAt (I := I) gRef (solnMetricField (I := I) S s) p V x)
    (fun p _ V t _ x =>
      covDerivOfField_eval_mdiffAt (I := I) gRef (solnEvolField (I := I) S t) p V x)









omit [SigmaCompactSpace M] in
theorem solnTowerSwap_reg
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hDreg : ∀ {t : Real}, t ∈ D.regular → D.regular ∈ 𝓝 t) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  solnTowerSwap_of_joint (I := I) gRef S hS N
    (fun p _ V _t ht _x =>
      (covDerivOfField_eval_contMDiffAt (I := I) gRef
        (fun r => solnMetricField (I := I) S r)
        (fun W => solnMetricJointAt (I := I) S hS (hDreg ht) W)
        p V).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))

end HCGCompactness
end DifferentialGeometry
