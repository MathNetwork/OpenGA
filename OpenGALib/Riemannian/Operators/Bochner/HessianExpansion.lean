import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Curvature.Tensoriality
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame.Smoothness
import OpenGALib.Riemannian.Util.Metric.MetricInnerSmoothness
import OpenGALib.Util.Notation
import Mathlib.Analysis.InnerProductSpace.Trace
import OpenGALib.Riemannian.Util.CovDeriv.CovDerivBridges

/-!
# Bochner anchor — Hessian expansion of `|∇f|²`

Helpers for `bochner_leibniz_trace_reduction` (intermediate E of the
Bochner–Weitzenböck identity). The first-order identity
$\mathrm{d}(|\nabla f|_g^2)\,v = 2\,\langle \nabla_v \nabla f, \nabla f\rangle_g$
and its second-order specialisations to chart-frame constant lifts and
to smooth vector fields.

Anchor `Bochner.lean` imports this file and feeds the Hessian expansion
into `bochner_leibniz_trace_reduction`, which combines with the Ricci-identity
chain (`Bochner/BochnerExpansion.lean`) to give the final identity.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace Topology

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]
  (g : RiemannianMetric I M)

/-! ## Helpers for the Leibniz trace reduction (E) -/

/-- **Math.** $\mathrm{d}(|\nabla f|_g^2)(y)\,v = 2\,\langle \nabla_v \nabla f,\,\nabla f\rangle_g(y)$.
Metric-compatibility on $(\nabla f, \nabla f)$ plus inner-product symmetry. -/
theorem mfderiv_gradientNormSq_apply
    (f : M → ℝ) (y : M) (v : TangentSpace I y)
    (h_grad_y : TangentSmoothAt (manifoldGradient (I := I) g f) y) :
    mfderiv I 𝓘(ℝ, ℝ) ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) y v
      = 2 * g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y v)
              (manifoldGradient (I := I) g f y) := by
  show mfderiv I 𝓘(ℝ, ℝ)
        (fun z : M => g.metricInner z (manifoldGradient (I := I) g f z)
                                      (manifoldGradient (I := I) g f z)) y v = _
  have hVsm : TangentSmoothAt (fun _ : M => (v : TangentSpace I y)) y :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt y
  -- Bridge metric-compat ∇ → `.toFun` form for the subsequent `rw [h, g.metricInner_comm ...]`.
  have h := leviCivitaConnection_metric_compatible g
    (fun _ : M => (v : TangentSpace I y))
    (manifoldGradient (I := I) g f)
    (manifoldGradient (I := I) g f)
    y hVsm h_grad_y h_grad_y
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h
  -- Cast h to typeclass `g.metricInner` abbrev form for rw matching.
  change ((mfderiv% fun y' => g.metricInner y' (manifoldGradient (I := I) g f y')
              (manifoldGradient (I := I) g f y')) y) v
        = g.metricInner y
            ((leviCivitaConnection (I := I) (M := M) g).toFun
              (manifoldGradient (I := I) g f) y v)
            (manifoldGradient (I := I) g f y)
          + g.metricInner y (manifoldGradient (I := I) g f y)
            ((leviCivitaConnection (I := I) (M := M) g).toFun
              (manifoldGradient (I := I) g f) y v) at h
  rw [h, g.metricInner_comm y (manifoldGradient (I := I) g f y)
       ((leviCivitaConnection (I := I) (M := M) g).toFun
          (manifoldGradient (I := I) g f) y v)]
  -- `covDerivAt g Y x = lcc.toFun Y x` def-eq; close `a + a = 2 * a` via ring after `show`.
  show g.metricInner y
        ((leviCivitaConnection (I := I) (M := M) g).toFun
            (manifoldGradient (I := I) g f) y v)
        (manifoldGradient (I := I) g f y)
      + g.metricInner y
        ((leviCivitaConnection (I := I) (M := M) g).toFun
            (manifoldGradient (I := I) g f) y v)
        (manifoldGradient (I := I) g f y)
      = 2 * g.metricInner y
              ((leviCivitaConnection (I := I) (M := M) g).toFun
                (manifoldGradient (I := I) g f) y v)
              (manifoldGradient (I := I) g f y)
  ring

/-- **Math.** **Section-form Hessian expansion** of $g = |\nabla f|_g^2$
on a smooth vector field $B$:
$$\mathrm{Hess}\,(|\nabla f|^2)(B, B)(x) = 2\bigl(
   \langle (\nabla^2 \nabla f)(B, B),\, \nabla f\rangle_g
   + \|\nabla_B \nabla f\|_g^2\bigr)(x).$$
Section-form analog of `hessian_gradientNormSq_apply_chartFrame`. -/
theorem hessian_gradientNormSq_apply_section
    [IsManifold I 2 M]
    (f : M → ℝ) (B : SmoothVectorField I M) (x : M)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) g f y⟩ : TangentBundle I M))) :
    hessian (I := I) (M := M) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) B.toFun B.toFun x
    = 2 * (g.metricInner x
            (secondCovDerivSection (I := I) (M := M) g              (manifoldGradient (I := I) g f) B.toFun B.toFun x)
            (manifoldGradient (I := I) g f x)
         + g.metricInner x
            (covDeriv g B.toFun (manifoldGradient (I := I) g f) x)
            (covDeriv g B.toFun (manifoldGradient (I := I) g f) x)) := by
  classical
  let gradF : SmoothVectorField I M := ⟨manifoldGradient (I := I) g f, h_grad⟩
  have h_grad_smoothAt : ∀ y, TangentSmoothAt (manifoldGradient (I := I) g f) y :=
    fun y => gradF.smoothAt y
  have hg_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) : M → ℝ) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => g.metricInner y (manifoldGradient (I := I) g f y)
                                (manifoldGradient (I := I) g f y))
    exact g.metricInner_contMDiff h_grad h_grad
  have h_grad_g_cmd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) y⟩
                        : TangentBundle I M)) :=
    Riemannian.manifoldGradient_smooth_of_smooth g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) hg_smooth
  have h_grad_g_smoothAt :
      TangentSmoothAt (manifoldGradient (I := I) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y)))) x :=
    TangentSmoothAt.mk
      (h_grad_g_cmd.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hBsm : TangentSmoothAt B.toFun x := B.smoothAt x
  -- C² gap on ∇f: smoothness of `y ↦ covDerivAt g ∇f y (B y)` at x
  -- (smooth-direction case via `leviCivitaConnection_smoothAt_smoothVF_dir`).
  have hBnf_smooth : TangentSmoothAt
      (fun y : M =>
        (leviCivitaConnection (I := I) (M := M) g).toFun
          (manifoldGradient (I := I) g f) y (B.toFun y)) x :=
    leviCivitaConnection_smoothAt_smoothVF_dir g B gradF x
  -- Level-1 bridge: hessian = iterated mDirDeriv minus Christoffel correction.
  have h_bridge := Riemannian.Operators.hessian_eq_mDirDeriv_iterate_sub_chris g
    ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) B.toFun B.toFun x
    h_grad_g_smoothAt hBsm hBsm
  -- mDirDeriv (|∇f|²) y (B y) = 2 g(∇_{B y} ∇f, ∇f) y (via `mfderiv_gradientNormSq_apply`).
  have h_inner_eq :
      (fun y : M => mDirDeriv (I := I) ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) y (B.toFun y))
        = (fun y : M => 2 * g.metricInner y
                    (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
                    (manifoldGradient (I := I) g f y)) := by
    funext y; exact mfderiv_gradientNormSq_apply g f y (B.toFun y) (h_grad_smoothAt y)
  rw [h_inner_eq] at h_bridge
  -- Christoffel term: mDirDeriv (|∇f|²) x (∇_B B x) = 2 g(∇_{∇_B B x} ∇f, ∇f x).
  have h_chris_term : mDirDeriv (I := I) ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) x
              (covDeriv g B.toFun B.toFun x)
        = 2 * g.metricInner x
              (covDerivAt g (manifoldGradient (I := I) g f) x
                (covDeriv g B.toFun B.toFun x))
              (manifoldGradient (I := I) g f x) :=
    mfderiv_gradientNormSq_apply g f x (covDeriv g B.toFun B.toFun x)
      (h_grad_smoothAt x)
  rw [h_chris_term] at h_bridge
  -- Pull `2` out of the outer mDirDeriv via `const_smul_mfderiv`.
  have h_inner_smooth :
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M => g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
              (manifoldGradient (I := I) g f y)) x :=
    g.metricInner_mdifferentiableAt_of_tangentSmoothAt hBnf_smooth (h_grad_smoothAt x)
  have h_pull_two :
      mDirDeriv (I := I)
          (fun y : M => 2 * g.metricInner y
                  (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
                  (manifoldGradient (I := I) g f y)) x (B.toFun x)
        = 2 * mDirDeriv (I := I)
              (fun y : M => g.metricInner y
                  (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
                  (manifoldGradient (I := I) g f y)) x (B.toFun x) := by
    show mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => 2 * g.metricInner y
            (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
            (manifoldGradient (I := I) g f y)) x (B.toFun x) = _
    have h_smul : (fun y : M => 2 * g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
              (manifoldGradient (I := I) g f y))
            = (2 : ℝ) • (fun y : M => g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
              (manifoldGradient (I := I) g f y)) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [h_smul, const_smul_mfderiv h_inner_smooth (2 : ℝ)]
    rfl
  rw [h_pull_two] at h_bridge
  -- Level-2 metric-compat on (B, ∇_B ∇f, ∇f) at x; converts to covDerivAt g form.
  have h_compat2 := leviCivitaConnection_metric_compatible g
    B.toFun
    (fun y : M =>
      (leviCivitaConnection (I := I) (M := M) g).toFun
        (manifoldGradient (I := I) g f) y (B.toFun y))
    (manifoldGradient (I := I) g f) x hBsm hBnf_smooth (h_grad_smoothAt x)
  change mDirDeriv (I := I)
      (fun y : M => g.metricInner y
        (covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
        (manifoldGradient (I := I) g f y)) x (B.toFun x)
      = g.metricInner x
          (covDerivAt g
            (fun y : M =>
              covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
            x (B.toFun x))
          (manifoldGradient (I := I) g f x)
        + g.metricInner x
            (covDerivAt g (manifoldGradient (I := I) g f) x (B.toFun x))
            (covDerivAt g (manifoldGradient (I := I) g f) x (B.toFun x))
        at h_compat2
  rw [h_compat2] at h_bridge
  -- Connect to `secondCovDerivSection`: `(∇^2 ∇f)(B, B) x = ∇_B (∇_B ∇f) x - ∇_{∇_B B x} ∇f`.
  have h_secondCDS :
      g.metricInner x
          (secondCovDerivSection (I := I) (M := M) g            (manifoldGradient (I := I) g f) B.toFun B.toFun x)
          (manifoldGradient (I := I) g f x)
        = g.metricInner x
            (covDerivAt g
              (fun y : M =>
                covDerivAt g (manifoldGradient (I := I) g f) y (B.toFun y))
              x (B.toFun x))
            (manifoldGradient (I := I) g f x)
          - g.metricInner x
              (covDerivAt g (manifoldGradient (I := I) g f) x
                (covDeriv g B.toFun B.toFun x))
              (manifoldGradient (I := I) g f x) := by
    unfold secondCovDerivSection
    rw [g.metricInner_sub_left]
    rfl
  -- `covDeriv g B.toFun ∇f x = covDerivAt g ∇f x (B x)` (def).
  have h_covDeriv_eq :
      covDeriv g B.toFun (manifoldGradient (I := I) g f) x
        = covDerivAt g (manifoldGradient (I := I) g f) x (B.toFun x) := rfl
  -- Combine: linearly relate `h_bridge` to the goal.
  rw [h_covDeriv_eq]
  linarith [h_bridge, h_secondCDS]

/-- **Math.** Per-direction Hessian expansion of $g = |\nabla f|_g^2$ on a
chart-frame constant section $v$:
$$\mathrm{Hess}\,g(v, v)(x) = 2\bigl(\langle (\nabla^2 \nabla f)(v, v), \nabla f\rangle_g
   + \|(\nabla_v \nabla f)\|_g^2\bigr)(x).$$
Combines `hessian_eq_mDirDeriv_iterate_sub_chris`,
`mfderiv_gradientNormSq_apply`, and a level-2 metric-compat. -/
theorem hessian_gradientNormSq_apply_chartFrame
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M) (v : TangentSpace I x)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) g f y⟩ : TangentBundle I M))) :
    hessian (I := I) (M := M) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y)))
        (fun _ : M => (v : TangentSpace I x))
        (fun _ : M => (v : TangentSpace I x)) x
    = 2 * (g.metricInner x
            (secondCovDerivAt (I := I) (M := M) g              (manifoldGradient (I := I) g f) x v v)
            (manifoldGradient (I := I) g f x)
         + g.metricInner x
            (covDerivAt g (manifoldGradient (I := I) g f) x v)
            (covDerivAt g (manifoldGradient (I := I) g f) x v)) := by
  let gradSV : SmoothVectorField I M := ⟨manifoldGradient (I := I) g f, h_grad⟩
  have h_grad_smoothAt : ∀ y, TangentSmoothAt (manifoldGradient (I := I) g f) y :=
    fun y => gradSV.smoothAt y
  have hg_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) : M → ℝ) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => g.metricInner y (manifoldGradient (I := I) g f y)
                                (manifoldGradient (I := I) g f y))
    exact g.metricInner_contMDiff h_grad h_grad
  have h_grad_g_cmd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) y⟩
                        : TangentBundle I M)) :=
    Riemannian.manifoldGradient_smooth_of_smooth g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) hg_smooth
  have h_grad_g_smoothAt :
      TangentSmoothAt (manifoldGradient (I := I) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y)))) x :=
    TangentSmoothAt.mk
      (h_grad_g_cmd.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hVsm : TangentSmoothAt (fun _ : M => (v : TangentSpace I x)) x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  -- C² gap on ∇f: smoothness of `y ↦ covDerivAt g ∇f y v` at x.
  have hSvsm : TangentSmoothAt
      (fun y : M =>
        (leviCivitaConnection (I := I) (M := M) g).toFun
          (manifoldGradient (I := I) g f) y (v : TangentSpace I x)) x :=
    leviCivitaConnection_smoothAt_smoothVF_dir g
      (SmoothVectorField.const (I := I) (M := M) (v : E)) gradSV x
  have h_bridge := Riemannian.Operators.hessian_eq_mDirDeriv_iterate_sub_chris g
    ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) (fun _ : M => (v : TangentSpace I x))
    (fun _ : M => (v : TangentSpace I x)) x
    h_grad_g_smoothAt hVsm hVsm
  have h_inner_eq :
      (fun y : M => mDirDeriv (I := I) ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) y (v : TangentSpace I x))
        = (fun y : M => 2 * g.metricInner y
                    (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
                    (manifoldGradient (I := I) g f y)) := by
    funext y; exact mfderiv_gradientNormSq_apply g f y v (h_grad_smoothAt y)
  rw [h_inner_eq] at h_bridge
  have h_chris_term : mDirDeriv (I := I) ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y))) x
              (covDeriv g (fun _ : M => (v : TangentSpace I x))
                        (fun _ : M => (v : TangentSpace I x)) x)
        = 2 * g.metricInner x
              (covDerivAt g (manifoldGradient (I := I) g f) x
                (covDeriv g (fun _ : M => (v : TangentSpace I x))
                          (fun _ : M => (v : TangentSpace I x)) x))
              (manifoldGradient (I := I) g f x) :=
    mfderiv_gradientNormSq_apply g f x
      (covDeriv g (fun _ : M => (v : TangentSpace I x))
                (fun _ : M => (v : TangentSpace I x)) x)
      (h_grad_smoothAt x)
  rw [h_chris_term] at h_bridge
  have h_inner_smooth :
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M => g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) g f y)) x :=
    g.metricInner_mdifferentiableAt_of_tangentSmoothAt hSvsm (h_grad_smoothAt x)
  -- Pull `2` out of the iterated `mDirDeriv` via `const_smul_mfderiv`.
  have h_pull_two :
      mDirDeriv (I := I)
          (fun y : M => 2 * g.metricInner y
                  (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
                  (manifoldGradient (I := I) g f y)) x v
        = 2 * mDirDeriv (I := I)
              (fun y : M => g.metricInner y
                  (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
                  (manifoldGradient (I := I) g f y)) x v := by
    show mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => 2 * g.metricInner y
            (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
            (manifoldGradient (I := I) g f y)) x v = _
    have h_smul : (fun y : M => 2 * g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) g f y))
            = (2 : ℝ) • (fun y : M => g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) g f y)) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [h_smul, const_smul_mfderiv h_inner_smooth (2 : ℝ)]
    show (2 : ℝ) • (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => g.metricInner y
            (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
            (manifoldGradient (I := I) g f y)) x) v
        = 2 * mDirDeriv (I := I) (fun y : M => g.metricInner y
              (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) g f y)) x v
    rfl
  rw [h_pull_two] at h_bridge
  -- Level-2 metric-compat on (const v, S_v, ∇f); convert lcc.toFun to covDerivAt g
  -- (def-eq) at h_compat2 to match h_bridge's pattern.
  have h_compat2 := leviCivitaConnection_metric_compatible g
    (fun _ : M => (v : TangentSpace I x))
    (fun y : M =>
      (leviCivitaConnection (I := I) (M := M) g).toFun
        (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
    (manifoldGradient (I := I) g f) x hVsm hSvsm (h_grad_smoothAt x)
  change mDirDeriv (I := I)
      (fun y : M => g.metricInner y
        (covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
        (manifoldGradient (I := I) g f y)) x v
      = g.metricInner x
          (covDerivAt g
            (fun y : M =>
              covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x)) x
            (v : TangentSpace I x))
          (manifoldGradient (I := I) g f x)
        + g.metricInner x
            (covDerivAt g (manifoldGradient (I := I) g f) x (v : TangentSpace I x))
            (covDerivAt g (manifoldGradient (I := I) g f) x (v : TangentSpace I x))
        at h_compat2
  rw [h_compat2] at h_bridge
  -- Normalize `(∇[const v] const v) x` notation to `covDerivAt g (const v) x v` (def-eq)
  -- to match the `secondCovDerivAt_def` unfolding.
  change hessian (I := I) (M := M) g ((fun y => g.metricInner y (manifoldGradient (I := I) g f y) (manifoldGradient (I := I) g f y)))
        (fun _ : M => (v : TangentSpace I x))
        (fun _ : M => (v : TangentSpace I x)) x =
      2 * (g.metricInner x
              (covDerivAt g
                (fun y : M =>
                  covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
                x (v : TangentSpace I x))
              (manifoldGradient (I := I) g f x)
            + g.metricInner x
                (covDerivAt g (manifoldGradient (I := I) g f) x (v : TangentSpace I x))
                (covDerivAt g (manifoldGradient (I := I) g f) x (v : TangentSpace I x)))
        - 2 * g.metricInner x
              (covDerivAt g (manifoldGradient (I := I) g f) x
                (covDerivAt g (fun _ : M => (v : TangentSpace I x)) x
                  (v : TangentSpace I x)))
              (manifoldGradient (I := I) g f x) at h_bridge
  rw [h_bridge]
  have h_secondCD :
      g.metricInner x
          (secondCovDerivAt (I := I) (M := M) g            (manifoldGradient (I := I) g f) x v v)
          (manifoldGradient (I := I) g f x)
        = g.metricInner x
            (covDerivAt g
              (fun y : M =>
                covDerivAt g (manifoldGradient (I := I) g f) y (v : TangentSpace I x))
              x (v : TangentSpace I x))
            (manifoldGradient (I := I) g f x)
          - g.metricInner x
              (covDerivAt g (manifoldGradient (I := I) g f) x
                (covDerivAt g (fun _ : M => (v : TangentSpace I x)) x
                  (v : TangentSpace I x)))
              (manifoldGradient (I := I) g f x) := by
    rw [secondCovDerivAt_def, g.metricInner_sub_left]
  linarith [h_secondCD]


end Operators
end Riemannian

end
