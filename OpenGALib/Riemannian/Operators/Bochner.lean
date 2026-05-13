import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Curvature.Tensoriality
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.Tensor.SmoothOrthoFrame
import OpenGALib.Util.Notation
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Bochner–Weitzenböck identity

For a smooth scalar $f : M \to \mathbb{R}$ on a Riemannian manifold $(M, g)$:
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f,\, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f,\, \nabla f).$$

Reference: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33;
do Carmo §6 (curvature commutators); Schoen-Simon 1981 §1 (variational
application).
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

/-! ## `mfderiv` distribution over `Finset.sum` -/

/-- **`mfderiv` distributes over `Finset.sum`** (evaluated at a tangent vector):
for a finite family of scalar functions `g : ι → M → ℝ` each
`MDifferentiableAt` at `x`,
$$\mathrm{d}\Bigl(\sum_{i \in s} g_i\Bigr)(x)(v)
   \;=\; \sum_{i \in s} \mathrm{d}(g_i)(x)(v).$$

Direct application of Mathlib's `HasMFDerivAt.sum` (which combines per-summand
`HasMFDerivAt` witnesses additively); `.mfderiv` extraction lifts the
section-level equality of CLMs to evaluation at `v`. -/
theorem mfderiv_finset_sum_apply
    {ι : Type} (s : Finset ι) (g : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (hg : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (g i) x) :
    (mfderiv I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x v : ℝ)
      = ∑ i ∈ s, (mfderiv I 𝓘(ℝ, ℝ) (g i) x v : ℝ) := by
  classical
  have h : HasMFDerivAt I 𝓘(ℝ, ℝ) (∑ i ∈ s, g i) x
      (∑ i ∈ s, mfderiv I 𝓘(ℝ, ℝ) (g i) x) :=
    HasMFDerivAt.sum (fun i hi => (hg i hi).hasMFDerivAt)
  have h' : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x
      (∑ i ∈ s, mfderiv I 𝓘(ℝ, ℝ) (g i) x) := by
    convert h using 1
    funext y
    exact (Finset.sum_apply y s g).symm
  rw [h'.mfderiv]
  -- `(∑ i, F i) v = ∑ i, F i v` via Mathlib `ContinuousLinearMap.sum_apply`.
  exact ContinuousLinearMap.sum_apply s _ v

/-! ## Building block: Ricci as g-orthonormal trace -/

/-- **F — Ricci as a g-orthonormal trace** (`ricciTensor` unwound via
`LinearMap.trace_eq_sum_inner`):
$$\mathrm{Ric}_g(V, W)(x) \;=\; \sum_i \bigl\langle \varepsilon_i,\,
  R(\varepsilon_i,\,V)\,W\,(x)\bigr\rangle_g,$$
where $\{\varepsilon_i\} = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,(T_xM)$
and $R$ is the Riemann curvature tensor with the standard sign convention.

The proof is `ricciTensor` def + `ricci` def + Mathlib's
`LinearMap.trace_eq_sum_inner` on the curvature endomorphism. The
$g$-orthonormal structure on $T_xM$ comes from
`instRiemannianBundleOfHasMetric` (the "single NACG/IPS source") under
`[HasMetric I M]`. -/
theorem ricciTensor_eq_sum_inner_orthonormal
    [IsManifold I 2 M]
    (x : M) (V W : TangentSpace I x) :
    Ric_g(V, W) x =
      ∑ i, ⟪(stdOrthonormalBasis ℝ (TangentSpace I x)) i,
            curvatureEndo
              (SmoothVectorField.const (I := I) (M := M) V)
              (SmoothVectorField.const (I := I) (M := M) W) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)⟫_ℝ := by
  show ricci (SmoothVectorField.const (I := I) (M := M) V)
        (SmoothVectorField.const (I := I) (M := M) W) x = _
  unfold ricci
  exact LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TangentSpace I x))

/-! ## Helpers for the Leibniz trace reduction (E) -/

/-- $\mathrm{d}(|\nabla f|_g^2)(y)\,v = 2\,\langle \nabla_v \nabla f,\,\nabla f\rangle_g(y)$.
Level-1 metric-compatibility on $(\nabla f,\, \nabla f)$ plus inner-product symmetry. -/
theorem mfderiv_gradientNormSq_apply
    (f : M → ℝ) (y : M) (v : TangentSpace I y)
    (h_grad_y : TangentSmoothAt (manifoldGradient (I := I) f) y) :
    mfderiv I 𝓘(ℝ, ℝ) (‖grad_g[I] f‖²_g) y v
      = 2 * metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y v)
              (manifoldGradient (I := I) f y) := by
  show mfderiv I 𝓘(ℝ, ℝ)
        (fun z : M => metricInner z (manifoldGradient (I := I) f z)
                                      (manifoldGradient (I := I) f z)) y v = _
  have hVsm : TangentSmoothAt (fun _ : M => (v : TangentSpace I y)) y :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt y
  have h := leviCivitaConnection_metric_compatible
    (fun _ : M => (v : TangentSpace I y))
    (manifoldGradient (I := I) f)
    (manifoldGradient (I := I) f)
    y hVsm h_grad_y h_grad_y
  rw [h, metricInner_comm y (manifoldGradient (I := I) f y)
       ((leviCivitaConnection (I := I) (M := M)).toFun
          (manifoldGradient (I := I) f) y v)]
  -- `covDerivAt Y x = lcc.toFun Y x` def-eq; close `a + a = 2 * a` via ring after `show`.
  show metricInner y
        ((leviCivitaConnection (I := I) (M := M)).toFun
            (manifoldGradient (I := I) f) y v)
        (manifoldGradient (I := I) f y)
      + metricInner y
        ((leviCivitaConnection (I := I) (M := M)).toFun
            (manifoldGradient (I := I) f) y v)
        (manifoldGradient (I := I) f y)
      = 2 * metricInner y
              ((leviCivitaConnection (I := I) (M := M)).toFun
                (manifoldGradient (I := I) f) y v)
              (manifoldGradient (I := I) f y)
  ring

/-- **Section-form Hessian expansion** of $g = |\nabla f|_g^2$ on a smooth
vector field $B$ (replacing the chart-frame constant section):
$$\mathrm{Hess}\,(|\nabla f|^2)(B, B)(x) = 2\bigl(
   \langle (\nabla^2 \nabla f)(B, B),\, \nabla f\rangle_g
   + \|\nabla_B \nabla f\|_g^2\bigr)(x).$$

This is the section-form analog of `hessian_gradientNormSq_apply_chartFrame`,
producing `secondCovDerivSection` (matching the section-form output of
`bochner_per_summand_assembled`). The proof is via section-level
metric-compatibility on $(B, \nabla_B \nabla f, \nabla f)$ at $x$.

Used in the section-form `leibniz_trace_reduction`. -/
private theorem hessian_gradientNormSq_apply_section
    [IsManifold I 2 M]
    (f : M → ℝ) (B : SmoothVectorField I M) (x : M)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    hessian (I := I) (M := M) (‖grad_g[I] f‖²_g) B.toFun B.toFun x
    = 2 * (metricInner x
            (secondCovDerivSection (I := I) (M := M)
              (manifoldGradient (I := I) f) B.toFun B.toFun x)
            (manifoldGradient (I := I) f x)
         + metricInner x
            (covDeriv B.toFun (manifoldGradient (I := I) f) x)
            (covDeriv B.toFun (manifoldGradient (I := I) f) x)) := by
  classical
  let gradF : SmoothVectorField I M := ⟨manifoldGradient (I := I) f, h_grad⟩
  have h_grad_smoothAt : ∀ y, TangentSmoothAt (manifoldGradient (I := I) f) y :=
    fun y => gradF.smoothAt y
  have hg_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ((‖grad_g[I] f‖²_g) : M → ℝ) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => metricInner y (manifoldGradient (I := I) f y)
                                (manifoldGradient (I := I) f y))
    exact metricInner_contMDiff h_grad h_grad
  have h_grad_g_cmd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) (‖grad_g[I] f‖²_g) y⟩
                        : TangentBundle I M)) :=
    Riemannian.manifoldGradient_smooth_of_smooth (‖grad_g[I] f‖²_g) hg_smooth
  have h_grad_g_smoothAt :
      TangentSmoothAt (manifoldGradient (I := I) (‖grad_g[I] f‖²_g)) x :=
    TangentSmoothAt.mk
      (h_grad_g_cmd.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hBsm : TangentSmoothAt B.toFun x := B.smoothAt x
  -- C² gap on ∇f: smoothness of `y ↦ covDerivAt ∇f y (B y)` at x
  -- (smooth-direction case via `leviCivitaConnection_smoothAt_smoothVF_dir`).
  have hBnf_smooth : TangentSmoothAt
      (fun y : M =>
        (leviCivitaConnection (I := I) (M := M)).toFun
          (manifoldGradient (I := I) f) y (B.toFun y)) x :=
    leviCivitaConnection_smoothAt_smoothVF_dir B gradF x
  -- Level-1 bridge: hessian = iterated mDirDeriv minus Christoffel correction.
  have h_bridge := Riemannian.Operators.hessian_eq_mDirDeriv_iterate_sub_chris
    (‖grad_g[I] f‖²_g) B.toFun B.toFun x
    h_grad_g_smoothAt hBsm hBsm
  -- mDirDeriv (|∇f|²) y (B y) = 2 g(∇_{B y} ∇f, ∇f) y (via `mfderiv_gradientNormSq_apply`).
  have h_inner_eq :
      (fun y : M => mDirDeriv (I := I) (‖grad_g[I] f‖²_g) y (B.toFun y))
        = (fun y : M => 2 * metricInner y
                    (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
                    (manifoldGradient (I := I) f y)) := by
    funext y; exact mfderiv_gradientNormSq_apply f y (B.toFun y) (h_grad_smoothAt y)
  rw [h_inner_eq] at h_bridge
  -- Christoffel term: mDirDeriv (|∇f|²) x (∇_B B x) = 2 g(∇_{∇_B B x} ∇f, ∇f x).
  have h_chris_term : mDirDeriv (I := I) (‖grad_g[I] f‖²_g) x
              (covDeriv B.toFun B.toFun x)
        = 2 * metricInner x
              (covDerivAt (manifoldGradient (I := I) f) x
                (covDeriv B.toFun B.toFun x))
              (manifoldGradient (I := I) f x) :=
    mfderiv_gradientNormSq_apply f x (covDeriv B.toFun B.toFun x)
      (h_grad_smoothAt x)
  rw [h_chris_term] at h_bridge
  -- Pull `2` out of the outer mDirDeriv via `const_smul_mfderiv`.
  have h_inner_smooth :
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
              (manifoldGradient (I := I) f y)) x :=
    metricInner_mdifferentiableAt_of_tangentSmoothAt hBnf_smooth (h_grad_smoothAt x)
  have h_pull_two :
      mDirDeriv (I := I)
          (fun y : M => 2 * metricInner y
                  (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
                  (manifoldGradient (I := I) f y)) x (B.toFun x)
        = 2 * mDirDeriv (I := I)
              (fun y : M => metricInner y
                  (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
                  (manifoldGradient (I := I) f y)) x (B.toFun x) := by
    show mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => 2 * metricInner y
            (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
            (manifoldGradient (I := I) f y)) x (B.toFun x) = _
    have h_smul : (fun y : M => 2 * metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
              (manifoldGradient (I := I) f y))
            = (2 : ℝ) • (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
              (manifoldGradient (I := I) f y)) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [h_smul, const_smul_mfderiv h_inner_smooth (2 : ℝ)]
    rfl
  rw [h_pull_two] at h_bridge
  -- Level-2 metric-compat on (B, ∇_B ∇f, ∇f) at x; converts to covDerivAt form.
  have h_compat2 := leviCivitaConnection_metric_compatible
    B.toFun
    (fun y : M =>
      (leviCivitaConnection (I := I) (M := M)).toFun
        (manifoldGradient (I := I) f) y (B.toFun y))
    (manifoldGradient (I := I) f) x hBsm hBnf_smooth (h_grad_smoothAt x)
  change mDirDeriv (I := I)
      (fun y : M => metricInner y
        (covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
        (manifoldGradient (I := I) f y)) x (B.toFun x)
      = metricInner x
          (covDerivAt
            (fun y : M =>
              covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
            x (B.toFun x))
          (manifoldGradient (I := I) f x)
        + metricInner x
            (covDerivAt (manifoldGradient (I := I) f) x (B.toFun x))
            (covDerivAt (manifoldGradient (I := I) f) x (B.toFun x))
        at h_compat2
  rw [h_compat2] at h_bridge
  -- Connect to `secondCovDerivSection`: `(∇^2 ∇f)(B, B) x = ∇_B (∇_B ∇f) x - ∇_{∇_B B x} ∇f`.
  have h_secondCDS :
      metricInner x
          (secondCovDerivSection (I := I) (M := M)
            (manifoldGradient (I := I) f) B.toFun B.toFun x)
          (manifoldGradient (I := I) f x)
        = metricInner x
            (covDerivAt
              (fun y : M =>
                covDerivAt (manifoldGradient (I := I) f) y (B.toFun y))
              x (B.toFun x))
            (manifoldGradient (I := I) f x)
          - metricInner x
              (covDerivAt (manifoldGradient (I := I) f) x
                (covDeriv B.toFun B.toFun x))
              (manifoldGradient (I := I) f x) := by
    unfold secondCovDerivSection
    rw [metricInner_sub_left]
    rfl
  -- `covDeriv B.toFun ∇f x = covDerivAt ∇f x (B x)` (def).
  have h_covDeriv_eq :
      covDeriv B.toFun (manifoldGradient (I := I) f) x
        = covDerivAt (manifoldGradient (I := I) f) x (B.toFun x) := rfl
  -- Combine: linearly relate `h_bridge` to the goal.
  rw [h_covDeriv_eq]
  linarith [h_bridge, h_secondCDS]

/-- Per-direction Hessian expansion of $g = |\nabla f|_g^2$ on a chart-frame
constant section $v$:
$$\mathrm{Hess}\,g(v, v)(x) = 2\bigl(\langle (\nabla^2 \nabla f)(v, v), \nabla f\rangle_g
   + \|(\nabla_v \nabla f)\|_g^2\bigr)(x).$$

Combines (i) `hessian_eq_mDirDeriv_iterate_sub_chris` to bridge into iterated
`mDirDeriv`, (ii) `mfderiv_gradientNormSq_apply` for the level-1 unfolding,
and (iii) a level-2 metric-compat on $(v_\text{const}, \nabla_v \nabla f, \nabla f)$
— the C² gap on $\nabla f$ is discharged via
`leviCivitaConnection_smoothAt_const_dir` on the `SmoothVectorField` wrapper
constructed from `h_grad`. -/
private theorem hessian_gradientNormSq_apply_chartFrame
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M) (v : TangentSpace I x)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
        (fun _ : M => (v : TangentSpace I x))
        (fun _ : M => (v : TangentSpace I x)) x
    = 2 * (metricInner x
            (secondCovDerivAt (I := I) (M := M)
              (manifoldGradient (I := I) f) x v v)
            (manifoldGradient (I := I) f x)
         + metricInner x
            (covDerivAt (manifoldGradient (I := I) f) x v)
            (covDerivAt (manifoldGradient (I := I) f) x v)) := by
  let gradSV : SmoothVectorField I M := ⟨manifoldGradient (I := I) f, h_grad⟩
  have h_grad_smoothAt : ∀ y, TangentSmoothAt (manifoldGradient (I := I) f) y :=
    fun y => gradSV.smoothAt y
  have hg_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ((‖grad_g[I] f‖²_g) : M → ℝ) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => metricInner y (manifoldGradient (I := I) f y)
                                (manifoldGradient (I := I) f y))
    exact metricInner_contMDiff h_grad h_grad
  have h_grad_g_cmd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) (‖grad_g[I] f‖²_g) y⟩
                        : TangentBundle I M)) :=
    Riemannian.manifoldGradient_smooth_of_smooth (‖grad_g[I] f‖²_g) hg_smooth
  have h_grad_g_smoothAt :
      TangentSmoothAt (manifoldGradient (I := I) (‖grad_g[I] f‖²_g)) x :=
    TangentSmoothAt.mk
      (h_grad_g_cmd.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hVsm : TangentSmoothAt (fun _ : M => (v : TangentSpace I x)) x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  -- C² gap on ∇f: smoothness of `y ↦ covDerivAt ∇f y v` at x.
  have hSvsm : TangentSmoothAt
      (fun y : M =>
        (leviCivitaConnection (I := I) (M := M)).toFun
          (manifoldGradient (I := I) f) y (v : TangentSpace I x)) x :=
    leviCivitaConnection_smoothAt_const_dir gradSV (v : E) x
  have h_bridge := Riemannian.Operators.hessian_eq_mDirDeriv_iterate_sub_chris
    (‖grad_g[I] f‖²_g) (fun _ : M => (v : TangentSpace I x))
    (fun _ : M => (v : TangentSpace I x)) x
    h_grad_g_smoothAt hVsm hVsm
  have h_inner_eq :
      (fun y : M => mDirDeriv (I := I) (‖grad_g[I] f‖²_g) y (v : TangentSpace I x))
        = (fun y : M => 2 * metricInner y
                    (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
                    (manifoldGradient (I := I) f y)) := by
    funext y; exact mfderiv_gradientNormSq_apply f y v (h_grad_smoothAt y)
  rw [h_inner_eq] at h_bridge
  have h_chris_term : mDirDeriv (I := I) (‖grad_g[I] f‖²_g) x
              (covDeriv (fun _ : M => (v : TangentSpace I x))
                        (fun _ : M => (v : TangentSpace I x)) x)
        = 2 * metricInner x
              (covDerivAt (manifoldGradient (I := I) f) x
                (covDeriv (fun _ : M => (v : TangentSpace I x))
                          (fun _ : M => (v : TangentSpace I x)) x))
              (manifoldGradient (I := I) f x) :=
    mfderiv_gradientNormSq_apply f x
      (covDeriv (fun _ : M => (v : TangentSpace I x))
                (fun _ : M => (v : TangentSpace I x)) x)
      (h_grad_smoothAt x)
  rw [h_chris_term] at h_bridge
  have h_inner_smooth :
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) f y)) x :=
    metricInner_mdifferentiableAt_of_tangentSmoothAt hSvsm (h_grad_smoothAt x)
  -- Pull `2` out of the iterated `mDirDeriv` via `const_smul_mfderiv`.
  have h_pull_two :
      mDirDeriv (I := I)
          (fun y : M => 2 * metricInner y
                  (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
                  (manifoldGradient (I := I) f y)) x v
        = 2 * mDirDeriv (I := I)
              (fun y : M => metricInner y
                  (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
                  (manifoldGradient (I := I) f y)) x v := by
    show mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => 2 * metricInner y
            (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
            (manifoldGradient (I := I) f y)) x v = _
    have h_smul : (fun y : M => 2 * metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) f y))
            = (2 : ℝ) • (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) f y)) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [h_smul, const_smul_mfderiv h_inner_smooth (2 : ℝ)]
    show (2 : ℝ) • (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => metricInner y
            (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
            (manifoldGradient (I := I) f y)) x) v
        = 2 * mDirDeriv (I := I) (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) f y)) x v
    rfl
  rw [h_pull_two] at h_bridge
  -- Level-2 metric-compat on (const v, S_v, ∇f); convert lcc.toFun to covDerivAt
  -- (def-eq) at h_compat2 to match h_bridge's pattern.
  have h_compat2 := leviCivitaConnection_metric_compatible
    (fun _ : M => (v : TangentSpace I x))
    (fun y : M =>
      (leviCivitaConnection (I := I) (M := M)).toFun
        (manifoldGradient (I := I) f) y (v : TangentSpace I x))
    (manifoldGradient (I := I) f) x hVsm hSvsm (h_grad_smoothAt x)
  change mDirDeriv (I := I)
      (fun y : M => metricInner y
        (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
        (manifoldGradient (I := I) f y)) x v
      = metricInner x
          (covDerivAt
            (fun y : M =>
              covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x)) x
            (v : TangentSpace I x))
          (manifoldGradient (I := I) f x)
        + metricInner x
            (covDerivAt (manifoldGradient (I := I) f) x (v : TangentSpace I x))
            (covDerivAt (manifoldGradient (I := I) f) x (v : TangentSpace I x))
        at h_compat2
  rw [h_compat2] at h_bridge
  -- Normalize `(∇[const v] const v) x` notation to `covDerivAt (const v) x v` (def-eq)
  -- to match the `secondCovDerivAt_def` unfolding.
  change hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
        (fun _ : M => (v : TangentSpace I x))
        (fun _ : M => (v : TangentSpace I x)) x =
      2 * (metricInner x
              (covDerivAt
                (fun y : M =>
                  covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
                x (v : TangentSpace I x))
              (manifoldGradient (I := I) f x)
            + metricInner x
                (covDerivAt (manifoldGradient (I := I) f) x (v : TangentSpace I x))
                (covDerivAt (manifoldGradient (I := I) f) x (v : TangentSpace I x)))
        - 2 * metricInner x
              (covDerivAt (manifoldGradient (I := I) f) x
                (covDerivAt (fun _ : M => (v : TangentSpace I x)) x
                  (v : TangentSpace I x)))
              (manifoldGradient (I := I) f x) at h_bridge
  rw [h_bridge]
  have h_secondCD :
      metricInner x
          (secondCovDerivAt (I := I) (M := M)
            (manifoldGradient (I := I) f) x v v)
          (manifoldGradient (I := I) f x)
        = metricInner x
            (covDerivAt
              (fun y : M =>
                covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              x (v : TangentSpace I x))
            (manifoldGradient (I := I) f x)
          - metricInner x
              (covDerivAt (manifoldGradient (I := I) f) x
                (covDerivAt (fun _ : M => (v : TangentSpace I x)) x
                  (v : TangentSpace I x)))
              (manifoldGradient (I := I) f x) := by
    rw [secondCovDerivAt_def, metricInner_sub_left]
  linarith [h_secondCD]

/-! ## `connectionLaplacian` (section-form definition)

Following Mathlib LC PR #36845 (Massot/Rothgang/Macbeth) and the external
`differential-geometry` library, the connection Laplacian is defined in
**section form** using the smooth $g$-orthonormal frame
`smoothOrthoFrame g α` (Gram-Schmidt of chart frame, centered at the
evaluation point $\alpha$).

Section form avoids the Hom-bundle Leibniz bridge between section and
constant forms, which is technically blocked by Lean's
`TangentSpace I x = E` non-reducibility (the same infrastructure issue
Mathlib LC PR works around with `set_option backward.isDefEq.respectTransparency false`).
With section form, the trace identifies directly with the section-form
output of `bochner_per_summand_assembled`, eliminating the bridge entirely. -/

/-- **Connection Laplacian** $\Delta_\nabla Z$ on a tangent vector field
$Z : \Pi x : M, T_x M$, computed against the smooth $g$-orthonormal frame
`smoothOrthoFrame g α` centered at the evaluation point $\alpha$:
$$(\Delta_\nabla Z)(\alpha) \;=\; \sum_i (\nabla^2 Z)(B_i, B_i)(\alpha),$$
where $B_i := \mathrm{smoothOrthoFrame}\,g\,\alpha\,i$ is the $i$-th smooth
$g$-orthonormal-at-$\alpha$ frame section.

**Ground truth**: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33
(Bochner identity); do Carmo §6 ex. 12. -/
noncomputable def connectionLaplacian
    (Z : Π x : M, TangentSpace I x) (α : M) : TangentSpace I α :=
  ∑ i, Riemannian.Operators.secondCovDerivSection (I := I) (M := M) Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α

/-- Definitional unfolding of `connectionLaplacian` as the section-form
trace of $\nabla^2 Z$ along `smoothOrthoFrame g α`. -/
@[simp] lemma connectionLaplacian_def
    (Z : Π x : M, TangentSpace I x) (α : M) :
    connectionLaplacian (I := I) (M := M) Z α =
      ∑ i, Riemannian.Operators.secondCovDerivSection (I := I) (M := M) Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α :=
  rfl

/-- The connection Laplacian on the zero vector field is zero. -/
@[simp] theorem connectionLaplacian_zero (α : M) :
    connectionLaplacian (I := I) (M := M)
        (0 : Π x : M, TangentSpace I x) α = 0 := by
  rw [connectionLaplacian_def]
  refine Finset.sum_eq_zero ?_
  intro i _
  show secondCovDerivSection (I := I) (M := M)
        (0 : Π x : M, TangentSpace I x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α = 0
  unfold secondCovDerivSection
  have h_inner_zero : ∀ y v, covDerivAt (0 : Π x : M, TangentSpace I x) y v = 0 := by
    intro y v
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 y) v = 0
    rw [CovariantDerivative.zero]; rfl
  have h_section_zero : (fun y : M => covDerivAt (0 : Π x : M, TangentSpace I x) y
        ((Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) y))
      = (0 : Π y : M, TangentSpace I y) := by
    funext y; exact h_inner_zero y _
  rw [h_section_zero]
  show ((leviCivitaConnection (I := I) (M := M)).toFun 0 α) _
        - ((leviCivitaConnection (I := I) (M := M)).toFun 0 α) _ = 0
  rw [CovariantDerivative.zero]
  show (0 : TangentSpace I α →L[ℝ] TangentSpace I α) _
      - (0 : TangentSpace I α →L[ℝ] TangentSpace I α) _ = 0
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, sub_zero]

/-! ## Two intermediates (E, G) for the Bochner identity -/

/-- **E — Leibniz trace reduction**: the scalar Laplacian of $|\nabla f|_g^2$
decomposes into a connection-Laplacian term and a Hessian Frobenius² term:
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2 \;=\;
   \langle \Delta_\nabla \nabla f,\, \nabla f \rangle_g
   + |\nabla^2 f|_g^2.$$

Combines `hessian_gradientNormSq_apply_chartFrame` (per-direction Leibniz
expansion) summed over `stdOrthonormalBasis ℝ (TangentSpace I x)`,
with `connectionLaplacian_eq_sum_secondCovDerivAt` for the trace identification
and `OrthonormalBasis.sum_sq_inner_left` for the Hessian Frobenius²
identification (orthonormal basis decomposition of $\|\nabla_{\varepsilon_i}
\nabla f\|_g^2$).

Used in `bochner_weitzenboeck` (assembly step H) along with G. -/
theorem leibniz_trace_reduction
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
      = ⟪connectionLaplacian (grad_g[I] f) x, (grad_g[I] f) x⟫_g
        + ‖hess_g[I] f‖²_g x := by
  classical
  show (1 / 2 : ℝ) * Operators.scalarLaplacian (I := I) (M := M) (‖grad_g[I] f‖²_g) x
      = metricInner x
          (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
          (manifoldGradient (I := I) f x)
        + frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
  -- Wrap `smoothOrthoFrame · x i` as `SmoothVectorField` for `hessian_gradientNormSq_apply_section`.
  let Bi : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i
      smooth := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i }
  -- Step 1: convert `scalarLaplacian` from std-basis trace to smoothOrthoFrame trace
  -- via Stage 7 basis-invariance of trace (`sum_diagonal_smoothOrthoFrame_eq_std`).
  have h_scalarLap_eq :
      Operators.scalarLaplacian (I := I) (M := M) (‖grad_g[I] f‖²_g) x
        = ∑ i, hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
            (Bi i).toFun (Bi i).toFun x := by
    rw [scalarLaplacian_eq_laplacian_hessianBilin]
    show laplacian (I := I) (M := M)
        (hessianBilin (I := I) (‖grad_g[I] f‖²_g)) x = _
    unfold laplacian
    rw [trace_def]
    rw [← Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x
          (hessianBilin (I := I) (‖grad_g[I] f‖²_g) x)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rfl
  rw [h_scalarLap_eq, Finset.mul_sum]
  -- Step 2: per-summand section-form Hess identity (`hessian_gradientNormSq_apply_section`).
  have h_summand : ∀ i,
      (1 / 2 : ℝ) * hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
        (Bi i).toFun (Bi i).toFun x
      = metricInner x
            (secondCovDerivSection (I := I) (M := M)
              (manifoldGradient (I := I) f) (Bi i).toFun (Bi i).toFun x)
            (manifoldGradient (I := I) f x)
          + metricInner x
              (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x)
              (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x) := by
    intro i
    rw [hessian_gradientNormSq_apply_section f (Bi i) x h_grad]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_summand i), Finset.sum_add_distrib]
  -- Step 3: identify the two sums.
  congr 1
  · -- First sum: ∑_i ⟨secondCovDerivSection ∇f (Bi · x) (Bi · x) x, ∇f x⟩
    --             = ⟨connectionLaplacian ∇f x, ∇f x⟩ via `sum_inner` + `connectionLaplacian_def`.
    show ∑ i, metricInner x
          (secondCovDerivSection (I := I) (M := M)
            (manifoldGradient (I := I) f) (Bi i).toFun (Bi i).toFun x)
          (manifoldGradient (I := I) f x)
        = metricInner x
            (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
            (manifoldGradient (I := I) f x)
    rw [connectionLaplacian_def]
    exact (sum_inner Finset.univ
      (fun i => secondCovDerivSection (I := I) (M := M)
        (manifoldGradient (I := I) f) (Bi i).toFun (Bi i).toFun x)
      (manifoldGradient (I := I) f x)).symm
  · -- Second sum: ∑_i ‖∇_{Bi · x x} ∇f x‖² = frobeniusSq (hessianBilin f) x.
    -- Approach: Stage 7 basis-invariance on the bilinear form
    -- `B(v, w) := ⟪covDerivAt ∇f x v, covDerivAt ∇f x w⟫_ℝ` (a `LinearMap.mk₂`),
    -- converts smoothOrthoFrame trace to std-basis trace; then the existing
    -- orthonormal-basis Frobenius identity closes.
    show ∑ i, metricInner x
            (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x)
            (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x)
        = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
    -- Construct the bilinear form for Stage 7 swap.
    set B' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ
        (fun v w => @inner ℝ (TangentSpace I x) _
          (covDerivAt (manifoldGradient (I := I) f) x v)
          (covDerivAt (manifoldGradient (I := I) f) x w))
        (fun v₁ v₂ w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x (v₁ + v₂))
              (covDerivAt (manifoldGradient (I := I) f) x w)
            = @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v₁)
                (covDerivAt (manifoldGradient (I := I) f) x w)
              + @inner ℝ (TangentSpace I x) _
                  (covDerivAt (manifoldGradient (I := I) f) x v₂)
                  (covDerivAt (manifoldGradient (I := I) f) x w)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_add, inner_add_left])
        (fun c v w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x (c • v))
              (covDerivAt (manifoldGradient (I := I) f) x w)
            = c • @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v)
                (covDerivAt (manifoldGradient (I := I) f) x w)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_smul,
              real_inner_smul_left]; rfl)
        (fun v w₁ w₂ => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x v)
              (covDerivAt (manifoldGradient (I := I) f) x (w₁ + w₂))
            = @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v)
                (covDerivAt (manifoldGradient (I := I) f) x w₁)
              + @inner ℝ (TangentSpace I x) _
                  (covDerivAt (manifoldGradient (I := I) f) x v)
                  (covDerivAt (manifoldGradient (I := I) f) x w₂)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_add, inner_add_right])
        (fun c v w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x v)
              (covDerivAt (manifoldGradient (I := I) f) x (c • w))
            = c • @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v)
                (covDerivAt (manifoldGradient (I := I) f) x w)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_smul,
              real_inner_smul_right]; rfl) with hB'_def
    -- Stage 7 swap: ∑_i B'(Bi · x x, Bi · x x) = ∑_i B'(εᵢ, εᵢ).
    have h_stage7 :=
      Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x B'
    rw [hB'_def] at h_stage7
    simp only [LinearMap.mk₂_apply] at h_stage7
    -- LHS: rewrite `metricInner x (covDeriv (Bi · x) ∇f x) (covDeriv (Bi · x) ∇f x)`
    -- as `⟪covDerivAt ∇f x (Bi · x x), covDerivAt ∇f x (Bi · x x)⟫_ℝ` (def-eq), match h_stage7's LHS.
    show ∑ i, @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x
                (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
              (covDerivAt (manifoldGradient (I := I) f) x
                (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
    rw [h_stage7]
    -- Now goal: ∑_i ⟪covDerivAt ∇f x εᵢ, covDerivAt ∇f x εᵢ⟫_ℝ = frobeniusSq.
    -- Existing chain via OrthonormalBasis.sum_sq_inner_left.
    unfold frobeniusSq
    refine Finset.sum_congr rfl ?_
    intro i _
    set b := stdOrthonormalBasis ℝ (TangentSpace I x)
    set v : TangentSpace I x :=
      covDerivAt (manifoldGradient (I := I) f) x (b i)
    have h_hess_unfold : ∀ j, ((hessianBilin (I := I) f x) (b i)) (b j)
                            = metricInner x v (b j) := fun _ => rfl
    simp only [h_hess_unfold]
    calc @inner ℝ (TangentSpace I x) _ v v
        = ⟪v, v⟫_ℝ := rfl
      _ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      _ = ∑ j, ⟪v, b j⟫_ℝ ^ 2 := (b.sum_sq_inner_left v).symm
      _ = ∑ j, (metricInner x v (b j)) ^ 2 := rfl

/-! ## Conditional infrastructure for the heart-of-Bochner closure

Two conditional reductions, ported from `external/differential-geometry`'s
`heart_of_bochner_curvature_term` (Item 5) and
`heart_of_bochner_of_inner_form` (Item 8). They expose the natural
"shape" of the algebraic content of the heart-of-Bochner closure, taking
as input the relevant algebraic identity and producing the form the
downstream consumer needs. These conditionals do not close any sorry by
themselves — they package the assumptions cleanly. -/

/-- **Hess-sym swap of the inner-product partner for $\nabla^2 \nabla f$**:
for constant lifts of $v, w, z$ at $x$,
$$\langle (\nabla^2 \nabla f)(v, w),\, z\rangle_g(x)
  = \langle (\nabla^2 \nabla f)(v, z),\, w\rangle_g(x).$$

The proof routes through metric-compatibility at $x$ on
$(V, \partial_W \nabla f, Z)$ (and similarly with $W \leftrightarrow Z$),
which converts each $\langle (\nabla^2 \nabla f)(v, \cdot),\, \cdot\rangle_g$
expression into an `mfderiv` of `hessianBilin f y \cdot \cdot` at $x$ in
direction $v$, plus Christoffel-correction `hessianBilin` terms at $x$.

The (w ↔ z) swap then closes via two ingredients:
* `h_eventual_sym`: the nbhd-Hessian-symmetry hypothesis equating
  $y \mapsto \mathrm{hessianBilin}\,f\,y\,w\,z$ and the (w ↔ z) swap on a
  nbhd of $x$. Its V-derivative bridge is `EventuallyEq.mfderiv_eq`.
* `hessianBilin_symm` at $x$ for the Christoffel-correction cross terms,
  applied to arbitrary tangent-space arguments (Γvw, z) and (Γvz, w).

The `h_eventual_sym` hypothesis is discharged in the downstream assembly
by combining pointwise `hessianBilin_symm` at each $y$ in a nbhd of $x$
with nbhd-`h_interior` propagation (available under
`IsLocallyConstantChartedSpace H M` and strict-interior `h_interior` at
$x$). Ported from do Carmo §6 / Petersen Ch 7 §1 Prop 33. -/
theorem metricInner_secondCovDerivAt_grad_swap_of_hess_eventual_sym
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M) (v w z : TangentSpace I x)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (h_grad : TangentSmoothAt (manifoldGradient (I := I) f) x)
    (h_grad_const_w : TangentSmoothAt
        (fun y : M => covDerivAt (manifoldGradient (I := I) f) y w) x)
    (h_grad_const_z : TangentSmoothAt
        (fun y : M => covDerivAt (manifoldGradient (I := I) f) y z) x)
    (h_eventual_sym : (fun y : M => hessianBilin (I := I) f y w z)
        =ᶠ[𝓝 x] (fun y : M => hessianBilin (I := I) f y z w)) :
    metricInner x (secondCovDerivAt (I := I) (M := M)
        (manifoldGradient (I := I) f) x v w) z =
      metricInner x (secondCovDerivAt (I := I) (M := M)
        (manifoldGradient (I := I) f) x v z) w := by
  classical
  -- Constant lifts of v, w, z at x.
  set V : Π y : M, TangentSpace I y := fun _ => (v : TangentSpace I x) with hV_def
  set W : Π y : M, TangentSpace I y := fun _ => (w : TangentSpace I x) with hW_def
  set Z : Π y : M, TangentSpace I y := fun _ => (z : TangentSpace I x) with hZ_def
  have hVsm : TangentSmoothAt V x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  have hWsm : TangentSmoothAt W x :=
    (SmoothVectorField.const (I := I) (M := M) (w : E)).smoothAt x
  have hZsm : TangentSmoothAt Z x :=
    (SmoothVectorField.const (I := I) (M := M) (z : E)).smoothAt x
  -- V-derivative bridge via EventuallyEq.mfderiv_eq (applied at v).
  have h_eq_mfderiv :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) f y w z) x
      = mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) f y z w) x :=
    Filter.EventuallyEq.mfderiv_eq h_eventual_sym
  have h_eq_at_v :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) f y w z) x v
      = mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) f y z w) x v :=
    congrArg (· v) h_eq_mfderiv
  -- Metric-compatibility at x with (V, ∂_W ∇f, Z) and the swap.
  have h_compat_W := leviCivitaConnection_metric_compatible
    V (fun y => covDerivAt (manifoldGradient (I := I) f) y w) Z x
    hVsm h_grad_const_w hZsm
  have h_compat_Z := leviCivitaConnection_metric_compatible
    V (fun y => covDerivAt (manifoldGradient (I := I) f) y z) W x
    hVsm h_grad_const_z hWsm
  -- Rewrite metric-compat LHS into `hessianBilin f y w z` / `f y z w` form.
  have h_hess_W :
      (fun y : M => metricInner y (covDerivAt (manifoldGradient (I := I) f) y w) (Z y))
        = (fun y : M => hessianBilin (I := I) f y w z) := by
    funext y; show metricInner y _ z = hessianBilin (I := I) f y w z; rfl
  have h_hess_Z :
      (fun y : M => metricInner y (covDerivAt (manifoldGradient (I := I) f) y z) (W y))
        = (fun y : M => hessianBilin (I := I) f y z w) := by
    funext y; show metricInner y _ w = hessianBilin (I := I) f y z w; rfl
  rw [h_hess_W] at h_compat_W
  rw [h_hess_Z] at h_compat_Z
  -- V x = v, W x = w, Z x = z (all rfl, constant lifts).
  have hVx : V x = v := rfl
  have hWx : W x = w := rfl
  have hZx : Z x = z := rfl
  rw [hVx] at h_compat_W h_compat_Z
  rw [hWx] at h_compat_Z
  rw [hZx] at h_compat_W
  -- General point-Hess-sym at x (any pair of tangent-space args).
  have h_hess_sym : ∀ a b : TangentSpace I x,
      hessianBilin (I := I) f x a b = hessianBilin (I := I) f x b a :=
    fun a b => hessianBilin_symm (I := I) f x h_interior hf_2 h_grad a b
  -- Christoffel corrections as tangent-space elements at x.
  set Γvw : TangentSpace I x :=
    (leviCivitaConnection (I := I) (M := M)).toFun W x v with hΓvw_def
  set Γvz : TangentSpace I x :=
    (leviCivitaConnection (I := I) (M := M)).toFun Z x v with hΓvz_def
  -- Identify the second metric-compat term as hessianBilin (cross terms).
  -- ⟨covDerivAt ∇f x w, Γvz⟩ = hessianBilin f x w Γvz (by def).
  have h_id_W : metricInner x (covDerivAt (manifoldGradient (I := I) f) x w)
        ((leviCivitaConnection (I := I) (M := M)).toFun Z x v)
      = hessianBilin (I := I) f x w Γvz := rfl
  have h_id_Z : metricInner x (covDerivAt (manifoldGradient (I := I) f) x z)
        ((leviCivitaConnection (I := I) (M := M)).toFun W x v)
      = hessianBilin (I := I) f x z Γvw := rfl
  rw [h_id_W] at h_compat_W
  rw [h_id_Z] at h_compat_Z
  -- Now unfold secondCovDerivAt and metric-inner-sub.
  show metricInner x
      (covDerivAt (fun y : M => covDerivAt (manifoldGradient (I := I) f) y w) x v
        - covDerivAt (manifoldGradient (I := I) f) x
            (covDerivAt (Y := fun _ : M => (w : TangentSpace I x)) x v)) z
    = metricInner x
      (covDerivAt (fun y : M => covDerivAt (manifoldGradient (I := I) f) y z) x v
        - covDerivAt (manifoldGradient (I := I) f) x
            (covDerivAt (Y := fun _ : M => (z : TangentSpace I x)) x v)) w
  rw [metricInner_sub_left, metricInner_sub_left]
  -- Identify outer terms: ⟨covDerivAt (∂_W ∇f) x v, z⟩ = ⟨lcc.(∂_W ∇f) x v, z⟩ (rfl).
  -- Identify Christoffel terms: ⟨covDerivAt ∇f x Γvw, z⟩ = hessianBilin f x Γvw z (rfl).
  show metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun
        (fun y : M => covDerivAt (manifoldGradient (I := I) f) y w) x v) z
      - hessianBilin (I := I) f x Γvw z
    = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun
        (fun y : M => covDerivAt (manifoldGradient (I := I) f) y z) x v) w
      - hessianBilin (I := I) f x Γvz w
  -- Cross-term Hess-sym: hessianBilin f x z Γvw = hessianBilin f x Γvw z, etc.
  have h_sym_zΓvw : hessianBilin (I := I) f x z Γvw
      = hessianBilin (I := I) f x Γvw z := h_hess_sym z Γvw
  have h_sym_wΓvz : hessianBilin (I := I) f x w Γvz
      = hessianBilin (I := I) f x Γvz w := h_hess_sym w Γvz
  -- Combine via linear_combination on h_compat_W, h_compat_Z, h_eq_at_v, h_sym_*.
  -- A - hA = B - hB  where
  --   h_compat_W: P = A + hB'  (where hB' = h_sym_wΓvz ↦ hB)
  --   h_compat_Z: Q = B + hA'  (where hA' = h_sym_zΓvw ↦ hA)
  --   h_eq_at_v:  P = Q
  --   h_sym_wΓvz: hB' = hB
  --   h_sym_zΓvw: hA' = hA
  -- ⇒ A - hA = (P - hB') - hA = (Q - hB) - hA' = (B + hA' - hB) - hA' = B - hB ✓
  linear_combination -h_compat_W + h_compat_Z + h_eq_at_v + h_sym_zΓvw - h_sym_wΓvz

/-- **Discharge of `h_eventual_sym` from strict interior hypothesis**.
Combines `extChartAt_self_eventually_mem_closure_interior_range` (nbhd
propagation of `h_interior` under `IsLocallyConstantChartedSpace`) with
pointwise `hessianBilin_symm` to produce the nbhd-Hessian-symmetry
equation needed by `metricInner_secondCovDerivAt_grad_swap_of_hess_eventual_sym`.

The stricter `extChartAt I x x ∈ interior (Set.range I)` hypothesis is
required so that the strict-interior open set has a nbhd of `x` as its
preimage; the conclusion is `eventually equal as a section` w.r.t. the
weaker closure-interior membership predicate used by the pointwise
`hessianBilin_symm`. -/
theorem hessianBilin_eventually_symm_of_strict_interior
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M)))
    (w z : TangentSpace I x) :
    (fun y : M => hessianBilin (I := I) f y w z)
      =ᶠ[𝓝 x] (fun y : M => hessianBilin (I := I) f y z w) := by
  -- Propagate strict h_strict to closure-interior eventually.
  have h_interior_nbhd :=
    extChartAt_self_eventually_mem_closure_interior_range (I := I) (M := M) h_strict
  filter_upwards [h_interior_nbhd] with y hy_interior
  -- C² of f at y from global C∞.
  have hf_2_y : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f y :=
    (hf y).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  -- Smoothness of ∇f at y from global smoothness.
  have h_grad_y : TangentSmoothAt (manifoldGradient (I := I) f) y :=
    (h_grad y).mdifferentiableAt (by simp)
  -- Pointwise Hess-sym at y. The `w z : TangentSpace I x` args are def-eq to
  -- `TangentSpace I y = E` arguments under `IsLocallyConstantChartedSpace`.
  exact hessianBilin_symm (I := I) f y hy_interior hf_2_y h_grad_y w z

/-- **Section-level Hessian symmetry on smooth vector fields**, discharged
from strict interior. Variant of `hessianBilin_eventually_symm_of_strict_interior`
where the two test slots are smooth varying sections `X, Y` instead of
constant tangent vectors. At every $y$ in a nbhd of $x$,
$\mathrm{Hess}\,f\,(X(y), Y(y))(y) = \mathrm{Hess}\,f\,(Y(y), X(y))(y)$
by pointwise `hessianBilin_symm`. This is the section-level Hess-sym
input needed for the per-summand swap step in the heart-of-Bochner chain
(`bochner_per_summand_swap` analog, OpenGALib analog of external
`heart_per_summand_swap`). -/
theorem hessianBilin_section_eventually_symm_of_strict_interior
    [IsManifold I 2 M]
    (f : M → ℝ) (X Y : Π y : M, TangentSpace I y) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (fun y : M => hessianBilin (I := I) f y (X y) (Y y))
      =ᶠ[𝓝 x] (fun y : M => hessianBilin (I := I) f y (Y y) (X y)) := by
  have h_interior_nbhd :=
    extChartAt_self_eventually_mem_closure_interior_range (I := I) (M := M) h_strict
  filter_upwards [h_interior_nbhd] with y hy_interior
  have hf_2_y : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f y :=
    (hf y).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have h_grad_y : TangentSmoothAt (manifoldGradient (I := I) f) y :=
    (h_grad y).mdifferentiableAt (by simp)
  exact hessianBilin_symm (I := I) f y hy_interior hf_2_y h_grad_y (X y) (Y y)

/-- **Inner-form of the D.2 swap of `secondCovDerivAt`'s outer pair**:
for $v, w, z \in T_xM$,
$$\langle (\nabla^2 \nabla f)(v, w),\, z\rangle_g(x)
  = \langle (\nabla^2 \nabla f)(w, v),\, z\rangle_g(x)
    + \langle R(\mathrm{const}\,v,\,\mathrm{const}\,w)\,\nabla f,\, z\rangle_g(x).$$

Direct corollary of `secondCovDerivAt_sub_swap_eq_riemannCurvature` (D.2)
applied to $Z = \nabla f$, paired with $z$ via the bilinearity of
`metricInner`. The third slot of `riemannCurvature` is the section
$\nabla f$ (not a constant lift); closing the Ric identification
requires the full 3-slot tensoriality of `riemannCurvature` (Z-slot
Leibniz `riemannCurvature_smul_third_scalar_field` already landed in
`Curvature/Tensoriality.lean`; Z-slot vanishing + X/Y-slot mirrors
outstanding) plus `ricci_symm` (now closed in `Curvature.lean`). -/
theorem metricInner_secondCovDerivAt_grad_eq_swap_add_curvature
    (f : M → ℝ) (x : M) (v w z : TangentSpace I x) :
    metricInner x (secondCovDerivAt (I := I) (M := M)
        (manifoldGradient (I := I) f) x v w) z
      = metricInner x (secondCovDerivAt (I := I) (M := M)
          (manifoldGradient (I := I) f) x w v) z
        + metricInner x
            (riemannCurvature (fun _ : M => (v : TangentSpace I x))
              (fun _ : M => (w : TangentSpace I x))
              (manifoldGradient (I := I) f) x) z := by
  have h := secondCovDerivAt_sub_swap_eq_riemannCurvature
    (I := I) (M := M) (manifoldGradient (I := I) f) x v w
  -- h : secondCovDerivAt ∇f x v w - secondCovDerivAt ∇f x w v
  --       = riemannCurvature (const v) (const w) ∇f x
  -- Restate: secondCovDerivAt ∇f x v w = secondCovDerivAt ∇f x w v + R(const v, const w) ∇f x
  have h' : secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x v w
      = secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x w v
        + riemannCurvature (fun _ : M => (v : TangentSpace I x))
            (fun _ : M => (w : TangentSpace I x))
            (manifoldGradient (I := I) f) x := by
    rw [← h]; abel
  rw [h', metricInner_add_left]

/-- **Step 3 helper — curvature term metric-skew packaging.** Given the
metric-skew identity of the Riemann curvature in the last pair of
arguments (the standard $g(R(X,Y)Z, W) = -g(R(X,Y)W, Z)$, applied to
$Z = \nabla f$ and $W = B(x)$), the curvature contribution of the
heart-of-Bochner trace summand reduces to
$- \langle \nabla f, R(B, w) B\rangle_g$ at $x$.

The metric-skew hypothesis is derivable from
`riemannCurvature_inner_self_zero` (now closed in `Curvature.lean`) by
polarisation — see `riemannCurvature_metric_skew`. Ported from external's
`heart_of_bochner_curvature_term`. -/
theorem heart_of_bochner_curvature_term
    (f : M → ℝ)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (h_metric_skew : metricInner x
        (riemannCurvature B w (manifoldGradient (I := I) f) x) (B x)
      + metricInner x (manifoldGradient (I := I) f x)
          (riemannCurvature B w B x) = 0) :
    metricInner x
        (riemannCurvature B w (manifoldGradient (I := I) f) x) (B x) =
      - metricInner x (manifoldGradient (I := I) f x)
          (riemannCurvature B w B x) := by
  linarith

/-- **Ricci sum identity** (heart-of-Bochner Step 3): the curvature trace
over the smooth orthonormal frame at `x` against `(W, ∇f, B_i)` equals
the Ricci bilinear evaluated at `(∇f x, W x)`:
$$\sum_i g_x\bigl(R(B_i, W)\,\nabla f,\, B_i\bigr) \;=\;
  \mathrm{Ric}_g(\nabla f, W)(x),$$
where `B_i = smoothOrthoFrame g x i`.

Strategy:
1. Per `i`, `riemannCurvature_eq_of_pointwise_eq` replaces the three
   smooth-section arguments of `R` with their constant lifts at `x`
   (`Bi i x`, `W x`, `∇f x`). The values at `x` agree by definition.
2. The bilinear form `Φ(v, w) := g_x(curvatureEndo (const Wx) (const ∇fx) x v, w)`
   has diagonal sum `∑ i Φ(Bi i x, Bi i x)` equal to the LHS, and by
   `Tensor.sum_diagonal_smoothOrthoFrame_eq_std` (Stage 7 basis-invariance)
   equal to `∑ i Φ(stdBasis i, stdBasis i)`.
3. `ricciTensor_eq_sum_inner_orthonormal` identifies the std-basis sum
   with `Ric_g(W x, ∇f x) x`; `ricci_symm` swaps to `Ric_g(∇f x, W x) x`.

External reference: `heart_curvature_orthonormal_sum_eq_ricci` in
`differential-geometry/.../Bochner.lean:2013`. -/
theorem heart_curvature_orthonormal_sum_eq_ricci
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (W : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ∑ i, metricInner x
        (riemannCurvature
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i)
          W.toFun (manifoldGradient (I := I) f) x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
      = Ric_g(manifoldGradient (I := I) f x, W.toFun x) x := by
  classical
  -- Wrap `∇f`, frame, and the constant lifts of `(W x, ∇f x)` as `SmoothVectorField`.
  let gradF : SmoothVectorField I M :=
    { toFun := manifoldGradient (I := I) f, smooth := h_grad }
  let Bi : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i
      smooth := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i }
  let WV : SmoothVectorField I M :=
    SmoothVectorField.const (I := I) (M := M) (W.toFun x : E)
  let GV : SmoothVectorField I M :=
    SmoothVectorField.const (I := I) (M := M) (gradF.toFun x : E)
  -- Bilinear form `Φ(v, w) := g_x(curvatureEndo WV GV x v, w)`.
  set Φ : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w => metricInner x (curvatureEndo WV GV x v) w)
      (fun v₁ v₂ w => by
        show metricInner x (curvatureEndo WV GV x (v₁ + v₂)) w
          = metricInner x (curvatureEndo WV GV x v₁) w
            + metricInner x (curvatureEndo WV GV x v₂) w
        rw [(curvatureEndo WV GV x).map_add, metricInner_add_left])
      (fun c v w => by
        show metricInner x (curvatureEndo WV GV x (c • v)) w
          = c • metricInner x (curvatureEndo WV GV x v) w
        rw [(curvatureEndo WV GV x).map_smul, metricInner_smul_left]; rfl)
      (fun v w₁ w₂ => by
        show metricInner x (curvatureEndo WV GV x v) (w₁ + w₂)
          = metricInner x (curvatureEndo WV GV x v) w₁
            + metricInner x (curvatureEndo WV GV x v) w₂
        rw [metricInner_add_right])
      (fun c v w => by
        show metricInner x (curvatureEndo WV GV x v) (c • w)
          = c • metricInner x (curvatureEndo WV GV x v) w
        rw [metricInner_smul_right]; rfl) with hΦ_def
  -- Step 1: per-`i` pointwise-eq reduction.
  have h_per_i : ∀ i,
      metricInner x
          (riemannCurvature (Bi i).toFun W.toFun gradF.toFun x) ((Bi i).toFun x)
        = Φ ((Bi i).toFun x) ((Bi i).toFun x) := by
    intro i
    have hR_eq : riemannCurvature (Bi i).toFun W.toFun gradF.toFun x
        = curvatureEndo WV GV x ((Bi i).toFun x) := by
      show riemannCurvature (Bi i).toFun W.toFun gradF.toFun x
        = riemannCurvature
            (fun _ : M => ((Bi i).toFun x : TangentSpace I x))
            WV.toFun GV.toFun x
      exact riemannCurvature_eq_of_pointwise_eq
        (Bi i) (SmoothVectorField.const ((Bi i).toFun x : E))
        W WV gradF GV x h_interior rfl rfl rfl
    rw [hR_eq]; rfl
  -- Step 2 + 3 + 4: rewrite via h_per_i, Stage 7, identify with Ric, ricci_symm.
  calc ∑ i, metricInner x
        (riemannCurvature (Bi i).toFun W.toFun gradF.toFun x) ((Bi i).toFun x)
      = ∑ i, Φ ((Bi i).toFun x) ((Bi i).toFun x) :=
        Finset.sum_congr rfl (fun i _ => h_per_i i)
    _ = ∑ i, Φ ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i) :=
        Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x Φ
    _ = Ric_g(W.toFun x, gradF.toFun x) x := by
        rw [ricciTensor_eq_sum_inner_orthonormal x (W.toFun x) (gradF.toFun x)]
        apply Finset.sum_congr rfl
        intro i _
        -- Φ v v = metricInner (curvatureEndo WV GV x v) v
        --       = ⟪curvatureEndo WV GV x v, v⟫_ℝ (def-eq)
        --       = ⟪v, curvatureEndo WV GV x v⟫_ℝ (real_inner_comm).
        show ⟪curvatureEndo WV GV x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i),
                (stdOrthonormalBasis ℝ (TangentSpace I x)) i⟫_ℝ
            = ⟪(stdOrthonormalBasis ℝ (TangentSpace I x)) i,
                curvatureEndo WV GV x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)⟫_ℝ
        exact real_inner_comm _ _
    _ = Ric_g(gradF.toFun x, W.toFun x) x := by
        show ricciTensor x (W.toFun x) (gradF.toFun x)
          = ricciTensor x (gradF.toFun x) (W.toFun x)
        show ricci WV GV x = ricci GV WV x
        exact ricci_symm WV GV x h_interior

/-- **Hessian-frame trace = Laplacian, locally**: on a neighbourhood of `x`,
$$\sum_i \mathrm{Hess}\,f(b)(B_i b, B_i b) \;=\; \Delta_g f(b),$$
where `B_i = smoothOrthoFrame g x i`.

Strategy:
1. On `smoothOrthoFrameNbhd x`, `(B_i b)_i` is `g_b`-orthonormal at each `b`
   (via `smoothOrthoFrame_orthonormal`).
2. Apply `Tensor.sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std` to swap
   the diagonal trace of `hessianBilin f b` over `(B_i b)` to the diagonal
   trace over `stdOrthonormalBasis ℝ (T_bM)`.
3. The latter equals `laplacian (hessianBilin f) b = scalarLaplacian f b
   = Δ_g f b` by definition + `scalarLaplacian_eq_laplacian_hessianBilin`. -/
theorem sum_hessianBilin_smoothOrthoFrame_eventuallyEq_laplacian
    (f : M → ℝ) (x : M) :
    (fun b => ∑ i, hessianBilin (I := I) f b
                    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b)
                    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b))
      =ᶠ[𝓝 x] (Δ_g[I] f : M → ℝ) := by
  filter_upwards [Riemannian.Tensor.smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x]
    with b hb
  -- At b ∈ nbhd, basis-invariance of trace of `hessianBilin f b`.
  rw [Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std
        (I := I) x hb (hessianBilin (I := I) f b)]
  -- Identify the std-basis trace with `Δ_g f b`.
  show ∑ i, hessianBilin (I := I) f b
            ((stdOrthonormalBasis ℝ (TangentSpace I b)) i)
            ((stdOrthonormalBasis ℝ (TangentSpace I b)) i)
       = scalarLaplacian (I := I) f b
  rw [scalarLaplacian_eq_laplacian_hessianBilin]
  rfl

/-! ### Orthonormal-frame skew-derivative and the connection-cancel sum -/

/-- **Smooth orthonormal frame cov-skew at `x`**: differentiating the constant
function `b ↦ g(B_i b, B_j b) = δ_{ij}` on `smoothOrthoFrameNbhd x` along
any direction `v ∈ T_xM` and applying metric compatibility gives
$$g_x(\nabla_v B_i, B_j x) + g_x(B_i x, \nabla_v B_j) = 0.$$

External reference: `smoothOrthoFrame_cov_skew` in
`differential-geometry/.../Bochner.lean:2058`. -/
theorem smoothOrthoFrame_cov_skew
    [T2Space M]
    (x : M) (i j : Fin (Module.finrank ℝ E)) (v : TangentSpace I x) :
    metricInner x
        ((leviCivitaConnection (I := I) (M := M)).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x v)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) +
    metricInner x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M)).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j) x v)
      = 0 := by
  classical
  -- Section-level smoothness of the smooth orthonormal frame.
  have hBi := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i
  have hBj := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x j
  have hBi_at : TangentSmoothAt
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x :=
    (hBi x).mdifferentiableAt (by simp)
  have hBj_at : TangentSmoothAt
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j) x :=
    (hBj x).mdifferentiableAt (by simp)
  -- Treat as constant section on the nbhd: `b ↦ g(B_i b, B_j b) =ᶠ if i = j then 1 else 0`.
  have h_constant_on_nbhd : ∀ᶠ b in 𝓝 x,
      metricInner b (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j b)
      = (if i = j then (1 : ℝ) else 0) := by
    filter_upwards [Riemannian.Tensor.smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x]
      with b hb
    exact Riemannian.Tensor.smoothOrthoFrame_orthonormal (I := I) hm.metric x hb i j
  -- mfderiv equality.
  have h_eq : (fun b : M => metricInner b
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j b)) =ᶠ[𝓝 x]
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) := h_constant_on_nbhd
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) (fun b : M => metricInner b
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j b)) x =
      mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (if i = j then (1 : ℝ) else 0)) x :=
    Filter.EventuallyEq.mfderiv_eq h_eq
  -- The const function has zero mfderiv.
  have h_const_zero : mfderiv I 𝓘(ℝ, ℝ)
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) x = 0 := mfderiv_const ..
  -- Metric compatibility at x along the constant direction `v`.
  have hVsm : TangentSmoothAt (fun _ : M => (v : TangentSpace I x)) x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  have hmc := leviCivitaConnection_metric_compatible
    (fun _ : M => (v : TangentSpace I x))
    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i)
    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j) x hVsm hBi_at hBj_at
  -- hmc : mfderiv (b ↦ g(B_i, B_j)) x ((const v) x) = g(LC B_i x (v), B_j x) + g(B_i x, LC B_j x (v))
  -- (const v) x = v, so this becomes the desired form, but with LHS = 0.
  have h_lhs_zero : (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => metricInner b
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j b)) x) v = 0 := by
    rw [h_mfderiv_eq, h_const_zero]; rfl
  rw [h_lhs_zero] at hmc
  exact hmc.symm

/-- **Hessian × cov-frame antisym-symm sum vanishes** (heart-of-Bochner Step 4):
for smooth scalar `f` (C∞), `W : SmoothVectorField`, and `x` in the strict
interior with smooth `∇f`,
$$\sum_i \mathrm{Hess}\,f(x)(B_i x,\, \nabla_{W(x)} B_i) \;=\; 0,$$
where `B_i = smoothOrthoFrame g x i` and `∇_{W(x)} B_i = covDeriv W B_i (x)`.

Strategy:
1. Expand `∇_{W(x)} B_i = ∑_j ⟨∇_{W(x)} B_i, B_j x⟩ • B_j x` (orthonormal Riesz).
2. By bilinearity, `Hess f(B_i, ∇_W B_i) = ∑_j ⟨∇_{W(x)} B_i, B_j⟩ • Hess f(B_i, B_j)`.
3. The matrix `a_{ij} := ⟨∇_{W(x)} B_i, B_j x⟩` is antisymmetric in (i, j) by
   `smoothOrthoFrame_cov_skew` + `metricInner_comm`.
4. The Hessian matrix `h_{ij} := Hess f(B_i, B_j)` is symmetric in (i, j) by
   `hessianBilin_symm` (needs `h_interior` + `f` C^2 + ∇f smooth).
5. `∑_{i,j} a_{ij} • h_{ij}` with antisym × symm = 0 (`Finset.sum_apply_diagonal_invariant`-style
   cancellation, or direct `Finset.sum_swap`-symmetry argument). -/
theorem sum_hessianBilin_smoothOrthoFrame_cov_eq_zero
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (W : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ∑ i, hessianBilin (I := I) f x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M)).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x
          (W.toFun x)) = 0 := by
  classical
  set bAt : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    Riemannian.Tensor.smoothOrthoFrameOrthonormalBasis (I := I) x with hbAt_def
  -- Key matrices.
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => metricInner x
      ((leviCivitaConnection (I := I) (M := M)).toFun
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x (W.toFun x))
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) with ha_def
  set h_mat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => hessianBilin (I := I) f x
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) with hh_def
  -- Step 1: Orthonormal Riesz expansion of ∇_{W(x)} B_i.
  -- `v = ∑ k, ⟪b_k, v⟫_ℝ • b_k` for orthonormal basis `b_k` and `v ∈ T_xM`.
  have h_riesz : ∀ i,
      (leviCivitaConnection (I := I) (M := M)).toFun
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x (W.toFun x)
        = ∑ j, a i j •
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) := by
    intro i
    set v : TangentSpace I x :=
      (leviCivitaConnection (I := I) (M := M)).toFun
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x (W.toFun x)
      with hv_def
    -- `OrthonormalBasis.sum_repr'` : `∑ j, ⟪b j, v⟫_ℝ • b j = v`.
    have h_sum : v = ∑ j, ⟪bAt j, v⟫_ℝ • bAt j := (bAt.sum_repr' v).symm
    rw [h_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- bAt j = smoothOrthoFrame ... j x by `smoothOrthoFrameOrthonormalBasis_apply`.
    rw [Riemannian.Tensor.smoothOrthoFrameOrthonormalBasis_apply]
    -- ⟪B_j x, v⟫_ℝ = metricInner x (B_j x) v = a i j (by metricInner_comm).
    show ⟪Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x, v⟫_ℝ • _ = a i j • _
    show metricInner x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) v • _
        = a i j • _
    congr 1
    show metricInner x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) v
        = metricInner x v
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x)
    exact metricInner_comm x _ _
  -- Step 2: rewrite the sum with the Riesz expansion + bilinearity of hessianBilin.
  have h_expand : ∀ i, hessianBilin (I := I) f x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M)).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x
          (W.toFun x))
      = ∑ j, a i j * h_mat i j := by
    intro i
    rw [h_riesz i]
    -- hessianBilin is bilinear; push sum out.
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [LinearMap.map_smul]
    show a i j • h_mat i j = a i j * h_mat i j
    rfl
  rw [show (∑ i, hessianBilin (I := I) f x _ _)
      = (∑ i, ∑ j, a i j * h_mat i j) from
    Finset.sum_congr rfl (fun i _ => h_expand i)]
  -- Step 3: Antisym of a, symm of h_mat ⇒ ∑_{i,j} a_{ij} h_{ij} = 0.
  -- Use a swap-of-indices argument: ∑_{i,j} a_{ij} h_{ij} = ∑_{i,j} a_{ji} h_{ji}
  --                                                     = -∑_{i,j} a_{ij} h_{ij}
  -- (by anti-symm of a and symm of h). Hence 2 * sum = 0 ⇒ sum = 0.
  have h_anti : ∀ i j, a i j = -(a j i) := by
    intro i j
    -- From smoothOrthoFrame_cov_skew: a i j + g(B_i, ∇_W B_j) = 0.
    -- And g(B_i x, ∇_{W x} B_j) = g(∇_{W x} B_j, B_i x) = a j i by metricInner_comm.
    have h := smoothOrthoFrame_cov_skew x i j (W.toFun x)
    have h_swap : metricInner x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M)).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j) x (W.toFun x))
        = a j i := by
      show metricInner x _ _ = metricInner x _ _
      exact metricInner_comm x _ _
    rw [h_swap] at h
    linarith
  have h_symm : ∀ i j, h_mat i j = h_mat j i := by
    intro i j
    have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
      (hf x).of_le (by
        show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
    have h_grad_at : TangentSmoothAt (manifoldGradient (I := I) f) x :=
      (h_grad x).mdifferentiableAt (by simp)
    exact hessianBilin_symm (I := I) f x h_interior hf_2 h_grad_at _ _
  -- ∑_{i,j} a_{ij} h_{ij} = ∑_{j,i} a_{ij} h_{ij}  (Finset.sum_comm on the outer)
  --                       = ∑_{j,i} a_{ji} h_{ji}  (relabel i ↔ j: a single rename)
  -- Combined with antisym + symm: a_{ji} h_{ji} = -a_{ij} h_{ij}.
  have h_anti_symm : ∀ i j, a i j * h_mat i j = -(a j i * h_mat j i) := by
    intro i j
    rw [h_anti i j, h_symm i j]; ring
  -- ∑_{i,j} a_{ij} h_{ij} = ∑_{i,j} -(a_{ji} h_{ji}) = -∑_{i,j} a_{ji} h_{ji}
  --                       = -∑_{j,i} a_{ji} h_{ji}  (rename outer)
  --                       = -∑_{i,j} a_{ij} h_{ij}  (sum_comm on inner)
  have h_sum_eq_neg : (∑ i, ∑ j, a i j * h_mat i j)
      = -(∑ i, ∑ j, a i j * h_mat i j) :=
    calc (∑ i, ∑ j, a i j * h_mat i j)
        = ∑ i, ∑ j, -(a j i * h_mat j i) :=
          Finset.sum_congr rfl (fun i _ =>
            Finset.sum_congr rfl (fun j _ => h_anti_symm i j))
      _ = -∑ i, ∑ j, a j i * h_mat j i := by
          simp only [← Finset.sum_neg_distrib]
      _ = -∑ j, ∑ i, a j i * h_mat j i := by
          rw [Finset.sum_comm (f := fun i j => a j i * h_mat j i)]
      _ = -∑ i, ∑ j, a i j * h_mat i j := rfl
  -- s = -s ⇒ s = 0.
  linarith

/-- **Conditional inner-form reduction.** Given the inner-product form
of the heart-of-Bochner sum identity against every test direction $w$
(against the smooth orthonormal frame `smoothOrthoFrame g x · x`), the
scalar form paired specifically against $\nabla f x$ follows by
Riesz-style specialisation plus pulling the sum out of the metric inner
product (bilinearity).

This is the OpenGALib analog of external's
`heart_of_bochner_smoothOrthoFrame_of_inner_form` (Item 8 of
`RicciIdentity.lean`). The inner-form hypothesis is the natural product
of the 4-step algebraic chain (Step 1 Hess-sym swap, Step 2 D.3, Step 3
Ric identification, Step 4 smooth-trace identification) when each step
is proven against an arbitrary test direction $w$. Specialising
afterwards at $w = \nabla f x$ recovers the scalar form needed by the
downstream Bochner-Weitzenböck assembly. -/
theorem sum_inner_secondCovDerivAt_grad_smoothOrthoFrame_of_inner_form
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      metricInner x
          (∑ i, secondCovDerivAt (I := I) (M := M)
            (manifoldGradient (I := I) f) x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
          w
        = metricInner x (manifoldGradient (I := I) (Δ_g[I] f) x) w
          + Ric_g(manifoldGradient (I := I) f x, w) x) :
    ∑ i, metricInner x
        (secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
            (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x := by
  classical
  -- Specialise hInner at w = ∇f x.
  have h := hInner (manifoldGradient (I := I) f x)
  -- Chain: ∑ ⟨A i, ∇f⟩ = ⟨∑ A i, ∇f⟩ (sum_inner, via metricInner = ⟪·,·⟫_ℝ
  -- def-eq) = ⟨∇Δf, ∇f⟩ + Ric (hInner) = ⟨∇f, ∇Δf⟩ + Ric (metricInner_comm).
  calc ∑ i, metricInner x
          (secondCovDerivAt (I := I) (M := M)
            (manifoldGradient (I := I) f) x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
          (manifoldGradient (I := I) f x)
      = metricInner x
          (∑ i, secondCovDerivAt (I := I) (M := M)
            (manifoldGradient (I := I) f) x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
          (manifoldGradient (I := I) f x) :=
        (sum_inner Finset.univ _ (manifoldGradient (I := I) f x)).symm
    _ = metricInner x (manifoldGradient (I := I) (Δ_g[I] f) x)
            (manifoldGradient (I := I) f x)
          + Ric_g(manifoldGradient (I := I) f x,
                  manifoldGradient (I := I) f x) x := h
    _ = metricInner x (manifoldGradient (I := I) f x)
            (manifoldGradient (I := I) (Δ_g[I] f) x)
          + Ric_g(manifoldGradient (I := I) f x,
                  manifoldGradient (I := I) f x) x := by
        rw [metricInner_comm x (manifoldGradient (I := I) (Δ_g[I] f) x)]

end Operators
end Riemannian
