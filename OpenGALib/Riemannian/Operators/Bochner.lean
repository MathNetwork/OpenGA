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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
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
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
      = ⟪connectionLaplacian (grad_g[I] f) x, (grad_g[I] f) x⟫_g
        + ‖hess_g[I] f‖²_g x := by
  show (1 / 2 : ℝ) * Operators.scalarLaplacian (I := I) (M := M) (‖grad_g[I] f‖²_g) x
      = metricInner x
          (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
          (manifoldGradient (I := I) f x)
        + frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
  unfold scalarLaplacian
  rw [Finset.mul_sum]
  -- Per-summand expansion via the helper, with `(1/2) * 2 = 1`
  have h_summand : ∀ i,
      (1 / 2 : ℝ) * hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
        (fun _ : M => ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                        : TangentSpace I x))
        (fun _ : M => ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                        : TangentSpace I x)) x
      = metricInner x
            (secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
            (manifoldGradient (I := I) f x)
          + metricInner x
              (covDerivAt (manifoldGradient (I := I) f) x
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
              (covDerivAt (manifoldGradient (I := I) f) x
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) := by
    intro i
    rw [hessian_gradientNormSq_apply_chartFrame f x _ h_grad]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_summand i), Finset.sum_add_distrib]
  -- Goal:
  --   ∑ᵢ metricInner x (sCD ∇f x εᵢ εᵢ) (∇f x)
  --   + ∑ᵢ metricInner x (covD ∇f x εᵢ) (covD ∇f x εᵢ)
  --   = metricInner x (connectionLaplacian (∇f) x) (∇f x) + frobeniusSq (hessianBilin f) x
  congr 1
  · -- First sum: bilinearity of metricInner + connectionLaplacian as trace bridge
    rw [connectionLaplacian_eq_sum_secondCovDerivAt]
    -- Goal: ∑ᵢ ⟨sCD εᵢ εᵢ, ∇f⟩ = ⟨∑ᵢ sCD εᵢ εᵢ, ∇f⟩
    -- via `sum_inner` on the InnerProductSpace ℝ (TangentSpace I x) instance
    -- (`metricInner x` = `⟪·,·⟫` def-eq via RiemannianBundle routing)
    exact (sum_inner Finset.univ
      (fun i =>
        secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
      (manifoldGradient (I := I) f x)).symm
  · -- Second sum: ∑ᵢ ‖covD ∇f x εᵢ‖² = frobeniusSq (hessianBilin f) x
    -- frobeniusSq B x = ∑ᵢ ∑ⱼ (B x εᵢ εⱼ)²; per-i this is ‖covD ∇f x εᵢ‖² via
    -- orthonormal basis decomposition (`OrthonormalBasis.sum_sq_inner_left`).
    show ∑ i, metricInner x
            (covDerivAt (manifoldGradient (I := I) f) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
            (covDerivAt (manifoldGradient (I := I) f) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
      = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
    unfold frobeniusSq
    refine Finset.sum_congr rfl ?_
    intro i _
    set b := stdOrthonormalBasis ℝ (TangentSpace I x)
    set v : TangentSpace I x :=
      covDerivAt (manifoldGradient (I := I) f) x (b i)
    -- For each i: metricInner x v v = ∑ⱼ ((hessianBilin f x) (b i) (b j))²
    -- = ∑ⱼ (metricInner x v (b j))² (by hessianBilin def + LinearMap.mk₂_apply)
    -- = ∑ⱼ ⟪v, b j⟫_ℝ² (def-eq metricInner ↔ inner)
    -- = ‖v‖² (by OrthonormalBasis.sum_sq_inner_left)
    -- = metricInner x v v (def-eq)
    have h_hess_unfold : ∀ j, ((hessianBilin (I := I) f x) (b i)) (b j)
                            = metricInner x v (b j) := fun _ => rfl
    simp only [h_hess_unfold]
    -- Goal: metricInner x v v = ∑ⱼ (metricInner x v (b j))^2
    -- Chain: metricInner x v v = ⟪v, v⟫_ℝ = ‖v‖^2 = ∑ⱼ ⟪v, b j⟫^2 = ∑ⱼ (metricInner x v (b j))^2
    calc metricInner x v v
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

/-- **Narrowed PRE-PAPER sorry**: heart-of-Bochner sum identity stated
against `smoothOrthoFrame` (Stage 6) instead of `stdOrthonormalBasis`.

By Stage 7 basis invariance
(`Tensor.sum_diagonal_smoothOrthoFrame_eq_std`), this form implies the
`stdOrthonormalBasis` version
(`sum_inner_secondCovDerivAt_grad_eq_inner_grad_laplacian_add_ricci`):
both are diagonal sums of the same bilinear map indexed over an
orthonormal basis of $T_xM$, and the diagonal sum is basis-invariant.

The `smoothOrthoFrame`-form is the natural target for the per-summand +
outer-assembly chain. **Per-summand layer landed** (`Bochner/PerSummand.lean`):

* `bochner_per_summand_swap` (step d) — Hess-sym swap form;
* `bochner_per_summand_riemann_form` (step e) — torsion-free curvature
  expansion;
* `bochner_per_summand_assembled` (step f) — combined per-summand identity
  $g(\nabla_B \nabla_B \nabla f, W) - g(\nabla_{\nabla_B B} \nabla f, W)
  = g(R(B, W)\,\nabla f, B) + \mathrm{d}(b \mapsto \mathrm{Hess}\,f(B, B))(x)\cdot W
  - 2\,\mathrm{Hess}\,f(B, \nabla_W B)(x)$.

**Outer-assembly layer outstanding** (~400 LOC):
1. Full 3-slot tensoriality of `riemannCurvature` (Z-slot Leibniz
   `riemannCurvature_smul_third_scalar_field` landed; Z-slot vanishing
   via chart frame + bump, X/Y-slot mirrors, pointwise-eq bundling all TODO).
2. `heart_curvature_orthonormal_sum_eq_ricci` analog:
   $\sum_i g(R(B_i, W) \nabla f, B_i) = \mathrm{Ric}(\nabla f, W)$.
3. `sum_hessianBilin_smoothOrthoFrame_eventuallyEq_laplacian`:
   $\sum_i \mathrm{Hess}\,f(B_i, B_i) =^\mathrm{nbhd} \Delta_g f$ via Stage 5+7.
4. `sum_hessianBilin_smoothOrthoFrame_cov_eq_zero`:
   $\sum_i \mathrm{Hess}\,f(B_i, \nabla_W B_i) = 0$ via antisymm-symm cancel.
5. mfderiv distributes over `Finset.sum`.
6. Final assembly into this narrowed sorry.

References: Petersen Ch 7 §1 Prop 33; do Carmo §6; external
`hInner_discharge` (`Bochner.lean:3257`). -/
private theorem sum_inner_secondCovDerivAt_grad_smoothOrthoFrame
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ∑ i, metricInner x
        (secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
            (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x := by
  sorry

private theorem sum_inner_secondCovDerivAt_grad_eq_inner_grad_laplacian_add_ricci
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ∑ i, metricInner x
        (secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
            (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x := by
  classical
  -- Wrap ∇f as a `SmoothVectorField` to access
  -- `leviCivitaConnection_smoothAt_const_dir` for the right-slot
  -- bilinearity hypothesis of `secondCovDerivAt`.
  let gradF : SmoothVectorField I M :=
    { toFun := manifoldGradient (I := I) f, smooth := h_grad }
  have h_const_dir : ∀ w : TangentSpace I x,
      TangentSmoothAt
        (fun y : M => covDerivAt (manifoldGradient (I := I) f) y w) x :=
    fun w => leviCivitaConnection_smoothAt_const_dir gradF (w : E) x
  -- Bilinear form `B(v)(w) := ⟨secondCovDerivAt ∇f x v w, ∇f x⟩`.
  -- Left slot: linear from `secondCovDerivAt_add_left/smul_left` (no
  -- smoothness needed). Right slot: linear from
  -- `secondCovDerivAt_add_right/smul_right` (smoothness via
  -- `h_const_dir`).
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w => metricInner x
        (secondCovDerivAt (I := I) (M := M)
          (manifoldGradient (I := I) f) x v w)
        (manifoldGradient (I := I) f x))
      (fun v₁ v₂ w => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x (v₁ + v₂) w)
            (manifoldGradient (I := I) f x)
          = metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v₁ w)
              (manifoldGradient (I := I) f x)
            + metricInner x
                (secondCovDerivAt (manifoldGradient (I := I) f) x v₂ w)
                (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_add_left, metricInner_add_left])
      (fun c v w => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x (c • v) w)
            (manifoldGradient (I := I) f x)
          = c • metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v w)
              (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_smul_left, metricInner_smul_left]; rfl)
      (fun v w₁ w₂ => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x v (w₁ + w₂))
            (manifoldGradient (I := I) f x)
          = metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v w₁)
              (manifoldGradient (I := I) f x)
            + metricInner x
                (secondCovDerivAt (manifoldGradient (I := I) f) x v w₂)
                (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_add_right (h_smooth_dir := h_const_dir),
            metricInner_add_left])
      (fun c v w => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x v (c • w))
            (manifoldGradient (I := I) f x)
          = c • metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v w)
              (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_smul_right
              (h_smooth_dir := h_const_dir w),
            metricInner_smul_left]; rfl) with hB_def
  -- Stage 7 basis-change bridge: the diagonal trace of `B` over
  -- `smoothOrthoFrame · x` equals the diagonal trace over
  -- `stdOrthonormalBasis ℝ (T_xM)`. Direct application of
  -- `Tensor.sum_diagonal_smoothOrthoFrame_eq_std`.
  have h_bridge :=
    Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x B
  -- Unfold `B` in `h_bridge` to expose the explicit
  -- `metricInner ∘ secondCovDerivAt ∘ ∇f` form on both sides via
  -- `LinearMap.mk₂_apply`.
  rw [hB_def] at h_bridge
  simp only [LinearMap.mk₂_apply] at h_bridge
  -- Now `h_bridge : narrowed-sorry LHS = original-sorry LHS`.
  -- Rewriting the goal's LHS with `← h_bridge` reduces to the
  -- narrowed sorry.
  rw [← h_bridge]
  exact sum_inner_secondCovDerivAt_grad_smoothOrthoFrame
    f x h_interior hf h_grad

/-- **G — heart-of-Bochner reduction**: the connection Laplacian on $\nabla f$
contracted with $\nabla f$ equals the inner product of $\nabla f$ with the
gradient of the scalar Laplacian, plus the Ricci correction:
$$\langle \Delta_\nabla \nabla f,\, \nabla f\rangle_g
   \;=\; \langle \nabla f,\, \nabla\,\Delta_g f\rangle_g
       + \mathrm{Ric}(\nabla f,\, \nabla f).$$

The outer assembly is proved here: the LHS unfolds via
`connectionLaplacian_eq_sum_secondCovDerivAt` and bilinearity of
`metricInner` (`sum_inner`) to the diagonal trace
$\sum_i \langle (\nabla^2 \nabla f)(\varepsilon_i, \varepsilon_i),
\nabla f\rangle_g(x)$, which equals the RHS by the sum identity
`sum_inner_secondCovDerivAt_grad_eq_inner_grad_laplacian_add_ricci` (the
heart-of-Bochner sum identity, currently a focused PRE-PAPER sorry).

Used in `bochner_weitzenboeck` (assembly step H) along with E. -/
theorem connectionLaplacian_grad_eq_grad_laplacian_add_ricci
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ⟪connectionLaplacian (grad_g[I] f) x, (grad_g[I] f) x⟫_g
      = ⟪(grad_g[I] f) x, (grad_g[I] (Δ_g[I] f)) x⟫_g
        + Ric_g((grad_g[I] f) x, (grad_g[I] f) x) x := by
  show metricInner x
        (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
          (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x
  rw [connectionLaplacian_eq_sum_secondCovDerivAt]
  -- Push sum out of `metricInner` via bilinearity (`= ⟪·,·⟫_ℝ` def-eq + `sum_inner`)
  change ⟪∑ i,
        secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i),
      manifoldGradient (I := I) f x⟫_ℝ = _
  rw [sum_inner]
  exact sum_inner_secondCovDerivAt_grad_eq_inner_grad_laplacian_add_ricci
    f x h_interior hf h_grad

/-! ## Bochner–Weitzenböck identity -/

/-- **Bochner–Weitzenböck identity**:
$$\tfrac{1}{2}\,\Delta_g\,|\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f, \nabla f).$$

Proved by combining `leibniz_trace_reduction` (E) and
`connectionLaplacian_grad_eq_grad_laplacian_add_ricci` (G):
$$\tfrac{1}{2} \Delta_g |\nabla f|_g^2
  \;\overset{E}{=}\; \langle \Delta_\nabla \nabla f, \nabla f\rangle_g + |\nabla^2 f|_g^2
  \;\overset{G}{=}\; \langle \nabla f, \nabla(\Delta_g f)\rangle_g
                     + \mathrm{Ric}(\nabla f, \nabla f) + |\nabla^2 f|_g^2.$$

Reference: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33;
do Carmo §6 (curvature commutators); Schoen-Simon 1981 §1 (variational
application). -/
theorem bochner_weitzenboeck
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x =
      ‖hess_g[I] f‖²_g x
      + ⟪(grad_g[I] f) x, (grad_g[I] (Δ_g[I] f)) x⟫_g
      + Ric_g((grad_g[I] f) x, (grad_g[I] f) x) x := by
  rw [leibniz_trace_reduction f x h_grad,
      connectionLaplacian_grad_eq_grad_laplacian_add_ricci f x h_interior hf h_grad]
  abel

end Operators
end Riemannian
