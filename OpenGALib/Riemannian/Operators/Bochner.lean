import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Gradient
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
open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

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

/-- **Heart-of-Bochner sum identity** (the per-summand-assembled core that
G reduces to): summing the diagonal trace of $\nabla^2(\nabla f)$ paired
with $\nabla f$ over the $g$-orthonormal frame produces the
$\langle \nabla f, \nabla(\Delta_g f)\rangle_g + \mathrm{Ric}(\nabla f,
\nabla f)$ decomposition.

**Sorry: PRE-PAPER**. Algebraic chain (textbook Bochner derivation,
cf. Petersen §9, do Carmo §6, external `secondCovDeriv_weitzenbock`):
1. **Step 1 (Hess-sym swap, per i)**: $g(\nabla^2_{\varepsilon_i,\varepsilon_i}\nabla f, \nabla f)
   = g(\nabla^2_{\varepsilon_i,\nabla f}\nabla f, \varepsilon_i)$ at $x$. Uses
   metric-compat $\times 2$ and `hessianBilin_symm` (B).
2. **Step 2 (smooth-frame Ricci identity)**: now closed via D.3 —
   `secondCovDerivSection_sub_swap_eq_riemannCurvature` in
   `OpenGALib/Riemannian/Operators/ConnectionLaplacian.lean`. Lifting
   the constant frame $\tilde\varepsilon_i$ and the smooth gradient
   section $\nabla f$, gives
   $\nabla^2_{\varepsilon_i,\nabla f}\nabla f - \nabla^2_{\nabla f,\varepsilon_i}\nabla f
       = R(\tilde\varepsilon_i,\nabla f)\nabla f$ at $x$.
3. **Step 3 (Ric identification)**: $\sum_i g(R(\tilde\varepsilon_i,\nabla f)\nabla f,
   \varepsilon_i) = \mathrm{Ric}_g(\nabla f,\nabla f)$ at $x$ via
   `riemannCurvature_antisymm` + Riemann-tensor block symmetry +
   `ricciTensor_eq_sum_inner_orthonormal` (F) + tensoriality
   (smooth section $\nabla f$ vs constant lift of $\nabla f x$ at $x$).
4. **Step 4 (∇Δf identification — INFRASTRUCTURE GAP)**:
   $\sum_i g(\nabla^2_{\nabla f,\varepsilon_i}\nabla f, \varepsilon_i)(x)
   = g(\nabla f, \nabla\Delta_g f)(x)$. Requires producing a
   **smooth $g$-orthonormal frame near $x$** that extends
   $\{\varepsilon_i\} = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,(T_xM)$.
   The chart-frame constant lift $\tilde\varepsilon_i$ is *not*
   $g$-orthonormal at $y \ne x$, so the chart-trace function
   $T_\mathrm{chart}(y) := \sum_i \mathrm{Hess}\,f(y)(\varepsilon_i,\varepsilon_i)$
   does **not** equal $\Delta_g f(y)$ off $x$. The $\nabla f$-direction
   derivative therefore picks up a Christoffel/Gram-correction term that
   the constant lift cannot cancel.

**Repair plan**: port `external/differential-geometry/`'s
`RicciIdentitySmoothFrame.lean` (~1443 lines) — chart-bump-multiplied
$g$-Gram-Schmidt of the chart frame yields `smoothOrthoFrame g x i`,
which is $g$-orthonormal at every point of `smoothOrthoFrameNbhd x`
and reduces to `stdOrthonormalBasis` at $x$. Restating this lemma
against `smoothOrthoFrame` (instead of the constant lift of
`stdOrthonormalBasis`) makes Step 4 mechanical. The basis-change
between `smoothOrthoFrame g x · x` and `stdOrthonormalBasis ℝ (T_x M)`
at $x$ is an orthogonal transformation; the trace $\sum_i ⟨\Delta_\nabla\nabla f,
\varepsilon_i⟩ \cdot ⟨\nabla f, \varepsilon_i⟩$ is invariant under this
basis change, so the original statement (in `stdOrthonormalBasis`)
follows from the smooth-frame version at $x$.

**Repair owner**: framework self-build. Estimated scope: ~500–1000
LOC port (chart bump + Gram-Schmidt + smoothness on the bump
neighbourhood + at-$x$ orthonormality + basis-change at $x$). -/
private theorem sum_inner_secondCovDerivAt_grad_eq_inner_grad_laplacian_add_ricci
    [IsManifold I 2 M]
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
  sorry

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
    [IsManifold I 2 M]
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
    [IsManifold I 2 M]
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
