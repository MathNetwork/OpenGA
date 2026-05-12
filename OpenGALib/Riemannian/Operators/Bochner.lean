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

/-! ## Helper: `mfderiv` of the gradient norm squared

The function $|\nabla f|_g^2 : M \to \mathbb{R}$ is $y \mapsto
\langle \nabla f(y), \nabla f(y)\rangle_g$. Its `mfderiv` at $y$ in direction
$v$ is $2 \langle \nabla_v \nabla f, \nabla f\rangle_g(y)$ — direct application
of metric-compatibility on $(\nabla f, \nabla f)$ plus inner-product symmetry.

This is the fundamental level-1 differentiation step used in `leibniz_trace_reduction` (E).
-/

/-- $\mathrm{d}(|\nabla f|_g^2)(y)\,v = 2 \langle \nabla_v \nabla f, \nabla f\rangle_g(y)$.

Pointwise hypothesis on the gradient: `TangentSmoothAt (∇f) y`. -/
theorem mfderiv_gradientNormSq_apply
    (f : M → ℝ) (y : M) (v : TangentSpace I y)
    (h_grad_y : TangentSmoothAt (manifoldGradient (I := I) f) y) :
    mfderiv I 𝓘(ℝ, ℝ) (‖grad_g[I] f‖²_g) y v
      = 2 * metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y v)
              (manifoldGradient (I := I) f y) := by
  -- ‖grad_g[I] f‖²_g = fun z => metricInner z (∇f z) (∇f z) (MetricNormSq instance)
  show mfderiv I 𝓘(ℝ, ℝ)
        (fun z : M => metricInner z (manifoldGradient (I := I) f z)
                                      (manifoldGradient (I := I) f z)) y v = _
  -- Metric-compatibility on (X = const v, Y = ∇f, Z = ∇f) at y
  have hVsm : TangentSmoothAt (fun _ : M => (v : TangentSpace I y)) y :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt y
  have h := leviCivitaConnection_metric_compatible
    (fun _ : M => (v : TangentSpace I y))
    (manifoldGradient (I := I) f)
    (manifoldGradient (I := I) f)
    y hVsm h_grad_y h_grad_y
  -- h: mfderiv (fun z => ⟨∇f z, ∇f z⟩) y · v
  --    = ⟨lcc.toFun ∇f y v, ∇f y⟩ + ⟨∇f y, lcc.toFun ∇f y v⟩
  -- = 2 ⟨covDerivAt ∇f y v, ∇f y⟩ (by inner-product symmetry)
  rw [h]
  rw [metricInner_comm y (manifoldGradient (I := I) f y)
       ((leviCivitaConnection (I := I) (M := M)).toFun
          (manifoldGradient (I := I) f) y v)]
  -- `covDerivAt Y x = lcc.toFun Y x` definitionally, then `a + a = 2 * a`.
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

/-! ## Per-direction expansion of the gradient-norm-squared scalar Hessian -/

/-- The connection Hessian of $g = |\nabla f|_g^2$ on a chart-frame constant
direction $v$ decomposes into a `secondCovDerivAt` $\langle\,\cdot\,, \nabla f\rangle_g$
piece plus a Hessian Frobenius$^2$-like piece:
$$\mathrm{Hess}\,g(v, v)(x) \;=\; 2 \bigl(\langle (\nabla^2 \nabla f)(v, v),
   \nabla f\rangle_g + \|(\nabla_v \nabla f)\|_g^2 \bigr)(x).$$

Combines (i) `hessian_eq_mDirDeriv_iterate_sub_chris` (bridge to iterated
`mDirDeriv` form), (ii) `mfderiv_gradientNormSq_apply` (level-1 metric-
compat to expand `mDirDeriv g y v`), and (iii) a level-2 metric-compat
on $(v_\text{const}, \nabla_v\nabla f, \nabla f)$ at $x$ — the level-2 step
needs `TangentSmoothAt (covDerivAt ∇f · v) x`, discharged via
`leviCivitaConnection_smoothAt_const_dir` on the `SmoothVectorField`
wrapper of $\nabla f$ (using the C^∞ hypothesis `h_grad`). -/
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
  -- Smoothness witnesses
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
  -- Level-2 smoothness of `S_v y := covDerivAt ∇f y v` at x (C² gap discharged)
  have hSvsm : TangentSmoothAt
      (fun y : M =>
        (leviCivitaConnection (I := I) (M := M)).toFun
          (manifoldGradient (I := I) f) y (v : TangentSpace I x)) x :=
    leviCivitaConnection_smoothAt_const_dir gradSV (v : E) x
  -- Apply bridge: hessian g (const v) (const v) x
  --   = mDirDeriv (fun y => mDirDeriv g y v) x v
  --     - mDirDeriv g x (covDeriv (const v) (const v) x)
  have h_bridge := Riemannian.Operators.hessian_eq_mDirDeriv_iterate_sub_chris
    (‖grad_g[I] f‖²_g) (fun _ : M => (v : TangentSpace I x))
    (fun _ : M => (v : TangentSpace I x)) x
    h_grad_g_smoothAt hVsm hVsm
  -- Substitute `mDirDeriv g y v = 2 ⟨covDerivAt ∇f y v, ∇f y⟩` in the inner section
  have h_inner_eq :
      (fun y : M => mDirDeriv (I := I) (‖grad_g[I] f‖²_g) y (v : TangentSpace I x))
        = (fun y : M => 2 * metricInner y
                    (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
                    (manifoldGradient (I := I) f y)) := by
    funext y
    exact mfderiv_gradientNormSq_apply f y v (h_grad_smoothAt y)
  rw [h_inner_eq] at h_bridge
  -- Substitute `mDirDeriv g x · = 2 ⟨covDerivAt ∇f x ·, ∇f x⟩` in the chris term
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
  -- Pull `2` out of the iterated mDirDeriv: `mDirDeriv (2 • h) x v = 2 • mDirDeriv h x v`
  have h_inner_smooth :
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) f y)) x :=
    metricInner_mdifferentiableAt_of_tangentSmoothAt hSvsm (h_grad_smoothAt x)
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
    -- `(2 • CLM) v = 2 • (CLM v) = 2 * (CLM v)` for ℝ-valued CLM
    show (2 : ℝ) • (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => metricInner y
            (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
            (manifoldGradient (I := I) f y)) x) v
        = 2 * mDirDeriv (I := I) (fun y : M => metricInner y
              (covDerivAt (manifoldGradient (I := I) f) y (v : TangentSpace I x))
              (manifoldGradient (I := I) f y)) x v
    rfl
  rw [h_pull_two] at h_bridge
  -- Apply level-2 metric-compat to expand the inner mDirDeriv
  -- (X = const v, Y = S_v = fun y => covDerivAt ∇f y v, Z = ∇f) at x
  have h_compat2 := leviCivitaConnection_metric_compatible
    (fun _ : M => (v : TangentSpace I x))
    (fun y : M =>
      (leviCivitaConnection (I := I) (M := M)).toFun
        (manifoldGradient (I := I) f) y (v : TangentSpace I x))
    (manifoldGradient (I := I) f) x hVsm hSvsm (h_grad_smoothAt x)
  -- h_compat2 : mfderiv (fun y => ⟨S_v y, ∇f y⟩) x v
  --           = ⟨covDerivAt S_v x v, ∇f x⟩ + ⟨S_v x, covDerivAt ∇f x v⟩
  -- The mfderiv form on LHS = mDirDeriv form. Convert lcc.toFun to covDerivAt
  -- (def-eq) so h_compat2's pattern matches h_bridge.
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
  -- so it matches the `secondCovDerivAt` def shape.
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
  -- h_bridge now has the fully-expanded form. Goal is to read off the result.
  -- Let's show the goal equals h_bridge's RHS modulo (i) metricInner_sub_left to combine,
  -- (ii) recognition of the secondCovDerivAt def.
  --
  -- h_bridge:
  -- hessian g (const v) (const v) x
  --   = 2 * (⟨covDerivAt S_v x v, ∇f x⟩ + ⟨S_v x, covDerivAt ∇f x v⟩)
  --     - 2 * ⟨covDerivAt ∇f x (covDeriv (const v) (const v) x), ∇f x⟩
  --
  -- S_v x = (lcc.toFun ∇f) x v = covDerivAt ∇f x v (def-eq).
  -- covDeriv (const v) (const v) x = (lcc.toFun (const v)) x v = covDerivAt (const v) x v.
  -- secondCovDerivAt (∇f) x v v = covDerivAt S_v x v - covDerivAt ∇f x (covDerivAt (const v) x v)
  -- (by `secondCovDerivAt_def` and `S_v` definition).
  --
  -- So after metricInner_sub_left + rearrangement, h_bridge gives the goal RHS.
  rw [h_bridge]
  -- Goal: 2 * (⟨covDerivAt S_v x v, ∇f x⟩ + ⟨covDerivAt ∇f x v, covDerivAt ∇f x v⟩)
  --     - 2 * ⟨covDerivAt ∇f x (covDerivAt (const v) x v), ∇f x⟩
  --   = 2 * (⟨secondCovDerivAt(∇f) x v v, ∇f x⟩ + ⟨covDerivAt ∇f x v, covDerivAt ∇f x v⟩)
  -- which reduces to:
  --   ⟨covDerivAt S_v x v - covDerivAt ∇f x (covDerivAt (const v) x v), ∇f x⟩
  --     = ⟨secondCovDerivAt(∇f) x v v, ∇f x⟩
  -- which is by `secondCovDerivAt_def` + `metricInner_sub_left`.
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
  -- Goal LHS uses `(∇[fun x ↦ v] fun x ↦ v) x = covDerivAt (fun _ => v) x v` (def-eq)
  -- linarith should close given h_secondCD
  linarith [h_secondCD]

/-! ## Two intermediates (E, G) for the Bochner identity -/

/-- **E — Leibniz trace reduction**: the scalar Laplacian of $|\nabla f|_g^2$
decomposes into a connection-Laplacian term and a Hessian Frobenius² term:
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2 \;=\;
   \langle \Delta_\nabla \nabla f,\, \nabla f \rangle_g
   + |\nabla^2 f|_g^2.$$

This is the trace form of the Leibniz product rule applied twice to
$\langle \nabla f, \nabla f\rangle_g$ in the $g$-orthonormal frame
`stdOrthonormalBasis ℝ (TangentSpace I x)`.

**Sorry: PRE-PAPER**. Closure path:
1. apply `leviCivitaConnection_metric_compatible` to $(\nabla f, \nabla f, \varepsilon_i)$
   to get $\nabla_{\varepsilon_i} \langle \nabla f, \nabla f\rangle_g
       = 2 \langle \nabla_{\varepsilon_i} \nabla f, \nabla f\rangle_g$;
2. apply metric-compat again to differentiate $\langle \nabla_{\varepsilon_i} \nabla f, \nabla f\rangle_g$
   in the $\varepsilon_i$-direction, yielding
   $\langle \nabla_{\varepsilon_i} \nabla_{\varepsilon_i} \nabla f, \nabla f\rangle_g
     + \langle \nabla_{\varepsilon_i} \nabla f, \nabla_{\varepsilon_i} \nabla f\rangle_g$;
3. sum over $i$, identify the second sum with $|\nabla^2 f|_g^2$ via
   `frobeniusSq` in the $g$-orthonormal frame;
4. reduce the iterated chart-coord trace
   $\sum_i \mathrm{mfderiv}^2 \,(|\nabla f|^2_g)\,\varepsilon_i\,\varepsilon_i$
   to $\Delta_g(|\nabla f|^2_g)\,(x)$ via `scalarLaplacian` definition + the
   Christoffel-correction matching of `secondCovDerivAt` against
   `connectionLaplacian` (`connectionLaplacian_eq_sum_secondCovDerivAt`).

Used in `bochner_weitzenboeck` (assembly step H) along with G. -/
theorem leibniz_trace_reduction
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
      = ⟪connectionLaplacian (grad_g[I] f) x, (grad_g[I] f) x⟫_g
        + ‖hess_g[I] f‖²_g x := by
  sorry

/-- **G — heart-of-Bochner reduction**: the connection Laplacian on $\nabla f$
contracted with $\nabla f$ equals the inner product of $\nabla f$ with the
gradient of the scalar Laplacian, plus the Ricci correction:
$$\langle \Delta_\nabla \nabla f,\, \nabla f\rangle_g
   \;=\; \langle \nabla f,\, \nabla\,\Delta_g f\rangle_g
       + \mathrm{Ric}(\nabla f,\, \nabla f).$$

This is the trace form of the Ricci identity (D) applied to $Z = \nabla f$,
with one slot contracted via the $g$-orthonormal frame, using Hessian
symmetry (B) to swap $\nabla^2 f(\varepsilon_i, \varepsilon_j)
\leftrightarrow \nabla^2 f(\varepsilon_j, \varepsilon_i)$.

**Sorry: PRE-PAPER**. Closure path:
1. expand `connectionLaplacian (∇f) x` via
   `connectionLaplacian_eq_sum_secondCovDerivAt` into
   $\sum_i \nabla^2 (\nabla f)(\varepsilon_i, \varepsilon_i)\,(x)$;
2. apply `secondCovDerivAt_sub_swap_eq_riemannCurvature` (D.2) summed over $i$,
   in conjunction with `hessianBilin_symm` (B) to swap the inner indices
   in $\langle \nabla_{\varepsilon_i}\nabla_{\varepsilon_i}\nabla f,
      \nabla f\rangle_g$ via the Hessian's $(0,2)$ symmetry;
3. recognise the sum-of-trace term $\sum_i \langle R(\varepsilon_i, \nabla f) \nabla f,
   \varepsilon_i\rangle_g$ as $\mathrm{Ric}_g(\nabla f, \nabla f)\,(x)$ via
   `ricciTensor_eq_sum_inner_orthonormal` (F);
4. recognise the remaining trace as $\langle \nabla f, \nabla(\Delta_g f)\rangle_g$
   via gradient duality `manifoldGradient_inner_eq` and the trace
   identification `scalarLaplacian_eq_laplacian_hessianBilin`.

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
  sorry

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
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
    = ‖hess_g[I] f‖²_g x
      + ⟪(grad_g[I] f) x,
         (grad_g[I] (Δ_g[I] f)) x⟫_g
      + Ric_g((grad_g[I] f) x,
              (grad_g[I] f) x) x := by
  rw [leibniz_trace_reduction f x h_interior hf h_grad,
      connectionLaplacian_grad_eq_grad_laplacian_add_ricci f x h_interior hf h_grad]
  abel

end Operators
end Riemannian
