import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature
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
    (h_grad : ∀ y : M, TangentSmoothAt (manifoldGradient (I := I) f) y) :
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
    (h_grad : ∀ y : M, TangentSmoothAt (manifoldGradient (I := I) f) y) :
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
    (h_grad : ∀ y : M, TangentSmoothAt (manifoldGradient (I := I) f) y) :
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
