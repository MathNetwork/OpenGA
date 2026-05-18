import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Curvature.Tensoriality
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame.Smoothness
import OpenGALib.Util.Notation
import Mathlib.Analysis.InnerProductSpace.Trace
import OpenGALib.Riemannian.Util.CovDerivBridges

/-!
# Bochner expansion: Ricci-identity-driven chain

Algebraic expansion of $\langle \Delta_\nabla \nabla f, \nabla f\rangle_g$
into $\langle \nabla f, \nabla(\Delta_g f)\rangle_g + \mathrm{Ric}(\nabla f, \nabla f)$,
realised as a four-step chain on the second covariant derivative:

* Hess-sym swap of `(∇² ∇f)`'s inner-product partner
* D.2 inner-form swap of the outer pair (Ricci identity)
* Ricci identification (curvature trace = Ricci bilinear)
* Smooth-trace identification (Hessian trace = `Δ_g f` locally; cov-skew
  cancellation of cross-Christoffel)

The packaged result
`sum_inner_secondCovDerivAt_grad_smoothOrthoFrame_of_inner_form` exposes the
four steps in the form consumed by `Bochner/PerSummand.lean`'s
`bochner_connectionLaplacian_grad_decomposition`.

Parallel to `Bochner/HessianExpansion.lean`, which expands $\mathrm{Hess}(|\nabla f|^2)$
on the gradient side.
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

/-! ## Building block: Ricci as g-orthonormal trace -/

/-- **Math.** **Ricci as a g-orthonormal trace**:
$$\mathrm{Ric}_g(V, W)(x) \;=\; \sum_i \bigl\langle \varepsilon_i,\,
  R(\varepsilon_i,\,V)\,W\,(x)\bigr\rangle_g,$$
for $\{\varepsilon_i\} = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,(T_xM)$.
Unfolds `ricci` via `LinearMap.trace_eq_sum_inner` on the curvature
endomorphism. -/
theorem ricciTensor_eq_sum_inner_orthonormal
    [IsManifold I 2 M]
    (x : M) (V W : TangentSpace I x) :
    Ric_g(V, W) x =
      ∑ i, ⟪(stdOrthonormalBasis ℝ (TangentSpace I x)) i,
            curvatureEndo (HasMetric.metric)
              (SmoothVectorField.const (I := I) (M := M) V)
              (SmoothVectorField.const (I := I) (M := M) W) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)⟫_ℝ := by
  show ricci (HasMetric.metric)
        (SmoothVectorField.const (I := I) (M := M) V)
        (SmoothVectorField.const (I := I) (M := M) W) x = _
  unfold ricci
  exact LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TangentSpace I x))

/-! ## Conditional infrastructure for the heart-of-Bochner closure

Two conditional reductions, ported from `external/differential-geometry`'s
`heart_of_bochner_curvature_term` (Item 5) and
`heart_of_bochner_of_inner_form` (Item 8). They expose the natural
"shape" of the algebraic content of the heart-of-Bochner closure, taking
as input the relevant algebraic identity and producing the form the
downstream consumer needs. These conditionals do not close any sorry by
themselves — they package the assumptions cleanly. -/

/-- **Math.** **Hess-sym swap of the inner-product partner for
$\nabla^2 \nabla f$**: for constant lifts of $v, w, z$ at $x$,
$$\langle (\nabla^2 \nabla f)(v, w),\, z\rangle_g(x)
  = \langle (\nabla^2 \nabla f)(v, z),\, w\rangle_g(x).$$

Routes through metric-compatibility at $x$ on $(V, \partial_W \nabla f, Z)$
to convert each side into an `mfderiv` of `hessianBilin f y _ _` at $x$ plus
Christoffel-correction terms. The (w ↔ z) swap closes via the neighbourhood
Hessian-symmetry hypothesis `h_eventual_sym` (lifted through V-derivative
by `EventuallyEq.mfderiv_eq`) and pointwise `hessianBilin_symm` for the
Christoffel terms.

Ported from do Carmo §6 / Petersen Ch 7 §1 Prop 33. -/
theorem metricInner_secondCovDerivAt_grad_swap_of_hess_eventual_sym
    [IsManifold I 2 M]
    (f : M → ℝ) (x : M) (v w z : TangentSpace I x)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (h_grad : TangentSmoothAt (manifoldGradient (I := I) HasMetric.metric f) x)
    (h_grad_const_w : TangentSmoothAt
        (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y w) x)
    (h_grad_const_z : TangentSmoothAt
        (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y z) x)
    (h_eventual_sym : (fun y : M => hessianBilin (I := I) HasMetric.metric f y w z)
        =ᶠ[𝓝 x] (fun y : M => hessianBilin (I := I) HasMetric.metric f y z w)) :
    metricInner x (secondCovDerivAt (I := I) (M := M) HasMetric.metric
        (manifoldGradient (I := I) HasMetric.metric f) x v w) z =
      metricInner x (secondCovDerivAt (I := I) (M := M) HasMetric.metric
        (manifoldGradient (I := I) HasMetric.metric f) x v z) w := by
  classical
  -- Constant lifts of v, w, z at x.
  set V : VectorFieldSection I M := fun _ => (v : TangentSpace I x) with hV_def
  set W : VectorFieldSection I M := fun _ => (w : TangentSpace I x) with hW_def
  set Z : VectorFieldSection I M := fun _ => (z : TangentSpace I x) with hZ_def
  have hVsm : TangentSmoothAt V x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  have hWsm : TangentSmoothAt W x :=
    (SmoothVectorField.const (I := I) (M := M) (w : E)).smoothAt x
  have hZsm : TangentSmoothAt Z x :=
    (SmoothVectorField.const (I := I) (M := M) (z : E)).smoothAt x
  -- V-derivative bridge via EventuallyEq.mfderiv_eq (applied at v).
  have h_eq_mfderiv :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) HasMetric.metric f y w z) x
      = mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) HasMetric.metric f y z w) x :=
    Filter.EventuallyEq.mfderiv_eq h_eventual_sym
  have h_eq_at_v :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) HasMetric.metric f y w z) x v
      = mfderiv I 𝓘(ℝ, ℝ) (fun y : M => hessianBilin (I := I) HasMetric.metric f y z w) x v :=
    congrArg (· v) h_eq_mfderiv
  -- Metric-compatibility at x; bridge ∇ → `.toFun` form for `rw [h_id_W/Z]`.
  have h_compat_W := leviCivitaConnection_metric_compatible HasMetric.metric
    V (fun y => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y w) Z x
    hVsm h_grad_const_w hZsm
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h_compat_W
  have h_compat_Z := leviCivitaConnection_metric_compatible HasMetric.metric
    V (fun y => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y z) W x
    hVsm h_grad_const_z hWsm
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h_compat_Z
  -- Rewrite metric-compat LHS into `hessianBilin f y w z` / `f y z w` form.
  have h_hess_W :
      (fun y : M => metricInner y (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y w) (Z y))
        = (fun y : M => hessianBilin (I := I) HasMetric.metric f y w z) := by
    funext y; show metricInner y _ z = hessianBilin (I := I) HasMetric.metric f y w z; rfl
  have h_hess_Z :
      (fun y : M => metricInner y (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y z) (W y))
        = (fun y : M => hessianBilin (I := I) HasMetric.metric f y z w) := by
    funext y; show metricInner y _ w = hessianBilin (I := I) HasMetric.metric f y z w; rfl
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
      hessianBilin (I := I) HasMetric.metric f x a b = hessianBilin (I := I) HasMetric.metric f x b a :=
    fun a b => hessianBilin_symm (I := I) HasMetric.metric f x h_interior hf_2 h_grad a b
  -- Christoffel corrections as tangent-space elements at x.
  set Γvw : TangentSpace I x :=
    (leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun W x v with hΓvw_def
  set Γvz : TangentSpace I x :=
    (leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun Z x v with hΓvz_def
  -- Identify the second metric-compat term as hessianBilin (cross terms).
  -- ⟨covDerivAt HasMetric.metric ∇f x w, Γvz⟩ = hessianBilin f x w Γvz (by def).
  have h_id_W : metricInner x (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun Z x v)
      = hessianBilin (I := I) HasMetric.metric f x w Γvz := rfl
  have h_id_Z : metricInner x (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x z)
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun W x v)
      = hessianBilin (I := I) HasMetric.metric f x z Γvw := rfl
  -- Cast h_compat_W / h_compat_Z to typeclass `metricInner` abbrev form for rw matching.
  change ((mfderiv% fun y : M => hessianBilin (I := I) HasMetric.metric f y w z) x) v
      = metricInner x
          ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
            (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y w) x v) z
        + metricInner x (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
          ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun Z x v)
    at h_compat_W
  change ((mfderiv% fun y : M => hessianBilin (I := I) HasMetric.metric f y z w) x) v
      = metricInner x
          ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
            (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y z) x v) w
        + metricInner x (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x z)
          ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun W x v)
    at h_compat_Z
  rw [h_id_W] at h_compat_W
  rw [h_id_Z] at h_compat_Z
  -- Now unfold secondCovDerivAt and metric-inner-sub.
  show metricInner x
      (covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y w) x v
        - covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x
            (covDerivAt HasMetric.metric (Y := fun _ : M => (w : TangentSpace I x)) x v)) z
    = metricInner x
      (covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y z) x v
        - covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x
            (covDerivAt HasMetric.metric (Y := fun _ : M => (z : TangentSpace I x)) x v)) w
  rw [metricInner_sub_left, metricInner_sub_left]
  -- Identify outer terms: ⟨covDerivAt HasMetric.metric (∂_W ∇f) x v, z⟩ = ⟨lcc.(∂_W ∇f) x v, z⟩ (rfl).
  -- Identify Christoffel terms: ⟨covDerivAt HasMetric.metric ∇f x Γvw, z⟩ = hessianBilin f x Γvw z (rfl).
  show metricInner x ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
        (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y w) x v) z
      - hessianBilin (I := I) HasMetric.metric f x Γvw z
    = metricInner x ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
        (fun y : M => covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) y z) x v) w
      - hessianBilin (I := I) HasMetric.metric f x Γvz w
  -- Cross-term Hess-sym: hessianBilin f x z Γvw = hessianBilin f x Γvw z, etc.
  have h_sym_zΓvw : hessianBilin (I := I) HasMetric.metric f x z Γvw
      = hessianBilin (I := I) HasMetric.metric f x Γvw z := h_hess_sym z Γvw
  have h_sym_wΓvz : hessianBilin (I := I) HasMetric.metric f x w Γvz
      = hessianBilin (I := I) HasMetric.metric f x Γvz w := h_hess_sym w Γvz
  -- Combine via linear_combination on h_compat_W, h_compat_Z, h_eq_at_v, h_sym_*.
  -- A - hA = B - hB  where
  --   h_compat_W: P = A + hB'  (where hB' = h_sym_wΓvz ↦ hB)
  --   h_compat_Z: Q = B + hA'  (where hA' = h_sym_zΓvw ↦ hA)
  --   h_eq_at_v:  P = Q
  --   h_sym_wΓvz: hB' = hB
  --   h_sym_zΓvw: hA' = hA
  -- ⇒ A - hA = (P - hB') - hA = (Q - hB) - hA' = (B + hA' - hB) - hA' = B - hB ✓
  linear_combination -h_compat_W + h_compat_Z + h_eq_at_v + h_sym_zΓvw - h_sym_wΓvz

/-- **Math.** Discharge of `h_eventual_sym` from `[I.Boundaryless]`.
Propagates the strict-interior fact (vacuous under `[I.Boundaryless]`) to
a nbhd via `extChartAt_self_eventually_mem_closure_interior_range` and
applies pointwise `hessianBilin_symm` to feed
`metricInner_secondCovDerivAt_grad_swap_of_hess_eventual_sym`. -/
theorem hessianBilin_eventually_symm_of_strict_interior
    [IsManifold I 2 M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (w z : TangentSpace I x) :
    (fun y : M => hessianBilin (I := I) HasMetric.metric f y w z)
      =ᶠ[𝓝 x] (fun y : M => hessianBilin (I := I) HasMetric.metric f y z w) := by
  have h_strict : extChartAt I x x ∈ interior (Set.range I) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ]; exact Set.mem_univ _
  have h_grad := manifoldGradient_smooth_of_smooth HasMetric.metric f hf
  have h_interior_nbhd :=
    extChartAt_self_eventually_mem_closure_interior_range (I := I) (M := M) h_strict
  filter_upwards [h_interior_nbhd] with y hy_interior
  -- C² of f at y from global C∞.
  have hf_2_y : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f y :=
    (hf y).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  -- Smoothness of ∇f at y from global smoothness.
  have h_grad_y : TangentSmoothAt (manifoldGradient (I := I) HasMetric.metric f) y :=
    (h_grad y).mdifferentiableAt (by simp)
  -- Pointwise Hess-sym at y. The `w z : TangentSpace I x` args are def-eq to
  -- `TangentSpace I y = E` arguments under `IsLocallyConstantChartedSpace`.
  exact hessianBilin_symm (I := I) HasMetric.metric f y hy_interior hf_2_y h_grad_y w z

/-- **Math.** Section-level Hessian symmetry on smooth vector fields,
discharged from strict interior. Variant with smooth varying sections
$X, Y$ instead of constant lifts: at every $y$ near $x$,
$\mathrm{Hess}\,f\,(X(y), Y(y))(y) = \mathrm{Hess}\,f\,(Y(y), X(y))(y)$. -/
theorem hessianBilin_section_eventually_symm_of_strict_interior
    [IsManifold I 2 M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : VectorFieldSection I M) (x : M) :
    (fun y : M => hessianBilin (I := I) HasMetric.metric f y (X y) (Y y))
      =ᶠ[𝓝 x] (fun y : M => hessianBilin (I := I) HasMetric.metric f y (Y y) (X y)) := by
  have h_strict : extChartAt I x x ∈ interior (Set.range I) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ]; exact Set.mem_univ _
  have h_grad := manifoldGradient_smooth_of_smooth HasMetric.metric f hf
  have h_interior_nbhd :=
    extChartAt_self_eventually_mem_closure_interior_range (I := I) (M := M) h_strict
  filter_upwards [h_interior_nbhd] with y hy_interior
  have hf_2_y : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f y :=
    (hf y).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have h_grad_y : TangentSmoothAt (manifoldGradient (I := I) HasMetric.metric f) y :=
    (h_grad y).mdifferentiableAt (by simp)
  exact hessianBilin_symm (I := I) HasMetric.metric f y hy_interior hf_2_y h_grad_y (X y) (Y y)

/-- **Math.** **Inner-form D.2 swap of `secondCovDerivAt`'s outer pair**:
for $v, w, z \in T_xM$,
$$\langle (\nabla^2 \nabla f)(v, w),\, z\rangle_g(x)
  = \langle (\nabla^2 \nabla f)(w, v),\, z\rangle_g(x)
    + \langle R(\mathrm{const}\,v,\,\mathrm{const}\,w)\,\nabla f,\, z\rangle_g(x).$$ -/
theorem metricInner_secondCovDerivAt_grad_eq_swap_add_curvature
    (f : M → ℝ) (x : M) (v w z : TangentSpace I x) :
    metricInner x (secondCovDerivAt (I := I) (M := M) HasMetric.metric
        (manifoldGradient (I := I) HasMetric.metric f) x v w) z
      = metricInner x (secondCovDerivAt (I := I) (M := M) HasMetric.metric
          (manifoldGradient (I := I) HasMetric.metric f) x w v) z
        + metricInner x
            (riemannCurvature HasMetric.metric (fun _ : M => (v : TangentSpace I x))
              (fun _ : M => (w : TangentSpace I x))
              (manifoldGradient (I := I) HasMetric.metric f) x) z := by
  have h := secondCovDerivAt_sub_swap_eq_riemannCurvature HasMetric.metric    (I := I) (M := M) (manifoldGradient (I := I) HasMetric.metric f) x v w
  -- h : secondCovDerivAt ∇f x v w - secondCovDerivAt ∇f x w v
  --       = riemannCurvature HasMetric.metric (const v) (const w) ∇f x
  -- Restate: secondCovDerivAt ∇f x v w = secondCovDerivAt ∇f x w v + R(const v, const w) ∇f x
  have h' : secondCovDerivAt (I := I) (M := M) HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v w
      = secondCovDerivAt (I := I) (M := M) HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w v
        + riemannCurvature HasMetric.metric (fun _ : M => (v : TangentSpace I x))
            (fun _ : M => (w : TangentSpace I x))
            (manifoldGradient (I := I) HasMetric.metric f) x := by
    rw [← h]; abel
  rw [h', metricInner_add_left]

/-- **Math.** Curvature-term metric-skew packaging:
given $g(R(B, w)\nabla f, B) + g(\nabla f, R(B, w) B) = 0$, the
heart-of-Bochner curvature summand reduces to
$- \langle \nabla f, R(B, w) B\rangle_g$ at $x$.

The hypothesis is the polarisation of `riemannCurvature_inner_self_zero`. -/
theorem heart_of_bochner_curvature_term
    (f : M → ℝ)
    {B w : VectorFieldSection I M} {x : M}
    (h_metric_skew : metricInner x
        (riemannCurvature HasMetric.metric B w (manifoldGradient (I := I) HasMetric.metric f) x) (B x)
      + metricInner x (manifoldGradient (I := I) HasMetric.metric f x)
          (riemannCurvature HasMetric.metric B w B x) = 0) :
    metricInner x
        (riemannCurvature HasMetric.metric B w (manifoldGradient (I := I) HasMetric.metric f) x) (B x) =
      - metricInner x (manifoldGradient (I := I) HasMetric.metric f x)
          (riemannCurvature HasMetric.metric B w B x) := by
  linarith

/-- **Math.** **Ricci sum identity** (heart-of-Bochner Step 3): the
curvature trace over the smooth orthonormal frame at $x$ against
$(W, \nabla f, B_i)$ equals the Ricci bilinear at $(\nabla f x, W x)$:
$$\sum_i g_x\bigl(R(B_i, W)\,\nabla f,\, B_i\bigr) \;=\;
  \mathrm{Ric}_g(\nabla f, W)(x).$$ -/
theorem heart_curvature_orthonormal_sum_eq_ricci
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (W : SmoothVectorField I M) (x : M) :
    ∑ i, metricInner x
        (riemannCurvature HasMetric.metric
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i)
          W.toFun (manifoldGradient (I := I) HasMetric.metric f) x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
      = Ric_g(manifoldGradient (I := I) HasMetric.metric f x, W.toFun x) x := by
  classical
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
    exact Set.mem_univ _
  have h_grad := manifoldGradient_smooth_of_smooth HasMetric.metric f hf
  -- Wrap `∇f`, frame, and the constant lifts of `(W x, ∇f x)` as `SmoothVectorField`.
  let gradF : SmoothVectorField I M :=
    { toFun := manifoldGradient (I := I) HasMetric.metric f, smooth := h_grad }
  let Bi : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i
      smooth := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i }
  let WV : SmoothVectorField I M :=
    SmoothVectorField.const (I := I) (M := M) (W.toFun x : E)
  let GV : SmoothVectorField I M :=
    SmoothVectorField.const (I := I) (M := M) (gradF.toFun x : E)
  -- Bilinear form `Φ(v, w) := g_x(curvatureEndo (HasMetric.metric) WV GV x v, w)`.
  set Φ : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w => metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) w)
      (fun v₁ v₂ w => by
        show metricInner x (curvatureEndo (HasMetric.metric) WV GV x (v₁ + v₂)) w
          = metricInner x (curvatureEndo (HasMetric.metric) WV GV x v₁) w
            + metricInner x (curvatureEndo (HasMetric.metric) WV GV x v₂) w
        rw [(curvatureEndo (HasMetric.metric) WV GV x).map_add, metricInner_add_left])
      (fun c v w => by
        show metricInner x (curvatureEndo (HasMetric.metric) WV GV x (c • v)) w
          = c • metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) w
        rw [(curvatureEndo (HasMetric.metric) WV GV x).map_smul, metricInner_smul_left]; rfl)
      (fun v w₁ w₂ => by
        show metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) (w₁ + w₂)
          = metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) w₁
            + metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) w₂
        rw [metricInner_add_right])
      (fun c v w => by
        show metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) (c • w)
          = c • metricInner x (curvatureEndo (HasMetric.metric) WV GV x v) w
        rw [metricInner_smul_right]; rfl) with hΦ_def
  -- Step 1: per-`i` pointwise-eq reduction.
  have h_per_i : ∀ i,
      metricInner x
          (riemannCurvature HasMetric.metric (Bi i).toFun W.toFun gradF.toFun x) ((Bi i).toFun x)
        = Φ ((Bi i).toFun x) ((Bi i).toFun x) := by
    intro i
    have hR_eq : riemannCurvature HasMetric.metric (Bi i).toFun W.toFun gradF.toFun x
        = curvatureEndo (HasMetric.metric) WV GV x ((Bi i).toFun x) := by
      show riemannCurvature HasMetric.metric (Bi i).toFun W.toFun gradF.toFun x
        = riemannCurvature HasMetric.metric
            (fun _ : M => ((Bi i).toFun x : TangentSpace I x))
            WV.toFun GV.toFun x
      exact riemannCurvature_eq_of_pointwise_eq
        (Bi i) (SmoothVectorField.const ((Bi i).toFun x : E))
        W WV gradF GV x h_interior rfl rfl rfl
    rw [hR_eq]; rfl
  -- Step 2 + 3 + 4: rewrite via h_per_i, Stage 7, identify with Ric, ricci_symm.
  calc ∑ i, metricInner x
        (riemannCurvature HasMetric.metric (Bi i).toFun W.toFun gradF.toFun x) ((Bi i).toFun x)
      = ∑ i, Φ ((Bi i).toFun x) ((Bi i).toFun x) :=
        Finset.sum_congr rfl (fun i _ => h_per_i i)
    _ = ∑ i, Φ ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i) :=
        Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x Φ
    _ = Ric_g(W.toFun x, gradF.toFun x) x := by
        rw [ricciTensor_eq_sum_inner_orthonormal x (W.toFun x) (gradF.toFun x)]
        apply Finset.sum_congr rfl
        intro i _
        -- Φ v v = metricInner (curvatureEndo (HasMetric.metric) WV GV x v) v
        --       = ⟪curvatureEndo (HasMetric.metric) WV GV x v, v⟫_ℝ (def-eq)
        --       = ⟪v, curvatureEndo (HasMetric.metric) WV GV x v⟫_ℝ (real_inner_comm).
        show ⟪curvatureEndo (HasMetric.metric) WV GV x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i),
                (stdOrthonormalBasis ℝ (TangentSpace I x)) i⟫_ℝ
            = ⟪(stdOrthonormalBasis ℝ (TangentSpace I x)) i,
                curvatureEndo (HasMetric.metric) WV GV x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)⟫_ℝ
        exact real_inner_comm _ _
    _ = Ric_g(gradF.toFun x, W.toFun x) x := by
        show ricciTensor (HasMetric.metric) x (W.toFun x) (gradF.toFun x)
          = ricciTensor (HasMetric.metric) x (gradF.toFun x) (W.toFun x)
        show ricci (HasMetric.metric) WV GV x
            = ricci (HasMetric.metric) GV WV x
        exact ricci_symm WV GV x h_interior

/-- **Math.** Hessian-frame trace equals Laplacian locally: on a
neighbourhood of $x$,
$$\sum_i \mathrm{Hess}\,f(b)(B_i b, B_i b) \;=\; \Delta_g f(b).$$
Combines orthonormality of `smoothOrthoFrame` on `smoothOrthoFrameNbhd`
with `sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std` and the std-basis
trace identification with `scalarLaplacian`. -/
theorem sum_hessianBilin_smoothOrthoFrame_eventuallyEq_laplacian
    (f : M → ℝ) (x : M) :
    (fun b => ∑ i, hessianBilin (I := I) HasMetric.metric f b
                    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b)
                    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i b))
      =ᶠ[𝓝 x] (Δ_g[I] f : M → ℝ) := by
  filter_upwards [Riemannian.Tensor.smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x]
    with b hb
  -- At b ∈ nbhd, basis-invariance of trace of `hessianBilin f b`.
  rw [Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std
        (I := I) x hb (hessianBilin (I := I) HasMetric.metric f b)]
  -- Identify the std-basis trace with `Δ_g f b`.
  show ∑ i, hessianBilin (I := I) HasMetric.metric f b
            ((stdOrthonormalBasis ℝ (TangentSpace I b)) i)
            ((stdOrthonormalBasis ℝ (TangentSpace I b)) i)
       = scalarLaplacian (I := I) HasMetric.metric f b
  rw [scalarLaplacian_eq_laplacian_hessianBilin HasMetric.metric]
  rfl

/-! ### Orthonormal-frame skew-derivative and the connection-cancel sum -/

/-- **Math.** **Smooth orthonormal frame cov-skew** at $x$:
$$g_x(\nabla_v B_i, B_j x) + g_x(B_i x, \nabla_v B_j) = 0.$$
Differentiate $g(B_i, B_j) = \delta_{ij}$ on `smoothOrthoFrameNbhd x`
and apply metric compatibility. -/
theorem smoothOrthoFrame_cov_skew
    [T2Space M]
    (x : M) (i j : Fin (Module.finrank ℝ E)) (v : TangentSpace I x) :
    metricInner x
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x v)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) +
    metricInner x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
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
  have hmc := leviCivitaConnection_metric_compatible HasMetric.metric
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

/-- **Math.** **Hessian × cov-frame antisym-symm sum vanishes** (heart-of-
Bochner Step 4):
$$\sum_i \mathrm{Hess}\,f(x)(B_i x,\, \nabla_{W(x)} B_i) \;=\; 0,$$
where $B_i = $`smoothOrthoFrame g x i`. Expands $\nabla_{W(x)} B_i$ in
the orthonormal frame, factoring into $\sum_{i,j} a_{ij} h_{ij}$ with
$a_{ij}$ antisymmetric (`smoothOrthoFrame_cov_skew`) and $h_{ij}$
symmetric (`hessianBilin_symm`). -/
theorem sum_hessianBilin_smoothOrthoFrame_cov_eq_zero
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (W : SmoothVectorField I M) (x : M) :
    ∑ i, hessianBilin (I := I) HasMetric.metric f x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x
          (W.toFun x)) = 0 := by
  classical
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
    exact Set.mem_univ _
  have h_grad := manifoldGradient_smooth_of_smooth HasMetric.metric f hf
  set bAt : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    Riemannian.Tensor.smoothOrthoFrameOrthonormalBasis (I := I) x with hbAt_def
  -- Key matrices.
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => metricInner x
      ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x (W.toFun x))
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) with ha_def
  set h_mat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => hessianBilin (I := I) HasMetric.metric f x
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
      (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) with hh_def
  -- Step 1: Orthonormal Riesz expansion of ∇_{W(x)} B_i.
  -- `v = ∑ k, ⟪b_k, v⟫_ℝ • b_k` for orthonormal basis `b_k` and `v ∈ T_xM`.
  have h_riesz : ∀ i,
      (leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i) x (W.toFun x)
        = ∑ j, a i j •
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x j x) := by
    intro i
    set v : TangentSpace I x :=
      (leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
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
  have h_expand : ∀ i, hessianBilin (I := I) HasMetric.metric f x
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
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
  rw [show (∑ i, hessianBilin (I := I) HasMetric.metric f x _ _)
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
        ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun
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
    have h_grad_at : TangentSmoothAt (manifoldGradient (I := I) HasMetric.metric f) x :=
      (h_grad x).mdifferentiableAt (by simp)
    exact hessianBilin_symm (I := I) HasMetric.metric f x h_interior hf_2 h_grad_at _ _
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

/-- **Math.** Conditional inner-form reduction. Math: Given the
heart-of-Bochner identity against every test direction $w$, the scalar
form paired against $\nabla f x$ follows.
Eng: Riesz-style specialisation plus bilinearity packages the four-step
algebraic chain (Hess-sym swap, D.3, Ricci identification, smooth-trace
identification) into the form consumed by the Bochner–Weitzenböck assembly. -/
theorem sum_inner_secondCovDerivAt_grad_smoothOrthoFrame_of_inner_form
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      metricInner x
          (∑ i, secondCovDerivAt (I := I) (M := M) HasMetric.metric
            (manifoldGradient (I := I) HasMetric.metric f) x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
          w
        = metricInner x (manifoldGradient (I := I) HasMetric.metric (Δ_g[I] f) x) w
          + Ric_g(manifoldGradient (I := I) HasMetric.metric f x, w) x) :
    ∑ i, metricInner x
        (secondCovDerivAt (I := I) (M := M) HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        (manifoldGradient (I := I) HasMetric.metric f x)
      = metricInner x (manifoldGradient (I := I) HasMetric.metric f x)
            (manifoldGradient (I := I) HasMetric.metric (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) HasMetric.metric f x),
                (manifoldGradient (I := I) HasMetric.metric f x)) x := by
  classical
  -- Specialise hInner at w = ∇f x.
  have h := hInner (manifoldGradient (I := I) HasMetric.metric f x)
  -- Chain: ∑ ⟨A i, ∇f⟩ = ⟨∑ A i, ∇f⟩ (sum_inner, via metricInner = ⟪·,·⟫_ℝ
  -- def-eq) = ⟨∇Δf, ∇f⟩ + Ric (hInner) = ⟨∇f, ∇Δf⟩ + Ric (metricInner_comm).
  calc ∑ i, metricInner x
          (secondCovDerivAt (I := I) (M := M) HasMetric.metric
            (manifoldGradient (I := I) HasMetric.metric f) x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
          (manifoldGradient (I := I) HasMetric.metric f x)
      = metricInner x
          (∑ i, secondCovDerivAt (I := I) (M := M) HasMetric.metric
            (manifoldGradient (I := I) HasMetric.metric f) x
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
            (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
          (manifoldGradient (I := I) HasMetric.metric f x) :=
        (sum_inner Finset.univ _ (manifoldGradient (I := I) HasMetric.metric f x)).symm
    _ = metricInner x (manifoldGradient (I := I) HasMetric.metric (Δ_g[I] f) x)
            (manifoldGradient (I := I) HasMetric.metric f x)
          + Ric_g(manifoldGradient (I := I) HasMetric.metric f x,
                  manifoldGradient (I := I) HasMetric.metric f x) x := h
    _ = metricInner x (manifoldGradient (I := I) HasMetric.metric f x)
            (manifoldGradient (I := I) HasMetric.metric (Δ_g[I] f) x)
          + Ric_g(manifoldGradient (I := I) HasMetric.metric f x,
                  manifoldGradient (I := I) HasMetric.metric f x) x := by
        rw [metricInner_comm x (manifoldGradient (I := I) HasMetric.metric (Δ_g[I] f) x)]

end Operators
end Riemannian

end
