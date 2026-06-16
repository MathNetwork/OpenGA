import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.Operators.HessianLie
import OpenGALib.Riemannian.Util.Metric.MetricInnerSmoothness
-- `Riem(X, Y) Z` notation is now defined inline in `Connection.lean`
-- alongside `riemannCurvature`; it transitively reaches us via the
-- `import OpenGALib.Riemannian.Connection.LeviCivita` above.
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import OpenGALib.Riemannian.Util.CovDeriv.CovDerivBridges

/-!
# Riemann curvature, Ricci, and scalar curvature

For $(M, g)$ with Levi-Civita connection $\nabla$:

* **Riemann curvature**:
  $R(X, Y) Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z.$
* **Ricci curvature**: trace of $z \mapsto R(z, X) Y$ on $T_xM$,
  $\mathrm{Ric}(X, Y)(x) := \mathrm{tr}\bigl(z \mapsto R(z, X) Y(x)\bigr).$
* **Scalar curvature**: metric trace of the Ricci tensor,
  $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x).$

`riemannCurvature` itself lives in `Riemannian.Connection` as connection
data, not metric data. This file collects the antisymmetry corollary
and the metric-dependent Ricci / scalar-curvature constructions.

Reference: do Carmo 1992 §4.
-/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Eng.** Constant smooth vector field at a tangent vector. Hides
`SmoothVectorField.const (I := I) (M := M) V` boilerplate inside this file. -/
local notation "cF[" V "]" => SmoothVectorField.const (I := I) (M := M) V

/-! ## Math API -/

/-- **Math.** $R(X, Y) Z = -R(Y, X) Z$.

Reference: do Carmo §4 Proposition 2.5 (i). -/
theorem riemannCurvature_antisymm
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) :
    riemannCurvature g X Y Z x = -riemannCurvature g Y X Z x := by
  simp only [riem_simp]
  rw [covDeriv_mlieBracket_swap_apply]
  abel

/-- **Math.** The endomorphism $z \mapsto R(z, X) Y(x)$ on $T_xM$ (with $z$ extended to
the constant section). Trace of this is the Ricci tensor at $x$. -/
noncomputable def curvatureEndo
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun z :=
    riemannCurvature g (fun _ => z) X Y x
  map_add' z₁ z₂ := by
    show riemannCurvature g (fun _ => z₁ + z₂) X.toFun Y.toFun x
       = riemannCurvature g (fun _ => z₁) X.toFun Y.toFun x
        + riemannCurvature g (fun _ => z₂) X.toFun Y.toFun x
    -- Unfold riemannCurvature g into 3 covDeriv g terms.
    show covDeriv g (fun _ => z₁ + z₂) (fun y => covDeriv g X.toFun Y.toFun y) x
          - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₁ + z₂) Y.toFun y) x
          - covDeriv g (fun y => mlieBracket I (fun _ => z₁ + z₂) X.toFun y) Y.toFun x
        = (covDeriv g (fun _ => z₁) (fun y => covDeriv g X.toFun Y.toFun y) x
            - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₁) Y.toFun y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z₁) X.toFun y) Y.toFun x)
        + (covDeriv g (fun _ => z₂) (fun y => covDeriv g X.toFun Y.toFun y) x
            - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₂) Y.toFun y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z₂) X.toFun y) Y.toFun x)
    -- Π-equality for adding constant sections.
    have h_const_add : ((fun _ : M => z₁ + z₂) : (y : M) → TangentSpace I y)
        = (fun _ => z₁) + (fun _ => z₂) := by funext y; rfl
    -- Term 1: covDeriv g (fun _ => z) F x = lev.toFun F x z is continuous linear map-linear in z.
    have hT1 : covDeriv g (fun _ : M => z₁ + z₂) (fun y => covDeriv g X.toFun Y.toFun y) x
        = covDeriv g (fun _ => z₁) (fun y => covDeriv g X.toFun Y.toFun y) x
        + covDeriv g (fun _ => z₂) (fun y => covDeriv g X.toFun Y.toFun y) x := by
      show ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) (z₁ + z₂)
          = ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) z₁
          + ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) z₂
      exact map_add _ _ _
    -- Term 2: inner field `fun y => covDeriv g (fun _ => z) Y y = lev.toFun Y y z`.
    -- continuous linear map-linear in z, so the inner field is the pointwise sum.
    have h_inner_add : (fun y => covDeriv g (fun _ : M => z₁ + z₂) Y.toFun y)
        = (fun y => covDeriv g (fun _ => z₁) Y.toFun y)
          + (fun y => covDeriv g (fun _ => z₂) Y.toFun y) := by
      funext y
      show ((leviCivitaConnection g).toFun Y.toFun y) (z₁ + z₂)
          = ((leviCivitaConnection g).toFun Y.toFun y) z₁
          + ((leviCivitaConnection g).toFun Y.toFun y) z₂
      exact map_add _ _ _
    -- Smoothness of each summand: `(fun y => covDeriv g (fun _ => z) Y y) =
    -- (fun y => lev.toFun Y y z)` is smooth via `leviCivitaConnection`'s
    -- isCovariantDerivativeOnUniv applied at the constant section.
    have h_const_z₁_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => z₁) y :=
      fun y => (cF[z₁]).smoothAt y
    have h_const_z₂_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => z₂) y :=
      fun y => (cF[z₂]).smoothAt y
    have hY_smooth := Y.smoothAt
    have hT2 : covDeriv g X.toFun (fun y => covDeriv g (fun _ : M => z₁ + z₂) Y.toFun y) x
        = covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₁) Y.toFun y) x
        + covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₂) Y.toFun y) x := by
      rw [h_inner_add]
      apply covDeriv_add_field
      · exact covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z₁ Y x
      · exact covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z₂ Y x
    -- Term 3: mlieBracket linearity in left argument.
    have h_lieBr_add : (fun y => mlieBracket I (fun _ : M => z₁ + z₂) X.toFun y)
        = (fun y => mlieBracket I (fun _ => z₁) X.toFun y)
          + (fun y => mlieBracket I (fun _ => z₂) X.toFun y) := by
      funext y
      rw [show ((fun _ : M => z₁ + z₂) : (y : M) → TangentSpace I y)
          = (fun _ => z₁) + (fun _ => z₂) from h_const_add]
      exact VectorField.mlieBracket_add_left (h_const_z₁_smooth y) (h_const_z₂_smooth y)
    -- Smoothness of (fun y => mlieBracket I (fun _ => z) X.toFun y) at x.
    -- This requires C^2 manifold for derivatives of mlieBracket; we assert
    -- via a separate framework lemma that we might not have. For now use
    -- a placeholder via Mathlib + framework's fallback.
    have hT3 : covDeriv g (fun y => mlieBracket I (fun _ : M => z₁ + z₂) X.toFun y) Y.toFun x
        = covDeriv g (fun y => mlieBracket I (fun _ => z₁) X.toFun y) Y.toFun x
        + covDeriv g (fun y => mlieBracket I (fun _ => z₂) X.toFun y) Y.toFun x := by
      rw [h_lieBr_add]
      -- For the OUTER covDeriv g, the field A vs A+B issue: covDeriv g is
      -- linear in the FIRST (direction) argument via continuous linear map, since
      -- covDeriv g F G x = lev.toFun G x (F x), and `(F + G) x = F x + G x`.
      show ((leviCivitaConnection g).toFun Y.toFun x)
          ((fun y => mlieBracket I (fun _ => z₁) X.toFun y) x
            + (fun y => mlieBracket I (fun _ => z₂) X.toFun y) x)
        = ((leviCivitaConnection g).toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ => z₁) X.toFun y) x)
          + ((leviCivitaConnection g).toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ => z₂) X.toFun y) x)
      exact map_add _ _ _
    rw [hT1, hT2, hT3]
    abel
  map_smul' c z := by
    show riemannCurvature g (fun _ => c • z) X.toFun Y.toFun x
       = c • riemannCurvature g (fun _ => z) X.toFun Y.toFun x
    show covDeriv g (fun _ => c • z) (fun y => covDeriv g X.toFun Y.toFun y) x
          - covDeriv g X.toFun (fun y => covDeriv g (fun _ => c • z) Y.toFun y) x
          - covDeriv g (fun y => mlieBracket I (fun _ => c • z) X.toFun y) Y.toFun x
        = c • (covDeriv g (fun _ => z) (fun y => covDeriv g X.toFun Y.toFun y) x
            - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z) Y.toFun y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z) X.toFun y) Y.toFun x)
    have h_const_smul : ((fun _ : M => c • z) : (y : M) → TangentSpace I y)
        = c • (fun _ => z) := by funext y; rfl
    have h_const_z_smooth : ∀ y, TangentSmoothAt (fun _ : M => z) y :=
      fun y => (cF[z]).smoothAt y
    have hY_smooth := Y.smoothAt
    -- Term 1: continuous linear map map_smul.
    have hT1 : covDeriv g (fun _ : M => c • z) (fun y => covDeriv g X.toFun Y.toFun y) x
        = c • covDeriv g (fun _ => z) (fun y => covDeriv g X.toFun Y.toFun y) x := by
      show ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) (c • z)
          = c • ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) z
      exact ContinuousLinearMap.map_smul _ _ _
    -- Term 2.
    have h_inner_smul : (fun y => covDeriv g (fun _ : M => c • z) Y.toFun y)
        = c • (fun y => covDeriv g (fun _ => z) Y.toFun y) := by
      funext y
      show ((leviCivitaConnection g).toFun Y.toFun y) (c • z)
          = c • ((leviCivitaConnection g).toFun Y.toFun y) z
      exact ContinuousLinearMap.map_smul _ _ _
    have hT2 : covDeriv g X.toFun (fun y => covDeriv g (fun _ : M => c • z) Y.toFun y) x
        = c • covDeriv g X.toFun (fun y => covDeriv g (fun _ => z) Y.toFun y) x := by
      rw [h_inner_smul]
      apply covDeriv_smul_const_field
      exact covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z Y x
    -- Term 3.
    have h_lieBr_smul : (fun y => mlieBracket I (fun _ : M => c • z) X.toFun y)
        = c • (fun y => mlieBracket I (fun _ => z) X.toFun y) := by
      funext y
      rw [show ((fun _ : M => c • z) : (y : M) → TangentSpace I y)
          = c • (fun _ => z) from h_const_smul]
      exact VectorField.mlieBracket_const_smul_left (h_const_z_smooth y)
    have hT3 : covDeriv g (fun y => mlieBracket I (fun _ : M => c • z) X.toFun y) Y.toFun x
        = c • covDeriv g (fun y => mlieBracket I (fun _ => z) X.toFun y) Y.toFun x := by
      rw [h_lieBr_smul]
      show ((leviCivitaConnection g).toFun Y.toFun x)
          ((c • fun y => mlieBracket I (fun _ : M => z) X.toFun y) x)
        = c • ((leviCivitaConnection g).toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ : M => z) X.toFun y) x)
      show ((leviCivitaConnection g).toFun Y.toFun x)
          (c • mlieBracket I (fun _ => z) X.toFun x)
        = c • ((leviCivitaConnection g).toFun Y.toFun x)
            (mlieBracket I (fun _ => z) X.toFun x)
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT1, hT2, hT3]
    -- Goal: c • A - c • B - c • C = c • (A - B - C)
    rw [smul_sub, smul_sub]

/-- **Math.** The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at $x$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{curvatureEndo}\,X\,Y\,x).$$

Reference: do Carmo §4 ex. 1. -/
noncomputable def ricci
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (curvatureEndo g X Y x)

/-! ### Diagonal `(3,4)` vanishing: $g(R(X,Y)Z, Z) = 0$

do Carmo §4 Proposition 2.5(iii) closure. The proof reduces, via metric
compatibility applied diagonally at every $y$, to the half-derivative
identity $D_V (g(Z, Z))(y) = 2\,g(\nabla_V Z, Z)(y)$. Differentiating
again at $x$ and using metric-compat once more expresses each
$g(\nabla_W \nabla_V Z, Z)$ in terms of iterated directional derivatives
of $f := g(Z, Z)$; the Hessian–Lie identity
(`mfderiv_iterate_sub_eq_mlieBracket_apply`) collapses
$X(Y(f)) - Y(X(f)) - [X,Y](f) = 0$, closing the chain. -/

/-- **Math.** **Diagonal metric-compat identity**: at every point $y \in M$ with
the direction $V$ smooth, metric compatibility gives
$$D_V (g(Z, Z))(y) = 2\,\langle \nabla_V Z, Z\rangle_g(y).$$
Stated using `mDirDeriv` (the `ℝ`-typed `mfderiv` wrapper) on the LHS
and `(leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun` (definitionally equal to `covDeriv HasMetric.metric`)
on the RHS. -/
private lemma mDirDeriv_self_eq_two_metricInner_leviCivita_self
    (g : RiemannianMetric I M)
    (V : VectorFieldSection I M) (Z : SmoothVectorField I M) (y : M)
    (hV : TangentSmoothAt V y) :
    mDirDeriv (fun y' => g.metricInner y' (Z y') (Z y')) y (V y)
      = 2 * g.metricInner y
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y) := by
  -- Bridge metric-compat ∇ → `.toFun` form so `rw [hsym]` matches the structural shape.
  have h := leviCivitaConnection_metric_compatible g V Z.toFun Z.toFun y
    hV (Z.smoothAt y) (Z.smoothAt y)
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h
  -- Cast h to typeclass `metricInner` form for rw matching.
  change mDirDeriv (fun y' => g.metricInner y' (Z y') (Z y')) y (V y)
      = g.metricInner y
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y))
          (Z y)
        + g.metricInner y (Z y)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y))
    at h
  have hsym :
      g.metricInner y (Z y)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y))
        = g.metricInner y
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y) :=
    g.metricInner_comm y _ _
  rw [hsym] at h
  have h_ℝ : mDirDeriv (fun y' => g.metricInner y' (Z y') (Z y')) y (V y)
      = g.metricInner y
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y)
        + g.metricInner y
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y) :=
    h
  rw [h_ℝ]; ring

/-- **Eng.** Function-equality form: at every $y$, the directional derivative of
$y \mapsto g(Z, Z)(y)$ along the smooth vector field $V$ equals
$2\,g(\nabla_V Z, Z)(y)$. -/
private lemma fun_mDirDeriv_self_eq_two_metricInner_leviCivita_self
    (g : RiemannianMetric I M)
    (V Z : SmoothVectorField I M) :
    (fun y' : M => mDirDeriv (fun y'' => g.metricInner y'' (Z y'') (Z y'')) y' (V.toFun y'))
      = (fun y' : M => 2 * g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := by
  funext y'
  exact mDirDeriv_self_eq_two_metricInner_leviCivita_self g V.toFun Z y' (V.smoothAt y')

/-- **Math.** **Iterated metric-compat identity at $x$**: differentiating the
diagonal identity once more at $x$ in direction $W(x)$ and applying
metric-compat at $x$ yields
$$\tfrac12\,W\!\left(V (g(Z, Z))\right)(x)
  = \langle \nabla_W \nabla_V Z, Z\rangle_g(x)
    + \langle \nabla_V Z, \nabla_W Z\rangle_g(x).$$ -/
private lemma half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (V W Z : SmoothVectorField I M) (x : M) :
    (1/2 : ℝ) * mDirDeriv
        (fun y' : M => mDirDeriv
          (fun y'' => g.metricInner y'' (Z y'') (Z y'')) y' (V.toFun y')) x (W.toFun x)
      = g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun
            (fun y' => covDeriv g V.toFun Z.toFun y') x (W.toFun x))
          (Z x)
        + g.metricInner x (covDeriv g V.toFun Z.toFun x)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (W.toFun x)) := by
  -- Use function-equality form of the diagonal identity to rewrite the LHS
  -- inner function; then apply mfderiv_const_smul and metric-compat at x.
  have h_fun := fun_mDirDeriv_self_eq_two_metricInner_leviCivita_self g V Z
  -- Sections smooth at x.
  have hcovVZ : TangentSmoothAt (fun y' => covDeriv g V.toFun Z.toFun y') x :=
    covDeriv_smoothVF_smoothAt g V Z x
  -- The mfderiv of LHS (the iterated mDirDeriv expression) at x in dir W(x):
  -- by h_fun, equals mfderiv of `fun y' => 2 * g(∇_V Z, Z)(y')` at x in dir W(x).
  -- That = 2 * mfderiv (g(∇_V Z, Z)) x (W x), and by metric-compat at x:
  --      = 2 * [g(∇_W ∇_V Z, Z) + g(∇_V Z, ∇_W Z)] x.
  -- So (1/2) * LHS = g(∇_W ∇_V Z, Z) x + g(∇_V Z, ∇_W Z) x.
  -- Bridge metric-compat ∇ → `.toFun` form for downstream `g.metricInner_comm` / `linarith`.
  have h_compat := leviCivitaConnection_metric_compatible g
    W.toFun (fun y' => covDeriv g V.toFun Z.toFun y') Z.toFun x
    (W.smoothAt x) hcovVZ (Z.smoothAt x)
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h_compat
  -- h_compat : mfderiv (fun y' => g(∇_V Z, Z) y') x (W x) =
  --              g(∇_W (∇_V Z), Z) + g(∇_V Z, ∇_W Z)
  -- Rewrite the LHS function via h_fun:
  conv_lhs => rw [show (fun y' : M => mDirDeriv
        (fun y'' => g.metricInner y'' (Z y'') (Z y'')) y' (V.toFun y'))
      = (fun y' : M => 2 * g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) from h_fun]
  -- Now LHS = (1/2) * mfderiv (fun y' => 2 * g(∇_V Z, Z) y') x (W x)
  -- Pull the 2 out: mfderiv (2 * h) x v = 2 * mfderiv h x v (linear).
  -- The function under mfderiv:  fun y' => 2 * g(LC.toFun Z y' (V y'), Z y')
  -- equals  2 • (fun y' => g(LC.toFun Z y' (V y'), Z y'))  via funext.
  -- Use mfderiv_const_smul; we need MDifferentiableAt of the inner section.
  -- The "covDeriv g V Z = LC.toFun Z y (V y)" is def-eq; the inner section's
  -- smoothness at x is hcovVZ (via g.metricInner_mdifferentiableAt).
  have h_inner_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y' : M => g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y')) x := by
    -- The function is `y' ↦ g(covDeriv g V Z y', Z y')` (def-eq covDeriv g ↔ LC.toFun).
    -- Use `g.metricInner_mdifferentiableAt` with `hcovVZ` and `Z.smoothAt x`.
    have h := g.metricInner_mdifferentiableAt
      (v := fun y' => covDeriv g V.toFun Z.toFun y') (w := Z.toFun) hcovVZ (Z.smoothAt x)
    exact h
  -- Avoid continuous linear map-smul issues by writing `2 * h = h + h` and using `mfderiv_add`.
  have h_two_add : (fun y' : M => (2 : ℝ) * g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y'))
      = (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')
        + g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := by
    funext y'; ring
  rw [h_two_add]
  -- Now: (1/2) * mDirDeriv (fun y' => h y' + h y') x (W x) where h := g(∇_V Z, Z) y'.
  -- Convert `fun y' => h y' + h y'` to the Pi-add form `h + h` (definitional).
  have h_pi_add : (fun y' : M => g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y')
      + g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y'))
      = (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := rfl
  rw [h_pi_add]
  -- `mfderiv (f + g) x v = mfderiv f x v + mfderiv g x v`.
  -- Compute the continuous linear map add via `mfderiv_add` then evaluate at `W.toFun x`.
  have h_clm_add :
      mfderiv I 𝓘(ℝ, ℝ) ((fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y'))) x
        = mfderiv I 𝓘(ℝ, ℝ) (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y')) x
          + mfderiv I 𝓘(ℝ, ℝ) (fun y' : M => g.metricInner y'
              ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
              (Z y')) x :=
    mfderiv_add h_inner_mdiff h_inner_mdiff
  -- Apply both sides to (W.toFun x) and use continuous linear map-add evaluation.
  have h_val_add : mDirDeriv ((fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y'))) x (W.toFun x)
      = mDirDeriv (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) x (W.toFun x)
        + mDirDeriv (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y')) x (W.toFun x) := by
    show mfderiv I 𝓘(ℝ, ℝ) _ x (W.toFun x) = _
    rw [h_clm_add]
    rfl
  rw [h_val_add]
  -- Now: (1/2) * (mDirDeriv h x v + mDirDeriv h x v) = h_compat
  have h_compat_ℝ :
      mDirDeriv (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) x (W.toFun x)
        = g.metricInner x
            ((leviCivitaConnection (I := I) (M := M) g).toFun
              (fun y' => covDeriv g V.toFun Z.toFun y') x (W.toFun x))
            (Z x)
          + g.metricInner x (covDeriv g V.toFun Z.toFun x)
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (W.toFun x)) :=
    h_compat
  rw [h_compat_ℝ]; ring

/-- **Math.** $\langle R(X, Y) Z, Z \rangle_g(x) = 0$ for smooth vector fields
$X, Y, Z$, with $x$ in the closure of the interior of $\mathrm{range}\,I$
(required by the Hessian–Lie identity for boundary-aware models).

Reference: do Carmo §4 Proposition 2.5(iii). -/
theorem riemannCurvature_inner_self_zero
    (g : RiemannianMetric I M)
    [IsManifold I 2 M]
    (X Y Z : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I))) :
    g.metricInner x (riemannCurvature g X.toFun Y.toFun Z.toFun x) (Z x) = 0 := by
  classical
  -- Setup: f := g(Z, Z), the self-norm-squared scalar function.
  set f : M → ℝ := fun y' => g.metricInner y' (Z y') (Z y') with hf_def
  -- f is C∞ globally, hence C² at x.
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := fun y =>
    g.metricInner_contMDiffAt (n := ∞) (Z.smooth y) (Z.smooth y)
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf_smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  -- [X, Y] is smooth at x (Mathlib + framework's mlieBracket_tangentSmoothAt).
  have hXY_br : TangentSmoothAt (mlieBracket I X.toFun Y.toFun) x :=
    mlieBracket_tangentSmoothAt X.smooth Y.smooth
  -- Equations (A) and (B): iterated metric-compat at x.
  have hA := half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv g X Y Z x  -- (V=X, W=Y)
  have hB := half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv g Y X Z x  -- (V=Y, W=X)
  -- Equation (C): metric-compat at x for V = [X, Y].
  have hC := mDirDeriv_self_eq_two_metricInner_leviCivita_self g
    (mlieBracket I X.toFun Y.toFun) Z x hXY_br
  -- Hessian–Lie identity at x: X(Y(f))(x) - Y(X(f))(x) = mfderiv f x ([X,Y](x))
  have hX1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) x :=
    (X.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hY1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) x :=
    (Y.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hHL : mDirDeriv (fun y' => mDirDeriv f y' (Y.toFun y')) x (X.toFun x)
      - mDirDeriv (fun y' => mDirDeriv f y' (X.toFun y')) x (Y.toFun x)
      = mDirDeriv f x (mlieBracket I X.toFun Y.toFun x) :=
    mfderiv_iterate_sub_eq_mlieBracket_apply f X.toFun Y.toFun x h_interior hf_2 hX1 hY1
  -- Inner product cross-cancel: g(∇_X Z, ∇_Y Z) = g(∇_Y Z, ∇_X Z).
  have h_inner_comm : g.metricInner x (covDeriv g X.toFun Z.toFun x)
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (Y.toFun x))
      = g.metricInner x (covDeriv g Y.toFun Z.toFun x)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (X.toFun x)) := by
    show g.metricInner x ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (X.toFun x))
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (Y.toFun x))
      = g.metricInner x ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (Y.toFun x))
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (X.toFun x))
    exact g.metricInner_comm x _ _
  -- Expand R via riemannCurvature_commutator_form g + g.metricInner_sub_left twice.
  show g.metricInner x (riemannCurvature g X.toFun Y.toFun Z.toFun x) (Z x) = 0
  rw [riemannCurvature_commutator_form]
  -- Goal: g(∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z, Z) x = 0
  rw [show g.metricInner x (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
        - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x) (Z x)
      = g.metricInner x (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x) (Z x)
        - g.metricInner x (covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x) (Z x)
        - g.metricInner x (covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x) (Z x)
      from by
    rw [show ((covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
          - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
          - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x : TangentSpace I x))
        = (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
          - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x)
          - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x from rfl,
      g.metricInner_sub_left, g.metricInner_sub_left]]
  -- Now: g(∇_X ∇_Y Z, Z) - g(∇_Y ∇_X Z, Z) - g(∇_{[X,Y]} Z, Z) = 0
  -- From hB (V=Y, W=X): (1/2) X(Y(f))(x) = g(∇_X ∇_Y Z, Z) + g(∇_Y Z, ∇_X Z)
  --                    ⇒ g(∇_X ∇_Y Z, Z) = (1/2) X(Y(f))(x) - g(∇_Y Z, ∇_X Z)
  -- From hA (V=X, W=Y): g(∇_Y ∇_X Z, Z) = (1/2) Y(X(f))(x) - g(∇_X Z, ∇_Y Z)
  -- From hC: 2 g(∇_{[X,Y]} Z, Z) = D_{[X,Y]} f(x)
  --        ⇒ g(∇_{[X,Y]} Z, Z) = (1/2) D_{[X,Y]} f(x) = (1/2) mDirDeriv f x ([X,Y] x)
  -- Combine: difference = (1/2) [X(Y(f)) - Y(X(f)) - [X,Y](f)] - inner cross-cancel = 0.
  -- Show all four covDeriv g terms are def-equal to LC.toFun forms:
  show g.metricInner x
        ((leviCivitaConnection (I := I) (M := M) g).toFun
          (fun y => covDeriv g Y.toFun Z.toFun y) x (X.toFun x)) (Z x)
      - g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun
            (fun y => covDeriv g X.toFun Z.toFun y) x (Y.toFun x)) (Z x)
      - g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x
            (VectorField.mlieBracket I X.toFun Y.toFun x)) (Z x)
      = 0
  -- Substitute via hA, hB, hC, hHL.
  -- hB: (1/2) X(Y(f))(x) = g(LC.toFun (∇_Y Z) x (X x), Z) + g(∇_Y Z, LC.toFun Z x (X x))
  -- ⇒ g(LC.toFun (∇_Y Z) x (X x), Z) = (1/2) X(Y(f))(x) - g(∇_Y Z, LC.toFun Z x (X x))
  -- hA: g(LC.toFun (∇_X Z) x (Y x), Z) = (1/2) Y(X(f))(x) - g(∇_X Z, LC.toFun Z x (Y x))
  -- hC: 2 g(LC.toFun Z x ([X,Y] x), Z) = mDirDeriv f x ([X,Y] x)
  -- Substitute and use hHL: X(Y(f)) - Y(X(f)) = mDirDeriv f x ([X,Y] x); h_inner_comm cancel.
  linarith [hA, hB, hC, hHL, h_inner_comm]

/-! ### Metric-skew of Riemann curvature in the (3rd, 4th) slot

Polarisation of `riemannCurvature_inner_self_zero` on $Z + W$ yields the
classical metric-skew identity
$\langle R(X, Y) Z, W\rangle_g + \langle R(X, Y) W, Z\rangle_g = 0$. -/

/-- **Math.** **Additivity of `riemannCurvature HasMetric.metric` in the differentiated (3rd) slot**:
$R(X, Y)(Z_1 + Z_2)(x) = R(X, Y) Z_1(x) + R(X, Y) Z_2(x)$ for $X, Y, Z_i$
smooth vector fields. Direct from `covDeriv_add_field` applied at $x$
(outer) and at every $y$ (inner section sum) plus `funext`.

Public-exposure of formerly `private` helper, needed by the Z-slot
additivity step of the full 3-slot tensoriality chain
(`Riemannian/Curvature/Tensoriality.lean`). -/
theorem riemannCurvature_add_third
    (g : RiemannianMetric I M)
    (X Y Z₁ Z₂ : SmoothVectorField I M) (x : M) :
    riemannCurvature g X.toFun Y.toFun (Z₁ + Z₂).toFun x
      = riemannCurvature g X.toFun Y.toFun Z₁.toFun x
        + riemannCurvature g X.toFun Y.toFun Z₂.toFun x := by
  classical
  have h_pi_add : (Z₁ + Z₂).toFun = Z₁.toFun + Z₂.toFun := by
    funext y; show (Z₁ + Z₂) y = Z₁ y + Z₂ y; rfl
  have h_inner_Y : (fun y => covDeriv g Y.toFun (Z₁ + Z₂).toFun y)
      = (fun y => covDeriv g Y.toFun Z₁.toFun y)
        + (fun y => covDeriv g Y.toFun Z₂.toFun y) := by
    funext y
    rw [h_pi_add]
    exact covDeriv_add_field g Y.toFun Z₁.toFun Z₂.toFun y
      (Z₁.smoothAt y) (Z₂.smoothAt y)
  have h_inner_X : (fun y => covDeriv g X.toFun (Z₁ + Z₂).toFun y)
      = (fun y => covDeriv g X.toFun Z₁.toFun y)
        + (fun y => covDeriv g X.toFun Z₂.toFun y) := by
    funext y
    rw [h_pi_add]
    exact covDeriv_add_field g X.toFun Z₁.toFun Z₂.toFun y
      (Z₁.smoothAt y) (Z₂.smoothAt y)
  show covDeriv g X.toFun (fun y => covDeriv g Y.toFun (Z₁ + Z₂).toFun y) x
      - covDeriv g Y.toFun (fun y => covDeriv g X.toFun (Z₁ + Z₂).toFun y) x
      - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) (Z₁ + Z₂).toFun x
    = (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z₁.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z₁.toFun y) x
        - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z₁.toFun x)
      + (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z₂.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z₂.toFun y) x
        - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z₂.toFun x)
  rw [h_inner_Y, h_inner_X, h_pi_add]
  rw [covDeriv_add_field g X.toFun (fun y => covDeriv g Y.toFun Z₁.toFun y)
        (fun y => covDeriv g Y.toFun Z₂.toFun y) x
        (covDeriv_smoothVF_smoothAt g Y Z₁ x)
        (covDeriv_smoothVF_smoothAt g Y Z₂ x),
      covDeriv_add_field g Y.toFun (fun y => covDeriv g X.toFun Z₁.toFun y)
        (fun y => covDeriv g X.toFun Z₂.toFun y) x
        (covDeriv_smoothVF_smoothAt g X Z₁ x)
        (covDeriv_smoothVF_smoothAt g X Z₂ x),
      covDeriv_add_field g (VectorField.mlieBracket I X.toFun Y.toFun)
        Z₁.toFun Z₂.toFun x (Z₁.smoothAt x) (Z₂.smoothAt x)]
  abel

/-- **Math.** **Metric-skew of the Riemann curvature in the (3rd, 4th) slot**:
$$\langle R(X, Y) Z, W\rangle_g(x) + \langle R(X, Y) W, Z\rangle_g(x) = 0.$$

Derived by polarising `riemannCurvature_inner_self_zero` on $Z + W$:
$$0 = \langle R(X, Y)(Z + W), Z + W\rangle_g
    = \underbrace{\langle R Z, Z\rangle}_{=0} + \langle R Z, W\rangle
      + \langle R W, Z\rangle + \underbrace{\langle R W, W\rangle}_{=0}.$$

Reference: do Carmo §4 Proposition 2.5(iv). -/
theorem riemannCurvature_metric_skew
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I))) :
    g.metricInner x (riemannCurvature g X.toFun Y.toFun Z.toFun x) (W x)
      + g.metricInner x (riemannCurvature g X.toFun Y.toFun W.toFun x) (Z x) = 0 := by
  have h_ZW := riemannCurvature_inner_self_zero g X Y (Z + W) x h_interior
  have h_Z := riemannCurvature_inner_self_zero g X Y Z x h_interior
  have h_W := riemannCurvature_inner_self_zero g X Y W x h_interior
  have h_add := riemannCurvature_add_third g X Y Z W x
  have h_ZW_x : (Z + W) x = Z x + W x := rfl
  rw [h_add, h_ZW_x, g.metricInner_add_left, g.metricInner_add_right,
      g.metricInner_add_right] at h_ZW
  linarith

/-! ### Pair symmetry: $g(R(X,Y)Z, W) = g(R(Z,W)X, Y)$

Standard algebraic corollary of the four-fold Bianchi I sum combined with
$(1,2)$-antisymmetry and $(3,4)$-antisymmetry. After cyclic Bianchi on the
triples $(X,Y,Z),\,(Y,Z,W),\,(Z,W,X),\,(W,X,Y)$ paired against the
respective fourth vector, the antisymmetries cancel 8 of the 12 terms,
leaving the headline identity. -/

/-- **Math.** **Pair symmetry of the Riemann tensor**:
$$g_x(R(X,Y)Z, W) \;=\; g_x(R(Z,W)X, Y).$$

Reference: do Carmo §4 Proposition 2.5 (iv); Petersen Ch. 3. -/
theorem riemannCurvature_pair_symm
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (x : M) :
    g.metricInner x (riemannCurvature g X Y Z x) (W x)
      = g.metricInner x (riemannCurvature g Z W X x) (Y x) := by
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
    exact Set.mem_univ _
  have bianchi_inner : ∀ (A B C D : SmoothVectorField I M),
      g.metricInner x (riemannCurvature g A B C x) (D x)
        + g.metricInner x (riemannCurvature g B C A x) (D x)
        + g.metricInner x (riemannCurvature g C A B x) (D x) = 0 := by
    intro A B C D
    have h := bianchi_first g A B C x
    have : g.metricInner x
              (riemannCurvature g A B C x + riemannCurvature g B C A x + riemannCurvature g C A B x) (D x)
            = g.metricInner x (0 : TangentSpace I x) (D x) := by rw [h]
    rw [g.metricInner_add_left, g.metricInner_add_left] at this
    rw [g.metricInner_zero_left] at this
    linarith
  have b1 := bianchi_inner X Y Z W
  have b2 := bianchi_inner Y Z W X
  have b3 := bianchi_inner Z W X Y
  have b4 := bianchi_inner W X Y Z
  have antisym12 : ∀ (A B C D : SmoothVectorField I M),
      g.metricInner x (riemannCurvature g A B C x) (D x)
        = -g.metricInner x (riemannCurvature g B A C x) (D x) := by
    intro A B C D
    rw [riemannCurvature_antisymm g A B C x, g.metricInner_neg_left]
  have antisym34 : ∀ (A B C D : SmoothVectorField I M),
      g.metricInner x (riemannCurvature g A B C x) (D x)
        = -g.metricInner x (riemannCurvature g A B D x) (C x) := by
    intro A B C D
    have h := riemannCurvature_metric_skew g A B C D x h_interior
    linarith
  -- Combine: sum of b1..b4 with the antisymmetries gives 2·σ(X,Y,Z,W) - 2·σ(Z,W,X,Y) = 0.
  -- Specialise antisym to the 12 σ-instances appearing in b1..b4 and feed to linarith.
  have a1 := antisym12 X Y Z W
  have a2 := antisym12 Y Z X W
  have a3 := antisym12 Z X Y W
  have a4 := antisym12 Y Z W X
  have a5 := antisym12 Z W Y X
  have a6 := antisym12 W Y Z X
  have a7 := antisym12 Z W X Y
  have a8 := antisym12 W X Z Y
  have a9 := antisym12 X Z W Y
  have a10 := antisym12 W X Y Z
  have a11 := antisym12 X Y W Z
  have a12 := antisym12 Y W X Z
  have c1 := antisym34 X Y Z W
  have c2 := antisym34 Y Z X W
  have c3 := antisym34 Z X Y W
  have c4 := antisym34 Y Z W X
  have c5 := antisym34 Z W Y X
  have c6 := antisym34 W Y Z X
  have c7 := antisym34 Z W X Y
  have c8 := antisym34 W X Z Y
  have c9 := antisym34 X Z W Y
  have c10 := antisym34 W X Y Z
  have c11 := antisym34 X Y W Z
  have c12 := antisym34 Y W X Z
  linarith

/-! ### Constant-direction commutator simplification

`R(const v, const w) Z x = ∇_v ∇_w Z - ∇_w ∇_v Z` at $x$ — the
$\nabla_{[X, Y]} Z$ term drops because $[\mathrm{const}\,v, \mathrm{const}\,w] = 0$
as a global section (`mlieBracket_const_const_apply_zero`), so the connection
evaluates `(leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun Z x` at the zero vector. -/

/-! ### Constant-direction Bianchi swap

Specialisation of `bianchi_first` to the triple $(\mathrm{const}\,v, X, Y)$,
combined with `riemannCurvature_antisymm` on the third Bianchi summand:
$$R(\mathrm{const}\,v, X)\,Y - R(\mathrm{const}\,v, Y)\,X
   = -R(X, Y)(\mathrm{const}\,v).$$
This is the per-basis-vector algebraic identity that drives `ricci_symm`. -/

/-- **Math.** **Constant-direction Bianchi swap**. Bianchi I on $(\mathrm{const}\,v, X, Y)$
together with first-pair antisymmetry of $R$ rearranges to the form needed
for the Ricci-symmetry trace argument. -/
private lemma riemannCurvature_const_first_swap_eq_neg
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (v : E) (X Y : SmoothVectorField I M) (x : M) :
    riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
        - riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x
      = -riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x := by
  classical
  set V : SmoothVectorField I M := SmoothVectorField.const (I := I) (M := M) v with hV_def
  have h_bianchi : riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
        + riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x
        + riemannCurvature g Y.toFun (fun _ : M => v) X.toFun x = 0 :=
    bianchi_first g V X Y x
  have h_antisym :
      riemannCurvature g Y.toFun (fun _ : M => v) X.toFun x
        = -riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x :=
    riemannCurvature_antisymm g Y.toFun (fun _ : M => v) X.toFun x
  rw [h_antisym] at h_bianchi
  apply eq_neg_of_add_eq_zero_left
  rw [show (riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
              - riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x
            + riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x
            : TangentSpace I x)
        = riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
            + riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x
            + -riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x from by abel]
  exact h_bianchi

/-- **Math.** $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

Reference: do Carmo §4 ex. 1.

Closure via:
* `LinearMap.trace_eq_sum_inner` on `curvatureEndo X Y x` against
  `stdOrthonormalBasis ℝ (T_xM)` (so each Ricci scalar is a sum of
  $\langle b_i, R(\mathrm{const}\,b_i, X)\,Y\,x\rangle$ pairings),
* `riemannCurvature_const_first_swap_eq_neg` per basis vector (Bianchi I +
  antisym packaging),
* `riemannCurvature_inner_self_zero` on $(X, Y, \mathrm{const}\,b_i)$ to kill
  every summand.

The hypothesis `h_interior` is required by `riemannCurvature_inner_self_zero`
(via the Hessian-Lie identity on boundary-aware models). -/
theorem ricci_symm
    [IsManifold I 2 M]
    (g : RiemannianMetric I M) (hg : g = hm.metric)
    (X Y : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I))) :
    ricci g X Y x = ricci g Y X x := by
  subst hg
  classical
  set b := stdOrthonormalBasis ℝ (TangentSpace I x) with hb_def
  have h_RXY : ricci hm.metric X Y x =
      ∑ i, ⟪b i, riemannCurvature hm.metric (fun _ : M => (b i : E)) X.toFun Y.toFun x⟫_ℝ := by
    show LinearMap.trace ℝ (TangentSpace I x)
          (curvatureEndo hm.metric X Y x) = _
    exact LinearMap.trace_eq_sum_inner _ b
  have h_RYX : ricci hm.metric Y X x =
      ∑ i, ⟪b i, riemannCurvature hm.metric (fun _ : M => (b i : E)) Y.toFun X.toFun x⟫_ℝ := by
    show LinearMap.trace ℝ (TangentSpace I x)
          (curvatureEndo hm.metric Y X x) = _
    exact LinearMap.trace_eq_sum_inner _ b
  rw [h_RXY, h_RYX]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_eq_zero, ← inner_sub_right,
      riemannCurvature_const_first_swap_eq_neg (I := I) (M := M) hm.metric (b i : E) X Y x]
  rw [inner_neg_right, neg_eq_zero]
  rw [real_inner_comm]
  exact riemannCurvature_inner_self_zero hm.metric X Y
    (SmoothVectorField.const (I := I) (M := M) (b i : E)) x h_interior


/-! ## Special metric predicates: flat manifold

These predicates describe properties of the ambient Riemannian metric
(via `[hm : HasMetric I M]` in scope); they do not take the metric as an
explicit argument because the underlying notations (`Riem`, `Ric_g`)
already consume the metric through the typeclass. -/

/-- **Math.** A Riemannian metric `g` is **flat** if its Riemann
curvature tensor vanishes pointwise. -/
def IsFlat (g : RiemannianMetric I M) : Prop :=
  ∀ (X Y Z : VectorFieldSection I M) (x : M), riemannCurvature g X Y Z x = 0

/-! ## Killing vector fields -/

/-- **Math.** A smooth vector field `X` is a **Killing vector field**
(for the metric) if the symmetric part of $\nabla X$ vanishes:
$g(\nabla_U X, W) + g(\nabla_W X, U) = 0$ for all $U, W$ at every point.
Equivalent to the Lie derivative $\mathcal{L}_X g = 0$ (the flow of $X$
is by isometries).

Reference: do Carmo §3 Ex. 5; Petersen Ch. 8. -/
def IsKilling (g : RiemannianMetric I M) (X : SmoothVectorField I M) : Prop :=
  ∀ (U W : SmoothVectorField I M) (y : M),
    g.metricInner y ((covDeriv g U X) y) (W y)
      + g.metricInner y ((covDeriv g W X) y) (U y) = 0

/-- **Math.** Covariantly differentiating the Killing equation.

For a Killing field `X`, the tensor
`(U, V, W) ↦ ⟪∇_U ∇_V X - ∇_{∇_U V} X, W⟫` is skew in its last two slots.
This is the textbook "differentiate the Killing equation and subtract the
connection terms" step. -/
private lemma IsKilling.second_covDeriv_inner_skew
    (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (hX : IsKilling g X)
    (U V W : SmoothVectorField I M) (x : M) :
    g.metricInner x
        (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x
          - covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x) (W x)
      + g.metricInner x
        (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x
          - covDeriv g (fun y => covDeriv g U.toFun W.toFun y) X.toFun x) (V x)
      = 0 := by
  classical
  let f : M → ℝ := fun y =>
    g.metricInner y (covDeriv g V.toFun X.toFun y) (W y)
  let kw_g : M → ℝ := fun y =>
    g.metricInner y (covDeriv g W.toFun X.toFun y) (V y)
  have h_kill_fun : (fun y : M => f y + kw_g y) = fun _ => 0 := by
    funext y
    exact hX V W y
  have h_deriv_zero : mDirDeriv (fun y : M => f y + kw_g y) x (U x) = 0 := by
    rw [h_kill_fun]
    rw [mDirDeriv, mfderiv_const]
    rfl
  have h_dVX : TangentSmoothAt (fun y : M => covDeriv g V.toFun X.toFun y) x :=
    covDeriv_smoothVF_smoothAt g V X x
  have h_dWX : TangentSmoothAt (fun y : M => covDeriv g W.toFun X.toFun y) x :=
    covDeriv_smoothVF_smoothAt g W X x
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
    exact g.metricInner_mdifferentiableAt_of_tangentSmoothAt h_dVX (W.smoothAt x)
  have hkw_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) kw_g x := by
    exact g.metricInner_mdifferentiableAt_of_tangentSmoothAt h_dWX (V.smoothAt x)
  have h_deriv_add :
      mDirDeriv (fun y : M => f y + kw_g y) x (U x)
        = mDirDeriv f x (U x) + mDirDeriv kw_g x (U x) := by
    unfold mDirDeriv
    rw [show (fun y : M => f y + kw_g y) = f + kw_g from rfl,
      mfderiv_add hf_mdiff hkw_mdiff]
    rfl
  have h_compat_f := leviCivitaConnection_metric_compatible g
    U.toFun (fun y : M => covDeriv g V.toFun X.toFun y) W.toFun x
    (U.smoothAt x) h_dVX (W.smoothAt x)
  have h_compat_g := leviCivitaConnection_metric_compatible g
    U.toFun (fun y : M => covDeriv g W.toFun X.toFun y) V.toFun x
    (U.smoothAt x) h_dWX (V.smoothAt x)
  change mDirDeriv f x (U x)
      = g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x) (W x)
        + g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
    at h_compat_f
  change mDirDeriv kw_g x (U x)
      = g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x) (V x)
        + g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x)
    at h_compat_g
  have h_expanded :
      g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x) (W x)
        + g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
        + (g.metricInner x
            (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x) (V x)
          + g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x))
        = 0 := by
    linarith [h_deriv_zero, h_deriv_add, h_compat_f, h_compat_g]
  have h_cross_W :
      g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
        = -g.metricInner x
            (covDeriv g (fun y : M => covDeriv g U.toFun W.toFun y) X.toFun x) (V x) := by
    have h := hX (SmoothVectorField.const (I := I) (M := M)
        (covDeriv g U.toFun W.toFun x)) V x
    change
      g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun W.toFun y) x))
          (V x)
        + g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x) = 0 at h
    have h_comm :
        g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
          + g.metricInner x
            ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun W.toFun y) x))
            (V x) = 0 := by
      rw [add_comm]
      exact h
    exact eq_neg_of_add_eq_zero_left h_comm
  have h_cross_V :
      g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x)
        = -g.metricInner x
            (covDeriv g (fun y : M => covDeriv g U.toFun V.toFun y) X.toFun x) (W x) := by
    have h := hX (SmoothVectorField.const (I := I) (M := M)
        (covDeriv g U.toFun V.toFun x)) W x
    change
      g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun V.toFun y) x))
          (W x)
        + g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x) = 0 at h
    have h_comm :
        g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x)
          + g.metricInner x
            ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun V.toFun y) x))
            (W x) = 0 := by
      rw [add_comm]
      exact h
    exact eq_neg_of_add_eq_zero_left h_comm
  rw [g.metricInner_sub_left, g.metricInner_sub_left]
  show g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x) (W x)
      - g.metricInner x (covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x) (W x)
      + (g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x) (V x)
        - g.metricInner x (covDeriv g (fun y => covDeriv g U.toFun W.toFun y) X.toFun x) (V x))
      = 0
  linarith [h_expanded, h_cross_W, h_cross_V]

/-- **Math.** Commutator of the second covariant derivative operator:
`H(U,V)X - H(V,U)X = R(U,V)X`, where
`H(U,V)X = ∇_U∇_V X - ∇_{∇_U V}X`. -/
private lemma second_covDeriv_commutator
    (g : RiemannianMetric I M)
    (X U V : SmoothVectorField I M) (x : M) :
    (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x
        - covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x)
      - (covDeriv g V.toFun (fun y => covDeriv g U.toFun X.toFun y) x
        - covDeriv g (fun y => covDeriv g V.toFun U.toFun y) X.toFun x)
      = riemannCurvature g U V X x := by
  rw [riemannCurvature_commutator_form]
  have h_torsion := covDeriv_sub_swap_eq_mlieBracket g U.toFun V.toFun x
    (U.smoothAt x) (V.smoothAt x)
  unfold covDeriv at h_torsion ⊢
  rw [← h_torsion]
  simp only [map_sub]
  abel_nf

/-- **Math.** **Killing field PDE**: a Killing vector field `X` satisfies
$$\nabla^2_{Y, Z} X = R(Y, X) Z$$
for all vector fields `Y, Z` and points `x`, where
$\nabla^2_{Y, Z} W := \nabla_Y(\nabla_Z W) - \nabla_{\nabla_Y Z} W$.

This is **the** PDE characterizing infinitesimal isometries — the
linearization of "flow generates isometries". Foundation for the
Bochner–Yano dimension bound `dim Isom(M) ≤ n(n+1)/2` and the rigidity
of constant-sectional-curvature manifolds.

With OpenGA's convention
`Riem(U,V)X = ∇_U∇_V X - ∇_V∇_U X - ∇_[U,V] X`, the right-hand side is
`riemannCurvature g Y X Z`, equivalently `-riemannCurvature g X Y Z`.

Reference: do Carmo, *Riemannian Geometry*, §3 Ex. 5; Petersen, Ch. 8 §2;
Cheeger–Ebin §1.84. -/
theorem IsKilling.second_covDeriv_eq_curvature
    (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (hX : IsKilling g X)
    (Y Z : SmoothVectorField I M) (x : M) :
    covDeriv g Y.toFun (covDeriv g Z X) x
      - covDeriv g (covDeriv g Y Z) X.toFun x
      = riemannCurvature g Y X Z x := by
  classical
  apply (g.metricInner_eq_iff_eq x _ _).mp
  intro w
  set W : SmoothVectorField I M := SmoothVectorField.const (I := I) (M := M) w with hW_def
  let A (U V W : SmoothVectorField I M) : ℝ :=
    g.metricInner x
      (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x
        - covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x) (W x)
  let C (U V W : SmoothVectorField I M) : ℝ :=
    g.metricInner x (riemannCurvature g U V X x) (W x)
  have h_skew_Y : A Y Z W + A Y W Z = 0 := by
    simpa [A] using IsKilling.second_covDeriv_inner_skew g X hX Y Z W x
  have h_skew_Z : A Z W Y + A Z Y W = 0 := by
    simpa [A] using IsKilling.second_covDeriv_inner_skew g X hX Z W Y x
  have h_skew_W : A W Y Z + A W Z Y = 0 := by
    simpa [A] using IsKilling.second_covDeriv_inner_skew g X hX W Y Z x
  have h_comm_YZ : A Y Z W - A Z Y W = C Y Z W := by
    have h := congrArg (fun v => g.metricInner x v (W x))
      (second_covDeriv_commutator g X Y Z x)
    change g.metricInner x
        ((covDeriv g Y.toFun (fun y => covDeriv g Z.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Y.toFun Z.toFun y) X.toFun x)
          - (covDeriv g Z.toFun (fun y => covDeriv g Y.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Z.toFun Y.toFun y) X.toFun x)) (W x)
        = g.metricInner x (riemannCurvature g Y Z X x) (W x) at h
    rw [g.metricInner_sub_left] at h
    simpa [A, C] using h
  have h_comm_ZW : A Z W Y - A W Z Y = C Z W Y := by
    have h := congrArg (fun v => g.metricInner x v (Y x))
      (second_covDeriv_commutator g X Z W x)
    change g.metricInner x
        ((covDeriv g Z.toFun (fun y => covDeriv g W.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Z.toFun W.toFun y) X.toFun x)
          - (covDeriv g W.toFun (fun y => covDeriv g Z.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g W.toFun Z.toFun y) X.toFun x)) (Y x)
        = g.metricInner x (riemannCurvature g Z W X x) (Y x) at h
    rw [g.metricInner_sub_left] at h
    simpa [A, C] using h
  have h_comm_WY : A W Y Z - A Y W Z = C W Y Z := by
    have h := congrArg (fun v => g.metricInner x v (Z x))
      (second_covDeriv_commutator g X W Y x)
    change g.metricInner x
        ((covDeriv g W.toFun (fun y => covDeriv g Y.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g W.toFun Y.toFun y) X.toFun x)
          - (covDeriv g Y.toFun (fun y => covDeriv g W.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Y.toFun W.toFun y) X.toFun x)) (Z x)
        = g.metricInner x (riemannCurvature g W Y X x) (Z x) at h
    rw [g.metricInner_sub_left] at h
    simpa [A, C] using h
  have h_curv : C Y Z W - C Z W Y + C W Y Z
      = 2 * g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
    have h_bianchi := bianchi_first g X W Y x
    have h_inner :
        g.metricInner x (riemannCurvature g X W Y x + riemannCurvature g W Y X x + riemannCurvature g Y X W x) (Z x)
          = 0 := by
      rw [h_bianchi]
      exact g.metricInner_zero_left x (Z x)
    rw [g.metricInner_add_left, g.metricInner_add_left] at h_inner
    have h_pair₁ : C Y Z W = g.metricInner x (riemannCurvature g X W Y x) (Z x) := by
      simpa [C] using riemannCurvature_pair_symm g Y Z X W x
    have h_pair₂ : C Z W Y = g.metricInner x (riemannCurvature g X Y Z x) (W x) := by
      simpa [C] using riemannCurvature_pair_symm g Z W X Y x
    have h_pair₃ : C W Y Z = g.metricInner x (riemannCurvature g X Z W x) (Y x) := by
      simpa [C] using riemannCurvature_pair_symm g W Y X Z x
    have h_antisym12 :
        g.metricInner x (riemannCurvature g X Y Z x) (W x)
          = -g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
      rw [riemannCurvature_antisymm g X.toFun Y.toFun Z.toFun x, g.metricInner_neg_left]
    have h_antisym34 :
        g.metricInner x (riemannCurvature g Y X W x) (Z x)
          = -g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
      have h := riemannCurvature_metric_skew g Y X W Z x (by
        rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
        exact Set.mem_univ _)
      linarith
    rw [h_pair₁, h_pair₂, h_pair₃]
    linarith [h_inner, h_antisym12, h_antisym34]
  have h_A : 2 * A Y Z W = C Y Z W - C Z W Y + C W Y Z := by
    linarith [h_skew_Y, h_skew_Z, h_skew_W, h_comm_YZ, h_comm_ZW, h_comm_WY]
  have h_target : A Y Z W = g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
    linarith [h_A, h_curv]
  simpa [A, hW_def] using h_target

/-! ## Sectional curvature

Pointwise sectional curvature
$$K_g(X, Y)(x) \;=\;
  \dfrac{g_x(R(X, Y) Y, X)}{\|X\|_g^2 \|Y\|_g^2 - g_x(X, Y)^2}$$
is the curvature of the 2-plane spanned by $X(x), Y(x)$. Well-defined
when the spanning is non-degenerate (denominator non-zero, i.e., $X(x),
Y(x)$ are linearly independent). Symmetric under swap $X \leftrightarrow Y$
by `riemannCurvature_pair_symm` + (1,2)/(3,4)-antisymmetries.

Reference: do Carmo §4 §3; Petersen Ch. 3 §2. -/

/-- **Math.** The **sectional curvature** of the 2-plane spanned by
$X(x), Y(x)$ at $x$:
$$K_g(X, Y)(x) := \dfrac{g_x(R(X, Y) Y, X)}
                       {g_x(X, X) \cdot g_x(Y, Y) - g_x(X, Y)^2}.$$

The denominator equals $\|X \wedge Y\|_g^2$ (squared area of the
parallelogram); $K$ is well-defined when the two vectors are linearly
independent (denominator non-zero). At linearly dependent inputs, the
formula returns the junk value $0$ via division by zero. -/
noncomputable def sectionalCurvature
    (g : RiemannianMetric I M)
    (X Y : VectorFieldSection I M) (x : M) : ℝ :=
  g.metricInner x (riemannCurvature g X Y Y x) (X x) /
    (g.metricInner x (X x) (X x) * g.metricInner x (Y x) (Y x)
      - g.metricInner x (X x) (Y x) ^ 2)

/-- **Math.** **Tangent-vector form** of sectional curvature: same
formula as `sectionalCurvature` but consuming the pointwise tangent
vectors $v, w \in T_xM$ directly via constant-section lifts. Useful when
$K$ is invoked on tangent vectors (paper notation $K(v, w)$) rather than
on vector fields. By $C^\infty(M)$-tensoriality of `riemannCurvature HasMetric.metric`,
the value depends only on $X(x), Y(x)$, so this is the canonical
pointwise function. -/
noncomputable def sectionalCurvatureAt
    (g : RiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) : ℝ :=
  sectionalCurvature (I := I) (M := M) g
    (fun _ : M => v) (fun _ : M => w) x

/-- **Math.** **Sectional curvature is symmetric in $X, Y$**:
$K_g(X, Y)(x) = K_g(Y, X)(x)$.

Numerator: $g(R(X,Y)Y, X) = g(R(Y,X)X, Y)$ via `riemannCurvature_pair_symm`
on $(X, Y, Y, X) \leftrightarrow (Y, X, X, Y)$, then a sign cancellation
using `riemannCurvature_antisymm` once in each slot.
Denominator: symmetric in $X, Y$ via `HasMetric.metric.metricInner_comm`. -/
theorem sectionalCurvature_symmetric
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    sectionalCurvature (I := I) g X Y x = sectionalCurvature (I := I) g Y X x := by
  unfold sectionalCurvature
  congr 1
  · have h_pair := riemannCurvature_pair_symm g X Y Y X x
    exact h_pair
  · have hXY : g.metricInner x (X x) (Y x) = g.metricInner x (Y x) (X x) :=
      g.metricInner_comm x _ _
    rw [hXY]; ring

end Riemannian
