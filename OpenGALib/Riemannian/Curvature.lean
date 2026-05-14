import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Riemannian.HessianLie
-- `Riem(X, Y) Z` notation is now defined inline in `Connection.lean`
-- alongside `riemannCurvature`; it transitively reaches us via the
-- `import OpenGALib.Riemannian.Connection` above.
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

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
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    Riem(X, Y) Z x = -Riem(Y, X) Z x := by
  simp only [riem_simp]
  rw [covDeriv_mlieBracket_swap_apply]
  abel

/-- **Math.** The endomorphism $z \mapsto R(z, X) Y(x)$ on $T_xM$ (with $z$ extended to
the constant section). Trace of this is the Ricci tensor at $x$. -/
noncomputable def curvatureEndo
    [IsManifold I 2 M]
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun z := riemannCurvature (fun _ => z) X Y x
  map_add' z₁ z₂ := by
    show riemannCurvature (fun _ => z₁ + z₂) X.toFun Y.toFun x
       = riemannCurvature (fun _ => z₁) X.toFun Y.toFun x
        + riemannCurvature (fun _ => z₂) X.toFun Y.toFun x
    -- Unfold riemannCurvature into 3 covDeriv terms.
    show covDeriv (fun _ => z₁ + z₂) (fun y => covDeriv X.toFun Y.toFun y) x
          - covDeriv X.toFun (fun y => covDeriv (fun _ => z₁ + z₂) Y.toFun y) x
          - covDeriv (fun y => mlieBracket I (fun _ => z₁ + z₂) X.toFun y) Y.toFun x
        = (covDeriv (fun _ => z₁) (fun y => covDeriv X.toFun Y.toFun y) x
            - covDeriv X.toFun (fun y => covDeriv (fun _ => z₁) Y.toFun y) x
            - covDeriv (fun y => mlieBracket I (fun _ => z₁) X.toFun y) Y.toFun x)
        + (covDeriv (fun _ => z₂) (fun y => covDeriv X.toFun Y.toFun y) x
            - covDeriv X.toFun (fun y => covDeriv (fun _ => z₂) Y.toFun y) x
            - covDeriv (fun y => mlieBracket I (fun _ => z₂) X.toFun y) Y.toFun x)
    -- Π-equality for adding constant sections.
    have h_const_add : ((fun _ : M => z₁ + z₂) : (y : M) → TangentSpace I y)
        = (fun _ => z₁) + (fun _ => z₂) := by funext y; rfl
    -- Term 1: covDeriv (fun _ => z) F x = lev.toFun F x z is continuous linear map-linear in z.
    have hT1 : covDeriv (fun _ : M => z₁ + z₂) (fun y => covDeriv X.toFun Y.toFun y) x
        = covDeriv (fun _ => z₁) (fun y => covDeriv X.toFun Y.toFun y) x
        + covDeriv (fun _ => z₂) (fun y => covDeriv X.toFun Y.toFun y) x := by
      show (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) (z₁ + z₂)
          = (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) z₁
          + (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) z₂
      exact map_add _ _ _
    -- Term 2: inner field `fun y => covDeriv (fun _ => z) Y y = lev.toFun Y y z`.
    -- continuous linear map-linear in z, so the inner field is the pointwise sum.
    have h_inner_add : (fun y => covDeriv (fun _ : M => z₁ + z₂) Y.toFun y)
        = (fun y => covDeriv (fun _ => z₁) Y.toFun y)
          + (fun y => covDeriv (fun _ => z₂) Y.toFun y) := by
      funext y
      show (leviCivitaConnection.toFun Y.toFun y) (z₁ + z₂)
          = (leviCivitaConnection.toFun Y.toFun y) z₁
          + (leviCivitaConnection.toFun Y.toFun y) z₂
      exact map_add _ _ _
    -- Smoothness of each summand: `(fun y => covDeriv (fun _ => z) Y y) =
    -- (fun y => lev.toFun Y y z)` is smooth via `leviCivitaConnection`'s
    -- isCovariantDerivativeOnUniv applied at the constant section.
    have h_const_z₁_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => z₁) y :=
      fun y => (cF[z₁]).smoothAt y
    have h_const_z₂_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => z₂) y :=
      fun y => (cF[z₂]).smoothAt y
    have hY_smooth := Y.smoothAt
    have hT2 : covDeriv X.toFun (fun y => covDeriv (fun _ : M => z₁ + z₂) Y.toFun y) x
        = covDeriv X.toFun (fun y => covDeriv (fun _ => z₁) Y.toFun y) x
        + covDeriv X.toFun (fun y => covDeriv (fun _ => z₂) Y.toFun y) x := by
      rw [h_inner_add]
      apply covDeriv_add_field
      · exact covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z₁ Y x
      · exact covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z₂ Y x
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
    have hT3 : covDeriv (fun y => mlieBracket I (fun _ : M => z₁ + z₂) X.toFun y) Y.toFun x
        = covDeriv (fun y => mlieBracket I (fun _ => z₁) X.toFun y) Y.toFun x
        + covDeriv (fun y => mlieBracket I (fun _ => z₂) X.toFun y) Y.toFun x := by
      rw [h_lieBr_add]
      -- For the OUTER covDeriv, the field A vs A+B issue: covDeriv is
      -- linear in the FIRST (direction) argument via continuous linear map, since
      -- covDeriv F G x = lev.toFun G x (F x), and `(F + G) x = F x + G x`.
      show (leviCivitaConnection.toFun Y.toFun x)
          ((fun y => mlieBracket I (fun _ => z₁) X.toFun y) x
            + (fun y => mlieBracket I (fun _ => z₂) X.toFun y) x)
        = (leviCivitaConnection.toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ => z₁) X.toFun y) x)
          + (leviCivitaConnection.toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ => z₂) X.toFun y) x)
      exact map_add _ _ _
    rw [hT1, hT2, hT3]
    abel
  map_smul' c z := by
    show riemannCurvature (fun _ => c • z) X.toFun Y.toFun x
       = c • riemannCurvature (fun _ => z) X.toFun Y.toFun x
    show covDeriv (fun _ => c • z) (fun y => covDeriv X.toFun Y.toFun y) x
          - covDeriv X.toFun (fun y => covDeriv (fun _ => c • z) Y.toFun y) x
          - covDeriv (fun y => mlieBracket I (fun _ => c • z) X.toFun y) Y.toFun x
        = c • (covDeriv (fun _ => z) (fun y => covDeriv X.toFun Y.toFun y) x
            - covDeriv X.toFun (fun y => covDeriv (fun _ => z) Y.toFun y) x
            - covDeriv (fun y => mlieBracket I (fun _ => z) X.toFun y) Y.toFun x)
    have h_const_smul : ((fun _ : M => c • z) : (y : M) → TangentSpace I y)
        = c • (fun _ => z) := by funext y; rfl
    have h_const_z_smooth : ∀ y, TangentSmoothAt (fun _ : M => z) y :=
      fun y => (cF[z]).smoothAt y
    have hY_smooth := Y.smoothAt
    -- Term 1: continuous linear map map_smul.
    have hT1 : covDeriv (fun _ : M => c • z) (fun y => covDeriv X.toFun Y.toFun y) x
        = c • covDeriv (fun _ => z) (fun y => covDeriv X.toFun Y.toFun y) x := by
      show (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) (c • z)
          = c • (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) z
      exact ContinuousLinearMap.map_smul _ _ _
    -- Term 2.
    have h_inner_smul : (fun y => covDeriv (fun _ : M => c • z) Y.toFun y)
        = c • (fun y => covDeriv (fun _ => z) Y.toFun y) := by
      funext y
      show (leviCivitaConnection.toFun Y.toFun y) (c • z)
          = c • (leviCivitaConnection.toFun Y.toFun y) z
      exact ContinuousLinearMap.map_smul _ _ _
    have hT2 : covDeriv X.toFun (fun y => covDeriv (fun _ : M => c • z) Y.toFun y) x
        = c • covDeriv X.toFun (fun y => covDeriv (fun _ => z) Y.toFun y) x := by
      rw [h_inner_smul]
      apply covDeriv_smul_const_field
      exact covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z Y x
    -- Term 3.
    have h_lieBr_smul : (fun y => mlieBracket I (fun _ : M => c • z) X.toFun y)
        = c • (fun y => mlieBracket I (fun _ => z) X.toFun y) := by
      funext y
      rw [show ((fun _ : M => c • z) : (y : M) → TangentSpace I y)
          = c • (fun _ => z) from h_const_smul]
      exact VectorField.mlieBracket_const_smul_left (h_const_z_smooth y)
    have hT3 : covDeriv (fun y => mlieBracket I (fun _ : M => c • z) X.toFun y) Y.toFun x
        = c • covDeriv (fun y => mlieBracket I (fun _ => z) X.toFun y) Y.toFun x := by
      rw [h_lieBr_smul]
      show (leviCivitaConnection.toFun Y.toFun x)
          ((c • fun y => mlieBracket I (fun _ : M => z) X.toFun y) x)
        = c • (leviCivitaConnection.toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ : M => z) X.toFun y) x)
      show (leviCivitaConnection.toFun Y.toFun x)
          (c • mlieBracket I (fun _ => z) X.toFun x)
        = c • (leviCivitaConnection.toFun Y.toFun x)
            (mlieBracket I (fun _ => z) X.toFun x)
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT1, hT2, hT3]
    -- Goal: c • A - c • B - c • C = c • (A - B - C)
    rw [smul_sub, smul_sub]

/-- **Math.** The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at $x$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{curvatureEndo}\,X\,Y\,x).$$

Reference: do Carmo §4 ex. 1. -/
noncomputable def ricci
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (curvatureEndo X Y x)

/-- **Math.** The Ricci curvature as a scalar function on the manifold:
`(Ric(X, Y))(x) = ricci X Y x`. -/
scoped[Riemannian] notation:max "Ric(" X ", " Y ")" => ricci X Y

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
and `leviCivitaConnection.toFun` (definitionally equal to `covDeriv`)
on the RHS. -/
private lemma mDirDeriv_self_eq_two_metricInner_leviCivita_self
    (V : Π y : M, TangentSpace I y) (Z : SmoothVectorField I M) (y : M)
    (hV : TangentSmoothAt V y) :
    mDirDeriv (fun y' => metricInner y' (Z y') (Z y')) y (V y)
      = 2 * metricInner y
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y)) (Z y) := by
  -- Re-state metric-compat in `.toFun` form (def-eq to the ∇-form result)
  -- so the subsequent `rw [hsym]` pattern fires on the structural shape.
  have h :
      mfderiv I 𝓘(ℝ, ℝ) (fun y' => metricInner y' (Z y') (Z y')) y (V y)
        = metricInner y
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y)) (Z y)
          + metricInner y (Z y)
              ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y)) :=
    leviCivitaConnection_metric_compatible V Z.toFun Z.toFun y
      hV (Z.smoothAt y) (Z.smoothAt y)
  have hsym :
      metricInner y (Z y)
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y))
        = metricInner y
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y)) (Z y) :=
    metricInner_comm y _ _
  rw [hsym] at h
  have h_ℝ : mDirDeriv (fun y' => metricInner y' (Z y') (Z y')) y (V y)
      = metricInner y
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y)) (Z y)
        + metricInner y
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y (V y)) (Z y) :=
    h
  rw [h_ℝ]; ring

/-- **Eng.** Function-equality form: at every $y$, the directional derivative of
$y \mapsto g(Z, Z)(y)$ along the smooth vector field $V$ equals
$2\,g(\nabla_V Z, Z)(y)$. -/
private lemma fun_mDirDeriv_self_eq_two_metricInner_leviCivita_self
    (V Z : SmoothVectorField I M) :
    (fun y' : M => mDirDeriv (fun y'' => metricInner y'' (Z y'') (Z y'')) y' (V.toFun y'))
      = (fun y' : M => 2 * metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := by
  funext y'
  exact mDirDeriv_self_eq_two_metricInner_leviCivita_self V.toFun Z y' (V.smoothAt y')

/-- **Math.** **Iterated metric-compat identity at $x$**: differentiating the
diagonal identity once more at $x$ in direction $W(x)$ and applying
metric-compat at $x$ yields
$$\tfrac12\,W\!\left(V (g(Z, Z))\right)(x)
  = \langle \nabla_W \nabla_V Z, Z\rangle_g(x)
    + \langle \nabla_V Z, \nabla_W Z\rangle_g(x).$$ -/
private lemma half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv
    [IsManifold I 2 M]
    (V W Z : SmoothVectorField I M) (x : M) :
    (1/2 : ℝ) * mDirDeriv
        (fun y' : M => mDirDeriv
          (fun y'' => metricInner y'' (Z y'') (Z y'')) y' (V.toFun y')) x (W.toFun x)
      = metricInner x
          ((leviCivitaConnection (I := I) (M := M)).toFun
            (fun y' => covDeriv V.toFun Z.toFun y') x (W.toFun x))
          (Z x)
        + metricInner x (covDeriv V.toFun Z.toFun x)
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (W.toFun x)) := by
  -- Use function-equality form of the diagonal identity to rewrite the LHS
  -- inner function; then apply mfderiv_const_smul and metric-compat at x.
  have h_fun := fun_mDirDeriv_self_eq_two_metricInner_leviCivita_self V Z
  -- Sections smooth at x.
  have hcovVZ : TangentSmoothAt (fun y' => covDeriv V.toFun Z.toFun y') x :=
    covDeriv_smoothVF_smoothAt V Z x
  -- The mfderiv of LHS (the iterated mDirDeriv expression) at x in dir W(x):
  -- by h_fun, equals mfderiv of `fun y' => 2 * g(∇_V Z, Z)(y')` at x in dir W(x).
  -- That = 2 * mfderiv (g(∇_V Z, Z)) x (W x), and by metric-compat at x:
  --      = 2 * [g(∇_W ∇_V Z, Z) + g(∇_V Z, ∇_W Z)] x.
  -- So (1/2) * LHS = g(∇_W ∇_V Z, Z) x + g(∇_V Z, ∇_W Z) x.
  -- Pin the metric-compat result in `.toFun` form (def-eq to ∇ form) so the
  -- downstream `metricInner_comm` / `linarith` chains pattern-match.
  have h_compat :
      mfderiv I 𝓘(ℝ, ℝ)
          (fun y' => metricInner y' (covDeriv V.toFun Z.toFun y') (Z.toFun y')) x
          (W.toFun x)
        = metricInner x
            ((leviCivitaConnection (I := I) (M := M)).toFun
              (fun y' => covDeriv V.toFun Z.toFun y') x (W.toFun x)) (Z.toFun x)
          + metricInner x (covDeriv V.toFun Z.toFun x)
              ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (W.toFun x)) :=
    leviCivitaConnection_metric_compatible
      W.toFun (fun y' => covDeriv V.toFun Z.toFun y') Z.toFun x
      (W.smoothAt x) hcovVZ (Z.smoothAt x)
  -- h_compat : mfderiv (fun y' => g(∇_V Z, Z) y') x (W x) =
  --              g(∇_W (∇_V Z), Z) + g(∇_V Z, ∇_W Z)
  -- Rewrite the LHS function via h_fun:
  conv_lhs => rw [show (fun y' : M => mDirDeriv
        (fun y'' => metricInner y'' (Z y'') (Z y'')) y' (V.toFun y'))
      = (fun y' : M => 2 * metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')) from h_fun]
  -- Now LHS = (1/2) * mfderiv (fun y' => 2 * g(∇_V Z, Z) y') x (W x)
  -- Pull the 2 out: mfderiv (2 * h) x v = 2 * mfderiv h x v (linear).
  -- The function under mfderiv:  fun y' => 2 * g(LC.toFun Z y' (V y'), Z y')
  -- equals  2 • (fun y' => g(LC.toFun Z y' (V y'), Z y'))  via funext.
  -- Use mfderiv_const_smul; we need MDifferentiableAt of the inner section.
  -- The "covDeriv V Z = LC.toFun Z y (V y)" is def-eq; the inner section's
  -- smoothness at x is hcovVZ (via metricInner_mdifferentiableAt).
  have h_inner_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y' : M => metricInner y'
        ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
        (Z y')) x := by
    -- The function is `y' ↦ g(covDeriv V Z y', Z y')` (def-eq covDeriv ↔ LC.toFun).
    -- Use `metricInner_mdifferentiableAt` with `hcovVZ` and `Z.smoothAt x`.
    have h := hm.metric.metricInner_mdifferentiableAt
      (v := fun y' => covDeriv V.toFun Z.toFun y') (w := Z.toFun) hcovVZ (Z.smoothAt x)
    exact h
  -- Avoid continuous linear map-smul issues by writing `2 * h = h + h` and using `mfderiv_add`.
  have h_two_add : (fun y' : M => (2 : ℝ) * metricInner y'
        ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
        (Z y'))
      = (fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')
        + metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := by
    funext y'; ring
  rw [h_two_add]
  -- Now: (1/2) * mDirDeriv (fun y' => h y' + h y') x (W x) where h := g(∇_V Z, Z) y'.
  -- Convert `fun y' => h y' + h y'` to the Pi-add form `h + h` (definitional).
  have h_pi_add : (fun y' : M => metricInner y'
        ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
        (Z y')
      + metricInner y'
        ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
        (Z y'))
      = (fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := rfl
  rw [h_pi_add]
  -- `mfderiv (f + g) x v = mfderiv f x v + mfderiv g x v`.
  -- Compute the continuous linear map add via `mfderiv_add` then evaluate at `W.toFun x`.
  have h_clm_add :
      mfderiv I 𝓘(ℝ, ℝ) ((fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => metricInner y'
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
            (Z y'))) x
        = mfderiv I 𝓘(ℝ, ℝ) (fun y' : M => metricInner y'
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
            (Z y')) x
          + mfderiv I 𝓘(ℝ, ℝ) (fun y' : M => metricInner y'
              ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
              (Z y')) x :=
    mfderiv_add h_inner_mdiff h_inner_mdiff
  -- Apply both sides to (W.toFun x) and use continuous linear map-add evaluation.
  have h_val_add : mDirDeriv ((fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => metricInner y'
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
            (Z y'))) x (W.toFun x)
      = mDirDeriv (fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')) x (W.toFun x)
        + mDirDeriv (fun y' : M => metricInner y'
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
            (Z y')) x (W.toFun x) := by
    show mfderiv I 𝓘(ℝ, ℝ) _ x (W.toFun x) = _
    rw [h_clm_add]
    rfl
  rw [h_val_add]
  -- Now: (1/2) * (mDirDeriv h x v + mDirDeriv h x v) = h_compat
  have h_compat_ℝ :
      mDirDeriv (fun y' : M => metricInner y'
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun y' (V.toFun y'))
          (Z y')) x (W.toFun x)
        = metricInner x
            ((leviCivitaConnection (I := I) (M := M)).toFun
              (fun y' => covDeriv V.toFun Z.toFun y') x (W.toFun x))
            (Z x)
          + metricInner x (covDeriv V.toFun Z.toFun x)
            ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (W.toFun x)) :=
    h_compat
  rw [h_compat_ℝ]; ring

/-- **Math.** $\langle R(X, Y) Z, Z \rangle_g(x) = 0$ for smooth vector fields
$X, Y, Z$, with $x$ in the closure of the interior of $\mathrm{range}\,I$
(required by the Hessian–Lie identity for boundary-aware models).

Reference: do Carmo §4 Proposition 2.5(iii). -/
theorem riemannCurvature_inner_self_zero
    [IsManifold I 2 M]
    (X Y Z : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I))) :
    metricInner x (Riem(X.toFun, Y.toFun) Z.toFun x) (Z x) = 0 := by
  classical
  -- Setup: f := g(Z, Z), the self-norm-squared scalar function.
  set f : M → ℝ := fun y' => metricInner y' (Z y') (Z y') with hf_def
  -- f is C∞ globally, hence C² at x.
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := fun y =>
    hm.metric.metricInner_contMDiffAt (n := ∞) (Z.smooth y) (Z.smooth y)
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf_smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  -- [X, Y] is smooth at x (Mathlib + framework's mlieBracket_tangentSmoothAt).
  have hXY_br : TangentSmoothAt (mlieBracket I X.toFun Y.toFun) x :=
    mlieBracket_tangentSmoothAt X.smooth Y.smooth
  -- Equations (A) and (B): iterated metric-compat at x.
  have hA := half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv X Y Z x  -- (V=X, W=Y)
  have hB := half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv Y X Z x  -- (V=Y, W=X)
  -- Equation (C): metric-compat at x for V = [X, Y].
  have hC := mDirDeriv_self_eq_two_metricInner_leviCivita_self
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
  have h_inner_comm : metricInner x (covDeriv X.toFun Z.toFun x)
        ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (Y.toFun x))
      = metricInner x (covDeriv Y.toFun Z.toFun x)
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (X.toFun x)) := by
    show metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (X.toFun x))
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (Y.toFun x))
      = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (Y.toFun x))
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x (X.toFun x))
    exact metricInner_comm x _ _
  -- Expand R via riemannCurvature_def + metricInner_sub_left twice.
  show metricInner x (riemannCurvature X.toFun Y.toFun Z.toFun x) (Z x) = 0
  rw [riemannCurvature_def]
  -- Goal: g(∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z, Z) x = 0
  rw [show metricInner x (covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
        - covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x
        - covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x) (Z x)
      = metricInner x (covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x) (Z x)
        - metricInner x (covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x) (Z x)
        - metricInner x (covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x) (Z x)
      from by
    rw [show ((covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
          - covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x
          - covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x : TangentSpace I x))
        = (covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
          - covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x)
          - covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x from rfl,
      metricInner_sub_left, metricInner_sub_left]]
  -- Now: g(∇_X ∇_Y Z, Z) - g(∇_Y ∇_X Z, Z) - g(∇_{[X,Y]} Z, Z) = 0
  -- From hB (V=Y, W=X): (1/2) X(Y(f))(x) = g(∇_X ∇_Y Z, Z) + g(∇_Y Z, ∇_X Z)
  --                    ⇒ g(∇_X ∇_Y Z, Z) = (1/2) X(Y(f))(x) - g(∇_Y Z, ∇_X Z)
  -- From hA (V=X, W=Y): g(∇_Y ∇_X Z, Z) = (1/2) Y(X(f))(x) - g(∇_X Z, ∇_Y Z)
  -- From hC: 2 g(∇_{[X,Y]} Z, Z) = D_{[X,Y]} f(x)
  --        ⇒ g(∇_{[X,Y]} Z, Z) = (1/2) D_{[X,Y]} f(x) = (1/2) mDirDeriv f x ([X,Y] x)
  -- Combine: difference = (1/2) [X(Y(f)) - Y(X(f)) - [X,Y](f)] - inner cross-cancel = 0.
  -- Show all four covDeriv terms are def-equal to LC.toFun forms:
  show metricInner x
        ((leviCivitaConnection (I := I) (M := M)).toFun
          (fun y => covDeriv Y.toFun Z.toFun y) x (X.toFun x)) (Z x)
      - metricInner x
          ((leviCivitaConnection (I := I) (M := M)).toFun
            (fun y => covDeriv X.toFun Z.toFun y) x (Y.toFun x)) (Z x)
      - metricInner x
          ((leviCivitaConnection (I := I) (M := M)).toFun Z.toFun x
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

/-- **Math.** **Additivity of `riemannCurvature` in the differentiated (3rd) slot**:
$R(X, Y)(Z_1 + Z_2)(x) = R(X, Y) Z_1(x) + R(X, Y) Z_2(x)$ for $X, Y, Z_i$
smooth vector fields. Direct from `covDeriv_add_field` applied at $x$
(outer) and at every $y$ (inner section sum) plus `funext`.

Public-exposure of formerly `private` helper, needed by the Z-slot
additivity step of the full 3-slot tensoriality chain
(`Riemannian/Curvature/Tensoriality.lean`). -/
theorem riemannCurvature_add_third
    (X Y Z₁ Z₂ : SmoothVectorField I M) (x : M) :
    riemannCurvature X.toFun Y.toFun (Z₁ + Z₂).toFun x
      = riemannCurvature X.toFun Y.toFun Z₁.toFun x
        + riemannCurvature X.toFun Y.toFun Z₂.toFun x := by
  classical
  -- Pi-add of toFun.
  have h_pi_add : (Z₁ + Z₂).toFun = Z₁.toFun + Z₂.toFun := by
    funext y; show (Z₁ + Z₂) y = Z₁ y + Z₂ y; rfl
  -- Inner section additivity (covDeriv Y (Z₁+Z₂) y = covDeriv Y Z₁ y + covDeriv Y Z₂ y).
  have h_inner_Y : (fun y => covDeriv Y.toFun (Z₁ + Z₂).toFun y)
      = (fun y => covDeriv Y.toFun Z₁.toFun y)
        + (fun y => covDeriv Y.toFun Z₂.toFun y) := by
    funext y
    rw [h_pi_add]
    exact covDeriv_add_field Y.toFun Z₁.toFun Z₂.toFun y
      (Z₁.smoothAt y) (Z₂.smoothAt y)
  have h_inner_X : (fun y => covDeriv X.toFun (Z₁ + Z₂).toFun y)
      = (fun y => covDeriv X.toFun Z₁.toFun y)
        + (fun y => covDeriv X.toFun Z₂.toFun y) := by
    funext y
    rw [h_pi_add]
    exact covDeriv_add_field X.toFun Z₁.toFun Z₂.toFun y
      (Z₁.smoothAt y) (Z₂.smoothAt y)
  -- Unfold riemannCurvature.
  show covDeriv X.toFun (fun y => covDeriv Y.toFun (Z₁ + Z₂).toFun y) x
      - covDeriv Y.toFun (fun y => covDeriv X.toFun (Z₁ + Z₂).toFun y) x
      - covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) (Z₁ + Z₂).toFun x
    = (covDeriv X.toFun (fun y => covDeriv Y.toFun Z₁.toFun y) x
        - covDeriv Y.toFun (fun y => covDeriv X.toFun Z₁.toFun y) x
        - covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z₁.toFun x)
      + (covDeriv X.toFun (fun y => covDeriv Y.toFun Z₂.toFun y) x
        - covDeriv Y.toFun (fun y => covDeriv X.toFun Z₂.toFun y) x
        - covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z₂.toFun x)
  rw [h_inner_Y, h_inner_X, h_pi_add]
  rw [covDeriv_add_field X.toFun (fun y => covDeriv Y.toFun Z₁.toFun y)
        (fun y => covDeriv Y.toFun Z₂.toFun y) x
        (covDeriv_smoothVF_smoothAt Y Z₁ x)
        (covDeriv_smoothVF_smoothAt Y Z₂ x),
      covDeriv_add_field Y.toFun (fun y => covDeriv X.toFun Z₁.toFun y)
        (fun y => covDeriv X.toFun Z₂.toFun y) x
        (covDeriv_smoothVF_smoothAt X Z₁ x)
        (covDeriv_smoothVF_smoothAt X Z₂ x),
      covDeriv_add_field (VectorField.mlieBracket I X.toFun Y.toFun)
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
    (X Y Z W : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I))) :
    metricInner x (Riem(X.toFun, Y.toFun) Z.toFun x) (W x)
      + metricInner x (Riem(X.toFun, Y.toFun) W.toFun x) (Z x) = 0 := by
  -- Diagonal-zero applied to U = Z+W, Z, W.
  have h_ZW := riemannCurvature_inner_self_zero X Y (Z + W) x h_interior
  have h_Z := riemannCurvature_inner_self_zero X Y Z x h_interior
  have h_W := riemannCurvature_inner_self_zero X Y W x h_interior
  -- Additivity of R in 3rd slot.
  have h_add := riemannCurvature_add_third X Y Z W x
  -- (Z+W) x = Z x + W x.
  have h_ZW_x : (Z + W) x = Z x + W x := rfl
  -- Expand h_ZW via h_add and h_ZW_x and bilinearity of metricInner.
  rw [h_add, h_ZW_x, metricInner_add_left, metricInner_add_right,
      metricInner_add_right] at h_ZW
  -- h_ZW : g(R Z, Z) + g(R Z, W) + (g(R W, Z) + g(R W, W)) = 0
  linarith

/-! ### Constant-direction commutator simplification

`R(const v, const w) Z x = ∇_v ∇_w Z - ∇_w ∇_v Z` at $x$ — the
$\nabla_{[X, Y]} Z$ term drops because $[\mathrm{const}\,v, \mathrm{const}\,w] = 0$
as a global section (`mlieBracket_const_const_apply_zero`), so the connection
evaluates `leviCivitaConnection.toFun Z x` at the zero vector. -/

/-- **Eng.** **No-bracket form of `riemannCurvature` for constant directions**. -/
theorem riemannCurvature_const_const_eq_commutator
    (v w : E) (Z : Π y : M, TangentSpace I y) (x : M) :
    riemannCurvature (fun _ : M => v) (fun _ : M => w) Z x
      = covDeriv (fun _ : M => v)
          (fun y => covDeriv (fun _ : M => w) Z y) x
        - covDeriv (fun _ : M => w)
          (fun y => covDeriv (fun _ : M => v) Z y) x := by
  rw [riemannCurvature_def]
  -- Third term is `covDeriv (mlieBracket I (const v) (const w)) Z x`. Show it's zero.
  have h_br : VectorField.mlieBracket I (fun _ : M => v) (fun _ : M => w) x = 0 :=
    mlieBracket_const_const_apply_zero v w x
  -- `covDeriv U Z x = leviCivitaConnection.toFun Z x (U x)`; with `U x = 0`,
  -- continuous linear map linearity gives zero.
  have h_third :
      covDeriv (VectorField.mlieBracket I (fun _ : M => v) (fun _ : M => w)) Z x = 0 := by
    show (leviCivitaConnection (I := I) (M := M)).toFun Z x
        (VectorField.mlieBracket I (fun _ : M => v) (fun _ : M => w) x) = 0
    rw [h_br]
    exact map_zero _
  rw [h_third, sub_zero]

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
    (v : E) (X Y : SmoothVectorField I M) (x : M) :
    riemannCurvature (fun _ : M => v) X.toFun Y.toFun x
        - riemannCurvature (fun _ : M => v) Y.toFun X.toFun x
      = -riemannCurvature X.toFun Y.toFun (fun _ : M => v) x := by
  classical
  set V : SmoothVectorField I M := SmoothVectorField.const (I := I) (M := M) v with hV_def
  -- Jacobi identity at x from Mathlib (`leibniz_identity_mlieBracket_apply`),
  -- with smoothness witnesses at level `minSmoothness ℝ 2` (downgraded from ∞).
  have hV_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, V.toFun y⟩ : TangentBundle I M)) x := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (V.smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hX_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) x := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (X.smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hY_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) x := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (Y.smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  haveI hM3 : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have h_jac := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) (M := M) (U := V.toFun) (V := X.toFun) (W := Y.toFun)
    hV_2 hX_2 hY_2
  -- Bianchi I with (X', Y', Z') = (V, X, Y). Use the unfolded `V.toFun = fun _ => v`
  -- form so the rewrite by `h_antisym` (using the `fun _ => v` shape) fires.
  have h_bianchi : riemannCurvature (fun _ : M => v) X.toFun Y.toFun x
        + riemannCurvature X.toFun Y.toFun (fun _ : M => v) x
        + riemannCurvature Y.toFun (fun _ : M => v) X.toFun x = 0 :=
    bianchi_first V X Y x h_jac
  -- First-pair antisymmetry on the 3rd Bianchi summand.
  have h_antisym :
      riemannCurvature Y.toFun (fun _ : M => v) X.toFun x
        = -riemannCurvature (fun _ : M => v) Y.toFun X.toFun x :=
    riemannCurvature_antisymm Y.toFun (fun _ : M => v) X.toFun x
  rw [h_antisym] at h_bianchi
  -- h_bianchi : R(V,X) Y + R(X,Y) V + - R(V,Y) X = 0
  -- Goal: R(V,X) Y - R(V,Y) X = -R(X,Y) V  ⇔  (R(V,X) Y - R(V,Y) X) + R(X,Y) V = 0.
  apply eq_neg_of_add_eq_zero_left
  -- Rearrange h_bianchi via `abel`.
  rw [show (riemannCurvature (fun _ : M => v) X.toFun Y.toFun x
              - riemannCurvature (fun _ : M => v) Y.toFun X.toFun x
            + riemannCurvature X.toFun Y.toFun (fun _ : M => v) x
            : TangentSpace I x)
        = riemannCurvature (fun _ : M => v) X.toFun Y.toFun x
            + riemannCurvature X.toFun Y.toFun (fun _ : M => v) x
            + -riemannCurvature (fun _ : M => v) Y.toFun X.toFun x from by abel]
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
    (X Y : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I))) :
    Ric(X, Y) x = Ric(Y, X) x := by
  classical
  set b := stdOrthonormalBasis ℝ (TangentSpace I x) with hb_def
  -- Expand each Ricci scalar as `∑ i, ⟪b i, R(const b i, ·) · x⟫_ℝ` via
  -- `LinearMap.trace_eq_sum_inner`.
  have h_RXY : Ric(X, Y) x =
      ∑ i, ⟪b i, riemannCurvature (fun _ : M => (b i : E)) X.toFun Y.toFun x⟫_ℝ := by
    show LinearMap.trace ℝ (TangentSpace I x) (curvatureEndo X Y x) = _
    exact LinearMap.trace_eq_sum_inner _ b
  have h_RYX : Ric(Y, X) x =
      ∑ i, ⟪b i, riemannCurvature (fun _ : M => (b i : E)) Y.toFun X.toFun x⟫_ℝ := by
    show LinearMap.trace ℝ (TangentSpace I x) (curvatureEndo Y X x) = _
    exact LinearMap.trace_eq_sum_inner _ b
  rw [h_RXY, h_RYX]
  -- Per i: the two inner products are equal (their difference vanishes
  -- by const-swap Bianchi + diagonal-zero).
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_eq_zero, ← inner_sub_right,
      riemannCurvature_const_first_swap_eq_neg (I := I) (M := M) (b i : E) X Y x]
  -- Goal: ⟪b i, -R(X, Y) (const b i) x⟫_ℝ = 0
  rw [inner_neg_right, neg_eq_zero]
  -- Goal: ⟪b i, R(X, Y) (const b i) x⟫_ℝ = 0
  -- Use real_inner_comm + riemannCurvature_inner_self_zero (with Z = cF[b i]).
  rw [real_inner_comm]
  -- Goal: ⟪R(X, Y) (const b i) x, b i⟫_ℝ = 0 (def-eq metricInner via hm.metric).
  exact riemannCurvature_inner_self_zero X Y
    (SmoothVectorField.const (I := I) (M := M) (b i : E)) x h_interior


end Riemannian

