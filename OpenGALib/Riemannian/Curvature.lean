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

For a Riemannian manifold $(M, g)$ with Levi-Civita connection $\nabla$:

* The **Riemann curvature tensor** is the trilinear map on vector fields
  $$R(X, Y) Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z.$$
* The **Ricci curvature** is the trace of the curvature endomorphism
  $z \mapsto R(z, X) Y$ on $T_xM$:
  $$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}\bigl(z \mapsto R(z, X) Y(x)\bigr).$$
* The **scalar curvature** is the metric trace of the Ricci tensor
  $$\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x) = \mathrm{tr}(\mathrm{Ric}^{\sharp}_x).$$

`riemannCurvature` itself lives in `Riemannian.Connection.Bianchi` (it is
connection-level, not metric). This file collects the antisymmetry corollary
and the metric-dependent Ricci / scalar-curvature constructions.

## Main definitions

* `curvatureEndo X Y x` — the endomorphism $z \mapsto R(z, X) Y(x)$ on $T_xM$.
* `ricci X Y x` — the Ricci scalar $\mathrm{Ric}(X, Y)(x)$ as $\mathrm{tr}(\mathrm{curvatureEndo}\,X\,Y\,x)$.
* `ricciTensor x` — the Ricci tensor at $x$ as a bilinear form on $T_xM$.
* `ricciSharp x` — the Ricci endomorphism $\mathrm{Ric}^{\sharp}_x$ via metric raising.
* `scalarCurvature x` — the scalar curvature $\mathrm{scal}(x) = \mathrm{tr}(\mathrm{ricciSharp}\,x)$.

## Main results

* `riemannCurvature_antisymm` — $R(X, Y) Z = -R(Y, X) Z$.
* `riemannCurvature_inner_self_zero` — $\langle R(X, Y) Z, Z \rangle_g = 0$.
* `ricci_symm` — $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

Reference: do Carmo 1992 §4.
-/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- Constant smooth vector field at a tangent vector. Hides
`SmoothVectorField.const (I := I) (M := M) V` boilerplate inside this file. -/
local notation "cF[" V "]" => SmoothVectorField.const (I := I) (M := M) V

/-! ## Math API -/

/-- $R(X, Y) Z = -R(Y, X) Z$.

Reference: do Carmo §4 Proposition 2.5 (i). -/
theorem riemannCurvature_antisymm
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    Riem(X, Y) Z x = -Riem(Y, X) Z x := by
  simp only [riem_simp]
  rw [covDeriv_mlieBracket_swap_apply]
  abel

/-- The endomorphism $z \mapsto R(z, X) Y(x)$ on $T_xM$ (with $z$ extended to
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
    -- Term 1: covDeriv (fun _ => z) F x = lev.toFun F x z is CLM-linear in z.
    have hT1 : covDeriv (fun _ : M => z₁ + z₂) (fun y => covDeriv X.toFun Y.toFun y) x
        = covDeriv (fun _ => z₁) (fun y => covDeriv X.toFun Y.toFun y) x
        + covDeriv (fun _ => z₂) (fun y => covDeriv X.toFun Y.toFun y) x := by
      show (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) (z₁ + z₂)
          = (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) z₁
          + (leviCivitaConnection.toFun (fun y => covDeriv X.toFun Y.toFun y) x) z₂
      exact map_add _ _ _
    -- Term 2: inner field `fun y => covDeriv (fun _ => z) Y y = lev.toFun Y y z`.
    -- CLM-linear in z, so the inner field is the pointwise sum.
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
      -- linear in the FIRST (direction) argument via CLM, since
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
    -- Term 1: CLM map_smul.
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

/-- The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at $x$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{curvatureEndo}\,X\,Y\,x).$$

Reference: do Carmo §4 ex. 1. -/
noncomputable def ricci
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (curvatureEndo X Y x)

/-- The Ricci curvature as a scalar function on the manifold:
`(Ric(X, Y))(x) = ricci X Y x`. -/
scoped[Riemannian] notation:max "Ric(" X ", " Y ")" => ricci X Y

/-! ### Heart of Bochner: `g(R(X,Y)Z, Z) = 0`

do Carmo §4 Proposition 2.5(iii) closure. The proof reduces, via metric
compatibility applied diagonally at every $y$, to the half-derivative
identity $D_V (g(Z, Z))(y) = 2\,g(\nabla_V Z, Z)(y)$. Differentiating
again at $x$ and using metric-compat once more expresses each
$g(\nabla_W \nabla_V Z, Z)$ in terms of iterated directional derivatives
of $f := g(Z, Z)$; the Hessian–Lie identity
(`mfderiv_iterate_sub_eq_mlieBracket_apply`) collapses
$X(Y(f)) - Y(X(f)) - [X,Y](f) = 0$, closing the chain. -/

/-- **Diagonal metric-compat identity**: at every point $y \in M$ with
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
  have h := leviCivitaConnection_metric_compatible V Z.toFun Z.toFun y
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

/-- Function-equality form: at every $y$, the directional derivative of
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

/-- **Iterated metric-compat identity at $x$**: differentiating the
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
  have h_compat := leviCivitaConnection_metric_compatible
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
  -- Avoid CLM-smul issues by writing `2 * h = h + h` and using `mfderiv_add`.
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
  -- Compute the CLM add via `mfderiv_add` then evaluate at `W.toFun x`.
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
  -- Apply both sides to (W.toFun x) and use CLM-add evaluation.
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

/-- $\langle R(X, Y) Z, Z \rangle_g(x) = 0$ for smooth vector fields
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

/-- **Additivity of `riemannCurvature` in the differentiated (3rd) slot**:
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

/-- **Metric-skew of the Riemann curvature in the (3rd, 4th) slot**:
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

/-- **No-bracket form of `riemannCurvature` for constant directions**. -/
theorem riemannCurvature_const_const_eq_iterate
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
  -- CLM linearity gives zero.
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

/-- **Constant-direction Bianchi swap**. Bianchi I on $(\mathrm{const}\,v, X, Y)$
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
  -- Pointwise smoothness witnesses for V, X, Y.
  have hV_smooth : ∀ y, TangentSmoothAt (fun _ : M => v) y := V.smoothAt
  have hX_smooth : ∀ y, TangentSmoothAt X.toFun y := X.smoothAt
  have hY_smooth : ∀ y, TangentSmoothAt Y.toFun y := Y.smoothAt
  -- First-derivative sections smooth.
  have h_dVY : ∀ y, TangentSmoothAt
      (fun y' => covDeriv (fun _ : M => v) Y.toFun y') y :=
    fun y => covDeriv_const_smoothVF_smoothAt v Y y
  have h_dXV : ∀ y, TangentSmoothAt
      (fun y' => covDeriv X.toFun (fun _ : M => v) y') y :=
    fun y => covDeriv_smoothVF_smoothAt X V y
  have h_dYX : ∀ y, TangentSmoothAt
      (fun y' => covDeriv Y.toFun X.toFun y') y :=
    fun y => covDeriv_smoothVF_smoothAt Y X y
  -- Lie-bracket sections smooth.
  have h_VX_br : ∀ y, TangentSmoothAt
      (fun y' => mlieBracket I (fun _ : M => v) X.toFun y') y :=
    fun y => mlieBracket_tangentSmoothAt V.smooth X.smooth
  have h_XV_br : ∀ y, TangentSmoothAt
      (fun y' => mlieBracket I X.toFun (fun _ : M => v) y') y :=
    fun y => mlieBracket_tangentSmoothAt X.smooth V.smooth
  have h_XY_br : ∀ y, TangentSmoothAt
      (fun y' => mlieBracket I X.toFun Y.toFun y') y :=
    fun y => mlieBracket_tangentSmoothAt X.smooth Y.smooth
  have h_YV_br : ∀ y, TangentSmoothAt
      (fun y' => mlieBracket I Y.toFun (fun _ : M => v) y') y :=
    fun y => mlieBracket_tangentSmoothAt Y.smooth V.smooth
  have h_VY_br : ∀ y, TangentSmoothAt
      (fun y' => mlieBracket I (fun _ : M => v) Y.toFun y') y :=
    fun y => mlieBracket_tangentSmoothAt V.smooth Y.smooth
  -- Jacobi identity at x from Mathlib (`leibniz_identity_mlieBracket_apply`).
  -- Smoothness witnesses at level `minSmoothness ℝ 2`, downgraded from ∞.
  have hV_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, (fun _ : M => v) y⟩ : TangentBundle I M)) x := by
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
  -- `leibniz_identity_mlieBracket_apply` needs `IsManifold I (minSmoothness ℝ 3) M`;
  -- provide it from `IsManifold I ∞ M` (`LEInfty` cascade on `ℕ∞ω`).
  haveI hM3 : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have h_jac := VectorField.leibniz_identity_mlieBracket_apply
    (I := I) (M := M) (U := fun _ : M => v) (V := X.toFun) (W := Y.toFun)
    hV_2 hX_2 hY_2
  -- Bianchi I with (X', Y', Z') = (const v, X.toFun, Y.toFun).
  have h_bianchi := bianchi_first (fun _ : M => v) X.toFun Y.toFun x
    hV_smooth hX_smooth hY_smooth
    h_dVY h_dXV h_dYX
    h_VX_br h_XV_br h_XY_br h_YV_br h_VY_br
    h_jac
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

/-- $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

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

/-- The **Ricci tensor** at $x$ as a bilinear form $T_xM \times T_xM \to \mathbb{R}$,
$(V, W) \mapsto \mathrm{Ric}(V, W)(x)$ with $V, W$ extended to constant sections.
Bundled as a `LinearMap → LinearMap → ℝ` for downstream metric raising. -/
noncomputable def ricciTensor (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ where
  toFun V :=
    { toFun := fun W =>
        ricci (cF[V])
              (cF[W]) x
      map_add' := fun W₁ W₂ => by
        -- Route via `curvatureEndo` LinearMap-additivity, then trace.
        show ricci (cF[V])
              (cF[W₁ + W₂]) x
            = ricci (cF[V])
                (cF[W₁]) x
              + ricci (cF[V])
                (cF[W₂]) x
        unfold ricci
        rw [show curvatureEndo (cF[V])
                  (cF[W₁ + W₂]) x
              = curvatureEndo (cF[V])
                  (cF[W₁]) x
                + curvatureEndo (cF[V])
                  (cF[W₂]) x from ?_]
        · exact (LinearMap.trace ℝ _).map_add _ _
        -- Pointwise LinearMap equality.
        refine LinearMap.ext fun z => ?_
        show riemannCurvature (fun _ => z)
              (cF[V]).toFun
              (cF[W₁ + W₂]).toFun x
            = riemannCurvature (fun _ => z)
                (cF[V]).toFun
                (cF[W₁]).toFun x
              + riemannCurvature (fun _ => z)
                (cF[V]).toFun
                (cF[W₂]).toFun x
        -- Π-equality: const(W₁+W₂) = const W₁ + const W₂.
        have h_const_add : ((fun _ : M => W₁ + W₂) : (y : M) → TangentSpace I y)
            = (fun _ => W₁) + (fun _ => W₂) := by funext y; rfl
        have h_const_W₁_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => W₁) y :=
          fun y => (cF[W₁]).smoothAt y
        have h_const_W₂_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => W₂) y :=
          fun y => (cF[W₂]).smoothAt y
        have h_const_z_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => z) y :=
          fun y => (cF[z]).smoothAt y
        have h_const_V_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => V) y :=
          fun y => (cF[V]).smoothAt y
        show covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V)
                  (fun _ : M => W₁ + W₂) y) x
              - covDeriv (fun _ : M => V) (fun y => covDeriv (fun _ => z)
                  (fun _ : M => W₁ + W₂) y) x
              - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                  (fun _ : M => W₁ + W₂) x
            = (covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V)
                    (fun _ : M => W₁) y) x
                - covDeriv (fun _ : M => V) (fun y => covDeriv (fun _ => z)
                    (fun _ : M => W₁) y) x
                - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                    (fun _ : M => W₁) x)
              + (covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V)
                    (fun _ : M => W₂) y) x
                - covDeriv (fun _ : M => V) (fun y => covDeriv (fun _ => z)
                    (fun _ : M => W₂) y) x
                - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                    (fun _ : M => W₂) x)
        -- Π-equality for the sum-of-constant-sections form.
        have h_const_W_sum : ((fun _ : M => W₁ + W₂) : (y : M) → TangentSpace I y)
            = (fun _ => W₁) + (fun _ => W₂) := by funext y; rfl
        -- Term1 inner: rewrite W₁+W₂ as Π-sum, apply covDeriv_add_field.
        have h_inner_T1 :
            ((fun y => covDeriv (fun _ : M => V) (fun _ : M => W₁ + W₂) y) :
              (y : M) → TangentSpace I y)
            = (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₁) y)
              + (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₂) y) := by
          funext y
          rw [show ((fun _ : M => W₁ + W₂) : (z : M) → TangentSpace I z)
                = (fun _ => W₁) + (fun _ => W₂) from h_const_W_sum]
          exact covDeriv_add_field (fun _ => V) (fun _ => W₁) (fun _ => W₂) y
            (h_const_W₁_smooth y) (h_const_W₂_smooth y)
        rw [h_inner_T1]
        have h_inner_T2 :
            ((fun y => covDeriv (fun _ : M => z) (fun _ : M => W₁ + W₂) y) :
              (y : M) → TangentSpace I y)
            = (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₁) y)
              + (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₂) y) := by
          funext y
          rw [show ((fun _ : M => W₁ + W₂) : (z : M) → TangentSpace I z)
                = (fun _ => W₁) + (fun _ => W₂) from h_const_W_sum]
          exact covDeriv_add_field (fun _ => z) (fun _ => W₁) (fun _ => W₂) y
            (h_const_W₁_smooth y) (h_const_W₂_smooth y)
        rw [h_inner_T2]
        -- Term3: convert `(fun _ => W₁+W₂)` to Π-add, then split.
        have hT3 : covDeriv
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W₁ + W₂) x
            = covDeriv
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W₁) x
            + covDeriv
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W₂) x := by
          rw [show ((fun _ : M => W₁ + W₂) : (z : M) → TangentSpace I z)
                = (fun _ => W₁) + (fun _ => W₂) from h_const_W_sum]
          exact covDeriv_add_field
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ => W₁) (fun _ => W₂) x
              (h_const_W₁_smooth x) (h_const_W₂_smooth x)
        rw [hT3]
        -- Outer T1: direction `(fun _ => z)` via covDeriv_add_field on the
        -- differentiated section sum.
        have hT1 :
            covDeriv (fun _ : M => z)
              (((fun y => covDeriv (fun _ : M => V) (fun _ : M => W₁) y) :
                  (y : M) → TangentSpace I y)
                + (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₂) y)) x
            = covDeriv (fun _ : M => z)
                (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₁) y) x
              + covDeriv (fun _ : M => z)
                (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₂) y) x :=
          covDeriv_add_field (fun _ => z)
            (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₁) y)
            (fun y => covDeriv (fun _ : M => V) (fun _ : M => W₂) y) x
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V
              (cF[W₁]) x)
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V
              (cF[W₂]) x)
        rw [hT1]
        -- Outer T2: direction `(fun _ => V)` of inner T2 sum.
        have hT2 :
            covDeriv (fun _ : M => V)
              (((fun y => covDeriv (fun _ : M => z) (fun _ : M => W₁) y) :
                  (y : M) → TangentSpace I y)
                + (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₂) y)) x
            = covDeriv (fun _ : M => V)
                (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₁) y) x
              + covDeriv (fun _ : M => V)
                (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₂) y) x :=
          covDeriv_add_field (fun _ => V)
            (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₁) y)
            (fun y => covDeriv (fun _ : M => z) (fun _ : M => W₂) y) x
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z
              (cF[W₁]) x)
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z
              (cF[W₂]) x)
        rw [hT2]
        abel
      map_smul' := fun c W => by
        show ricci (cF[V])
              (cF[c • W]) x
            = (RingHom.id ℝ) c • ricci
                (cF[V])
                (cF[W]) x
        unfold ricci
        rw [show curvatureEndo (cF[V])
                  (cF[c • W]) x
              = c • curvatureEndo (cF[V])
                  (cF[W]) x from ?_]
        · simp
        refine LinearMap.ext fun z => ?_
        show riemannCurvature (fun _ => z)
              (cF[V]).toFun
              (cF[c • W]).toFun x
            = c • riemannCurvature (fun _ => z)
                (cF[V]).toFun
                (cF[W]).toFun x
        have h_const_smul : ((fun _ : M => c • W) : (y : M) → TangentSpace I y)
            = c • (fun _ => W) := by funext y; rfl
        have h_const_W_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => W) y :=
          fun y => (cF[W]).smoothAt y
        show covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V)
                  (fun _ : M => c • W) y) x
              - covDeriv (fun _ : M => V) (fun y => covDeriv (fun _ => z)
                  (fun _ : M => c • W) y) x
              - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                  (fun _ : M => c • W) x
            = c • (covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V)
                    (fun _ : M => W) y) x
                - covDeriv (fun _ : M => V) (fun y => covDeriv (fun _ => z)
                    (fun _ : M => W) y) x
                - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                    (fun _ : M => W) x)
        -- Term 1 inner.
        have h_inner_T1 :
            ((fun y => covDeriv (fun _ : M => V) (fun _ : M => c • W) y) :
              (y : M) → TangentSpace I y)
            = c • (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y) := by
          funext y
          rw [show ((fun _ : M => c • W) : (z : M) → TangentSpace I z)
                = c • (fun _ => W) from h_const_smul]
          exact covDeriv_smul_const_field (fun _ => V) (fun _ => W) y c
            (h_const_W_smooth y)
        rw [h_inner_T1]
        have h_inner_T2 :
            ((fun y => covDeriv (fun _ : M => z) (fun _ : M => c • W) y) :
              (y : M) → TangentSpace I y)
            = c • (fun y => covDeriv (fun _ : M => z) (fun _ : M => W) y) := by
          funext y
          rw [show ((fun _ : M => c • W) : (z : M) → TangentSpace I z)
                = c • (fun _ => W) from h_const_smul]
          exact covDeriv_smul_const_field (fun _ => z) (fun _ => W) y c
            (h_const_W_smooth y)
        rw [h_inner_T2]
        -- Term 3: covDeriv (...) (c • const W) x = c • covDeriv (...) (const W) x.
        have hT3 : covDeriv
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => c • W) x
            = c • covDeriv
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W) x := by
          rw [show ((fun _ : M => c • W) : (z : M) → TangentSpace I z)
                = c • (fun _ => W) from h_const_smul]
          exact covDeriv_smul_const_field
            (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
            (fun _ => W) x c (h_const_W_smooth x)
        rw [hT3]
        -- Outer T1: direction `(fun _ => z)`, differentiated `c • F`.
        have hT1 :
            covDeriv (fun _ : M => z)
              ((c • (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y)) :
                  (y : M) → TangentSpace I y) x
            = c • covDeriv (fun _ : M => z)
                (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y) x :=
          covDeriv_smul_const_field (fun _ => z)
            (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y) x c
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V
              (cF[W]) x)
        rw [hT1]
        have hT2 :
            covDeriv (fun _ : M => V)
              ((c • (fun y => covDeriv (fun _ : M => z) (fun _ : M => W) y)) :
                  (y : M) → TangentSpace I y) x
            = c • covDeriv (fun _ : M => V)
                (fun y => covDeriv (fun _ : M => z) (fun _ : M => W) y) x :=
          covDeriv_smul_const_field (fun _ => V)
            (fun y => covDeriv (fun _ : M => z) (fun _ : M => W) y) x c
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z
              (cF[W]) x)
        rw [hT2]
        rw [smul_sub, smul_sub] }
  map_add' V₁ V₂ := by
    -- LinearMap-level additivity in V slot.
    refine LinearMap.ext fun W => ?_
    show ricci (cF[V₁ + V₂])
            (cF[W]) x
        = ricci (cF[V₁])
            (cF[W]) x
          + ricci (cF[V₂])
            (cF[W]) x
    unfold ricci
    rw [show curvatureEndo (cF[V₁ + V₂])
              (cF[W]) x
          = curvatureEndo (cF[V₁])
              (cF[W]) x
            + curvatureEndo (cF[V₂])
              (cF[W]) x from ?_]
    · exact (LinearMap.trace ℝ _).map_add _ _
    refine LinearMap.ext fun z => ?_
    show riemannCurvature (fun _ => z)
          (cF[V₁ + V₂]).toFun
          (cF[W]).toFun x
        = riemannCurvature (fun _ => z)
            (cF[V₁]).toFun
            (cF[W]).toFun x
          + riemannCurvature (fun _ => z)
            (cF[V₂]).toFun
            (cF[W]).toFun x
    have h_const_add : ((fun _ : M => V₁ + V₂) : (y : M) → TangentSpace I y)
        = (fun _ => V₁) + (fun _ => V₂) := by funext y; rfl
    have h_const_V₁_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => V₁) y :=
      fun y => (cF[V₁]).smoothAt y
    have h_const_V₂_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => V₂) y :=
      fun y => (cF[V₂]).smoothAt y
    show covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V₁ + V₂)
              (fun _ : M => W) y) x
          - covDeriv (fun _ : M => V₁ + V₂)
              (fun y => covDeriv (fun _ => z) (fun _ : M => W) y) x
          - covDeriv (fun y => mlieBracket I (fun _ => z)
              (fun _ : M => V₁ + V₂) y) (fun _ : M => W) x
        = (covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V₁)
                (fun _ : M => W) y) x
            - covDeriv (fun _ : M => V₁) (fun y => covDeriv (fun _ => z)
                (fun _ : M => W) y) x
            - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₁) y)
                (fun _ : M => W) x)
          + (covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V₂)
                (fun _ : M => W) y) x
            - covDeriv (fun _ : M => V₂) (fun y => covDeriv (fun _ => z)
                (fun _ : M => W) y) x
            - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₂) y)
                (fun _ : M => W) x)
    -- Term 1 inner: direction-CLM-linearity of covDeriv.
    have h_inner_T1 :
        ((fun y => covDeriv (fun _ : M => V₁ + V₂) (fun _ : M => W) y) :
          (y : M) → TangentSpace I y)
        = (fun y => covDeriv (fun _ : M => V₁) (fun _ : M => W) y)
          + (fun y => covDeriv (fun _ : M => V₂) (fun _ : M => W) y) := by
      funext y
      show (leviCivitaConnection.toFun (fun _ : M => W) y) (V₁ + V₂)
          = (leviCivitaConnection.toFun (fun _ : M => W) y) V₁
            + (leviCivitaConnection.toFun (fun _ : M => W) y) V₂
      exact map_add _ _ _
    rw [h_inner_T1]
    -- Term 2: outer covDeriv direction (V₁+V₂) at section-level via CLM.
    -- Stash the differentiated section so its type is fully determined.
    set Fz : (y : M) → TangentSpace I y :=
      fun y => covDeriv (fun _ : M => z) (fun _ : M => W) y with hFz
    have hT2 : covDeriv (fun _ : M => V₁ + V₂) Fz x
        = covDeriv (fun _ : M => V₁) Fz x + covDeriv (fun _ : M => V₂) Fz x := by
      show (leviCivitaConnection.toFun Fz x) (V₁ + V₂)
          = (leviCivitaConnection.toFun Fz x) V₁
            + (leviCivitaConnection.toFun Fz x) V₂
      exact map_add _ _ _
    rw [hT2]
    -- Term 3: mlieBracket additivity in right argument.
    have h_lieBr_add :
        ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₁ + V₂) y) :
          (y : M) → TangentSpace I y)
        = (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₁) y)
          + (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₂) y) := by
      funext y
      rw [show ((fun _ : M => V₁ + V₂) : (z : M) → TangentSpace I z)
            = (fun _ => V₁) + (fun _ => V₂) from h_const_add]
      exact VectorField.mlieBracket_add_right (h_const_V₁_smooth y) (h_const_V₂_smooth y)
    rw [h_lieBr_add]
    -- Outer covDeriv on T3: direction is the sum, differentiated is `const W`.
    have hT3 : covDeriv ((fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₁) y)
            + (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₂) y))
              (fun _ : M => W) x
        = covDeriv (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₁) y) (fun _ : M => W) x
          + covDeriv (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₂) y) (fun _ : M => W) x := by
      show (leviCivitaConnection.toFun (fun _ : M => W) x)
            ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₁) y) x
              + (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₂) y) x)
          = (leviCivitaConnection.toFun (fun _ : M => W) x)
              ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₁) y) x)
            + (leviCivitaConnection.toFun (fun _ : M => W) x)
              ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₂) y) x)
      exact map_add _ _ _
    -- Outer covDeriv on T1: direction `(fun _ => z)`, differentiated sum.
    have hT1 :
        covDeriv (fun _ : M => z)
            (((fun y => covDeriv (fun _ : M => V₁) (fun _ : M => W) y) :
                (y : M) → TangentSpace I y)
              + (fun y => covDeriv (fun _ : M => V₂) (fun _ : M => W) y)) x
        = covDeriv (fun _ : M => z)
              (fun y => covDeriv (fun _ : M => V₁) (fun _ : M => W) y) x
          + covDeriv (fun _ : M => z)
              (fun y => covDeriv (fun _ : M => V₂) (fun _ : M => W) y) x :=
      covDeriv_add_field (fun _ => z)
        (fun y => covDeriv (fun _ : M => V₁) (fun _ : M => W) y)
        (fun y => covDeriv (fun _ : M => V₂) (fun _ : M => W) y) x
        (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V₁
          (cF[W]) x)
        (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V₂
          (cF[W]) x)
    rw [hT1, hT3]
    abel
  map_smul' c V := by
    refine LinearMap.ext fun W => ?_
    show ricci (cF[c • V])
            (cF[W]) x
        = ((RingHom.id ℝ) c • ricci (cF[V])
            (cF[W]) x : ℝ)
    unfold ricci
    rw [show curvatureEndo (cF[c • V])
              (cF[W]) x
          = c • curvatureEndo (cF[V])
              (cF[W]) x from ?_]
    · simp
    refine LinearMap.ext fun z => ?_
    show riemannCurvature (fun _ => z)
          (cF[c • V]).toFun
          (cF[W]).toFun x
        = c • riemannCurvature (fun _ => z)
            (cF[V]).toFun
            (cF[W]).toFun x
    have h_const_smul : ((fun _ : M => c • V) : (y : M) → TangentSpace I y)
        = c • (fun _ => V) := by funext y; rfl
    have h_const_V_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => V) y :=
      fun y => (cF[V]).smoothAt y
    show covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => c • V)
              (fun _ : M => W) y) x
          - covDeriv (fun _ : M => c • V)
              (fun y => covDeriv (fun _ => z) (fun _ : M => W) y) x
          - covDeriv (fun y => mlieBracket I (fun _ => z)
              (fun _ : M => c • V) y) (fun _ : M => W) x
        = c • (covDeriv (fun _ => z) (fun y => covDeriv (fun _ : M => V)
                (fun _ : M => W) y) x
            - covDeriv (fun _ : M => V) (fun y => covDeriv (fun _ => z)
                (fun _ : M => W) y) x
            - covDeriv (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                (fun _ : M => W) x)
    -- Term 1 inner.
    have h_inner_T1 :
        ((fun y => covDeriv (fun _ : M => c • V) (fun _ : M => W) y) :
          (y : M) → TangentSpace I y)
        = c • (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y) := by
      funext y
      show (leviCivitaConnection.toFun (fun _ : M => W) y) (c • V)
          = c • (leviCivitaConnection.toFun (fun _ : M => W) y) V
      exact ContinuousLinearMap.map_smul _ _ _
    rw [h_inner_T1]
    -- Term 2: outer covDeriv direction is c • V at section level.
    set Fz : (y : M) → TangentSpace I y :=
      fun y => covDeriv (fun _ : M => z) (fun _ : M => W) y with hFz
    have hT2 : covDeriv (fun _ : M => c • V) Fz x
        = c • covDeriv (fun _ : M => V) Fz x := by
      show (leviCivitaConnection.toFun Fz x) (c • V)
          = c • (leviCivitaConnection.toFun Fz x) V
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT2]
    -- Term 3: mlieBracket scalar in right arg.
    have h_lieBr_smul :
        ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => c • V) y) :
          (y : M) → TangentSpace I y)
        = c • (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y) := by
      funext y
      rw [show ((fun _ : M => c • V) : (z : M) → TangentSpace I z)
            = c • (fun _ => V) from h_const_smul]
      exact VectorField.mlieBracket_const_smul_right (h_const_V_smooth y)
    rw [h_lieBr_smul]
    have hT3 : covDeriv (c • (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V) y)) (fun _ : M => W) x
        = c • covDeriv (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V) y) (fun _ : M => W) x := by
      show (leviCivitaConnection.toFun (fun _ : M => W) x)
            ((c • fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y) x)
          = c • (leviCivitaConnection.toFun (fun _ : M => W) x)
              ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y) x)
      show (leviCivitaConnection.toFun (fun _ : M => W) x)
            (c • mlieBracket I (fun _ : M => z) (fun _ : M => V) x)
          = c • (leviCivitaConnection.toFun (fun _ : M => W) x)
              (mlieBracket I (fun _ : M => z) (fun _ : M => V) x)
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT3]
    -- Outer T1: direction `(fun _ => z)`, differentiated `c • F`.
    have hT1 :
        covDeriv (fun _ : M => z)
            ((c • (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y)) :
                (y : M) → TangentSpace I y) x
        = c • covDeriv (fun _ : M => z)
              (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y) x :=
      covDeriv_smul_const_field (fun _ => z)
        (fun y => covDeriv (fun _ : M => V) (fun _ : M => W) y) x c
        (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V
          (cF[W]) x)
    rw [hT1]
    rw [smul_sub, smul_sub]

/-- The **Ricci endomorphism** $\mathrm{Ric}^{\sharp}_x : T_xM \to T_xM$ defined
by metric raising of the Ricci tensor:
$\langle \mathrm{Ric}^{\sharp}_x V, W \rangle_g = \mathrm{Ric}(V, W)(x)$. -/
noncomputable def ricciSharp (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun V :=
    (metricToDualEquiv x).symm (ricciTensor (I := I) (M := M) x V).toContinuousLinearMap
  map_add' V₁ V₂ := by
    show (metricToDualEquiv x).symm ((ricciTensor x (V₁ + V₂)).toContinuousLinearMap)
        = (metricToDualEquiv x).symm ((ricciTensor x V₁).toContinuousLinearMap)
        + (metricToDualEquiv x).symm ((ricciTensor x V₂).toContinuousLinearMap)
    rw [show ricciTensor (I := I) (M := M) x (V₁ + V₂)
          = ricciTensor x V₁ + ricciTensor x V₂ from
        (ricciTensor (I := I) (M := M) x).map_add V₁ V₂]
    show (metricToDualEquiv x).symm
          ((ricciTensor x V₁ + ricciTensor x V₂).toContinuousLinearMap)
        = (metricToDualEquiv x).symm ((ricciTensor x V₁).toContinuousLinearMap)
        + (metricToDualEquiv x).symm ((ricciTensor x V₂).toContinuousLinearMap)
    rw [show (ricciTensor (I := I) (M := M) x V₁
                + ricciTensor x V₂).toContinuousLinearMap
          = (ricciTensor x V₁).toContinuousLinearMap
            + (ricciTensor x V₂).toContinuousLinearMap from
        LinearMap.toContinuousLinearMap.map_add _ _]
    exact (metricToDualEquiv x).symm.map_add _ _
  map_smul' c V := by
    show (metricToDualEquiv x).symm ((ricciTensor x (c • V)).toContinuousLinearMap)
        = c • (metricToDualEquiv x).symm ((ricciTensor x V).toContinuousLinearMap)
    rw [show ricciTensor (I := I) (M := M) x (c • V)
          = c • ricciTensor x V from
        (ricciTensor (I := I) (M := M) x).map_smul c V]
    show (metricToDualEquiv x).symm ((c • ricciTensor x V).toContinuousLinearMap)
        = c • (metricToDualEquiv x).symm ((ricciTensor x V).toContinuousLinearMap)
    rw [show (c • ricciTensor (I := I) (M := M) x V).toContinuousLinearMap
          = c • (ricciTensor x V).toContinuousLinearMap from
        LinearMap.toContinuousLinearMap.map_smul _ _]
    exact (metricToDualEquiv x).symm.map_smul c _

/-- The **scalar curvature** $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x)
= \mathrm{tr}(\mathrm{Ric}^{\sharp}_x)$.

Basis-free definition: trace of the Ricci endomorphism. Equals $\sum_i \mathrm{Ric}(e_i, e_i)$
for any $g$-orthonormal basis $\{e_i\}$ of $T_xM$. -/
noncomputable def scalarCurvature (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (ricciSharp (I := I) (M := M) x)

/-- The scalar curvature `scal_g[I]`. `I` is bracketed because
`x : M` does not expose the model with corners. -/
scoped[Riemannian] notation:max "scal_g[" I "]" => scalarCurvature (I := I)

/-- Pointwise Ricci tensor on tangent vectors: `Ric_g(v, w) x = ricciTensor x v w`. -/
scoped[Riemannian] notation:max "Ric_g(" v ", " w ") " x:max => ricciTensor x v w

end Riemannian

