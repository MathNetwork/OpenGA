import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Riemannian.HessianLie
-- `Riem(X, Y) Z` notation is now defined inline in `Connection.lean`
-- alongside `riemannCurvature`; it transitively reaches us via the
-- `import OpenGALib.Riemannian.Connection` above.
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

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
* `riemannCurvature_inner_self_zero` (sorry, PRE-PAPER) — $\langle R(X, Y) Z, Z \rangle_g = 0$.
* `ricci_symm` (sorry, PRE-PAPER) — $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

Reference: do Carmo 1992 §4.
-/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian

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

/-- $\langle R(X, Y) Z, Z \rangle_g(x) = 0$.

Reference: do Carmo §4 Proposition 2.5 (iii).

**Sorry: PRE-PAPER**. Closure path: expand `riemannCurvature` to its
$\nabla\nabla - \nabla\nabla - \nabla_{[\cdot,\cdot]}$ form, apply
metric-compatibility four times to reduce each $\langle \nabla_\cdot \nabla_\cdot Z, Z\rangle$
to $\tfrac12 X(Y(f))$ where $f := \langle Z, Z\rangle$, and collapse via the
manifold scalar Hessian-Lie identity (`mfderiv_iterate_sub_eq_mlieBracket_apply`). -/
theorem riemannCurvature_inner_self_zero
    [IsManifold I 2 M]
    (X Y Z : SmoothVectorField I M) (x : M) :
    metricInner x (Riem(X.toFun, Y.toFun) Z.toFun x) (Z x) = 0 := by
  sorry

/-- $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

Reference: do Carmo §4 ex. 1.

**Sorry: PRE-PAPER**. Closure path: trace-via-orthonormal-basis + Bianchi I +
first-arg antisymmetry of $R$ + diagonal-zero (`riemannCurvature_inner_self_zero`).
For each $e_i$ in an orthonormal basis, Bianchi I on $(\mathrm{const}\,e_i, X, Y)$
gives $\langle R(e_i, X) Y, e_i\rangle - \langle R(e_i, Y) X, e_i\rangle = -\langle R(X, Y) e_i, e_i\rangle$;
summing produces $\mathrm{Ric}(X, Y) - \mathrm{Ric}(Y, X) = -\mathrm{tr}(R(X, Y)) = 0$. -/
theorem ricci_symm
    [IsManifold I 2 M]
    (X Y : SmoothVectorField I M) (x : M) :
    Ric(X, Y) x = Ric(Y, X) x := by
  sorry

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

