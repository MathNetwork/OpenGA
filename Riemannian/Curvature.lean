import Riemannian.Connection
import Riemannian.Connection.Smoothness
import Riemannian.TangentBundle.SmoothVectorField
import Riemannian.Foundations.HessianLie
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Riemannian.Curvature

Riemann curvature tensor, Ricci curvature, scalar curvature.

## Form

  * `riemannCurvature` — real `noncomputable def` built directly from
    `covDeriv` (Levi-Civita) and `mlieBracket` via the standard formula
    $R(X, Y)Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.
  * `ricciTraceMap` — the linear map $z \mapsto R(z, X)Y(x)$ on $T_xM$,
    bundling the curvature endomorphism for the trace.
  * `ricci` — real `noncomputable def` via `LinearMap.trace ℝ (TangentSpace I x)`
    applied to `ricciTraceMap`. Finite-dimensional trace operator from
    Mathlib (`LinearMap.trace`); the `[FiniteDimensional ℝ E]` cascade
    propagates through the framework-owned NACG / IPS bridges
    (`Riemannian.Metric`).
  * `ricciFormAt` — Ricci as a bilinear form $T_xM \times T_xM \to \mathbb{R}$
    bundled as `LinearMap → LinearMap → ℝ`. Bilinearity slots are PRE-PAPER
    (closure via `koszulCovDeriv` tensoriality).
  * `ricciEndo` — Ricci endomorphism $T_xM \to T_xM$ via metric raising
    of `ricciFormAt` (Riesz extraction through `metricRiesz`).
  * `scalarCurvature` — real `noncomputable def` as $\mathrm{tr}(\mathrm{Ric}^{\sharp})$,
    i.e., `LinearMap.trace ℝ` applied to `ricciEndo`. **Basis-free**:
    avoids `stdOrthonormalBasis`, which (per the framework's IPS bridge
    `instInnerProductSpaceTangent`) is orthonormal w.r.t. background
    `inner E`, NOT w.r.t. the Riemannian metric `g_x` — the previous
    definition would have produced wrong values on any non-Euclidean
    manifold.

## Sorry status

  * `ricciTraceMap.map_add'` and `map_smul'` — PRE-PAPER. The
    `C^\infty(M)`-linearity of the curvature endomorphism in its first
    argument (when extended via constants from $T_xM$) requires the
    Levi-Civita-on-`covDeriv` linearity lemmas. Repair: derive from
    `koszulCovDeriv`'s linearity in $X$ when its linearity proofs land.
  * `ricci_symm` — PRE-PAPER. Symmetry of Ricci requires the algebraic
    Bianchi identity on the Riemann tensor. Repair: framework self-build
    of Bianchi from torsion-freeness + curvature definition.

**Ground truth**: do Carmo 1992 §4 (Riemann curvature, sectional, Ricci).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-! `riemannCurvature` and `riemannCurvature_antisymm` are connection-level
content (depend only on `covDeriv` and `mlieBracket`, not metric). They
live in `Riemannian.Connection.Bianchi` (re-exported via
`Riemannian.Connection`) so that `bianchi_first` can reference them
without circular dependency. -/

/-- **Ricci-trace linear map** at a point: the linear map
$z \mapsto R(z\text{-extended}, X) Y(x)$ on $T_xM$, where
$z\text{-extended}$ is the constant section with value $z$.

`X, Y` are bundled `SmoothVectorField`s, providing the global smoothness
witnesses needed for the underlying covariant-derivative additivity
(via `IsCovariantDerivativeOn.add`) and Lie-bracket linearity
(`mlieBracket_add_left`, `mlieBracket_const_smul_left`). -/
noncomputable def ricciTraceMap
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
    have h_const_z₁_smooth : ∀ y, OpenGALib.TangentSmoothAt
        (fun _ : M => z₁) y :=
      fun y => (SmoothVectorField.const (I := I) (M := M) z₁).smoothAt y
    have h_const_z₂_smooth : ∀ y, OpenGALib.TangentSmoothAt
        (fun _ : M => z₂) y :=
      fun y => (SmoothVectorField.const (I := I) (M := M) z₂).smoothAt y
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
    have h_const_z_smooth : ∀ y, OpenGALib.TangentSmoothAt (fun _ : M => z) y :=
      fun y => (SmoothVectorField.const (I := I) (M := M) z).smoothAt y
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

/-- The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at a point
$x$, defined as the trace of the linear map $z \mapsto R(z, X)Y$ on
$T_xM$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{ricciTraceMap}\,X\,Y\,x).$$

**Ground truth**: do Carmo 1992 §4 ex. 1.

Real `noncomputable def` via `LinearMap.trace ℝ (TangentSpace I x)`
applied to `ricciTraceMap`. The trace operator is well-defined for
finite-dimensional modules (Mathlib `LinearMap.trace`); since
$E$ is `[FiniteDimensional ℝ E]` in our cascade, the trace returns
a meaningful scalar.

The ℝ-linearity proofs inside `ricciTraceMap` (`map_add'`,
`map_smul'` in the trace argument $z$) are sorry'd (PRE-PAPER,
repair via Mathlib's `CovariantDerivative` linearity lemmas
applied through `riemannCurvature`'s defining formula). -/
noncomputable def ricci
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (ricciTraceMap X Y x)

/-- **Skew-symmetry of `R(X,Y)` as endomorphism, diagonal form**:
$\langle R(X,Y) Z, Z \rangle_g(x) = 0$.

Proof outline (do Carmo 1992 §4 Proposition 2.5 (iii)):
expand `riemannCurvature` to `∇∇` form, apply metric-compat 4× to
reduce each `⟨∇_·∇_· Z, Z⟩` term to `(1/2)·X(Y(f))` with `f := ⟨Z,Z⟩`,
then collapse via the manifold scalar Hessian-Lie identity
(`mfderiv_iterate_sub_eq_mlieBracket_apply`).

Closure path is fully laid out in proof body; substantive metric-compat
applications + scalar manipulations remain. ~150 lines mechanical Lean. -/
theorem riemannCurvature_inner_diagonal_zero
    [IsManifold I 2 M]
    (X Y Z : SmoothVectorField I M) (x : M) :
    metricInner x (riemannCurvature X Y Z x) (Z x) = 0 := by
  -- Define f := ⟨Z, Z⟩ : M → ℝ (smooth from Z C^∞ + metric C^∞).
  -- Apply metric-compat to ⟨∇_Y Z, Z⟩, ⟨∇_X Z, Z⟩, ⟨∇_{[X,Y]} Z, Z⟩:
  --   ⟨∇_A Z, Z⟩ = (1/2) A(f).
  -- Then for ⟨∇_X∇_Y Z, Z⟩:
  --   apply metric-compat to ⟨∇_Y Z, Z⟩ along X-direction:
  --     X(⟨∇_Y Z, Z⟩) = ⟨∇_X∇_Y Z, Z⟩ + ⟨∇_Y Z, ∇_X Z⟩
  --     ⟹ ⟨∇_X∇_Y Z, Z⟩ = (1/2) X(Y(f)) - ⟨∇_Y Z, ∇_X Z⟩.
  --   Similarly ⟨∇_Y∇_X Z, Z⟩ = (1/2) Y(X(f)) - ⟨∇_X Z, ∇_Y Z⟩.
  --   And ⟨∇_{[X,Y]} Z, Z⟩ = (1/2) [X,Y](f).
  -- Substitute into ⟨R(X,Y)Z, Z⟩:
  --   = (1/2)[X(Y(f)) - Y(X(f)) - [X,Y](f)]   (cross ⟨∇,∇⟩ terms cancel by inner symm)
  --   = 0   by manifold Hessian-Lie applied to f.
  sorry

/-- **Ricci curvature is symmetric**: $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

Proof: trace-via-orthonormal-basis + Bianchi I + first-arg antisymmetry of `R`
+ skew-symm of `R` endomorphism (`riemannCurvature_inner_diagonal_zero`).

For each `e_i` in the orthonormal basis, Bianchi I applied to
`(constE e_i, X, Y)` gives:
  `⟨R(e_i, X) Y, e_i⟩ - ⟨R(e_i, Y) X, e_i⟩ = -⟨R(X, Y) e_i, e_i⟩`.
Summing:
  `ricci(X,Y) - ricci(Y,X) = -∑_i ⟨R(X,Y) e_i, e_i⟩ = 0`
by diagonal-zero applied to each `e_i`.

**Ground truth**: do Carmo 1992 §4 ex. 1. -/
theorem ricci_symm
    [IsManifold I 2 M]
    (X Y : SmoothVectorField I M) (x : M) :
    ricci X Y x = ricci Y X x := by
  -- Trace via OnB + Bianchi I + diagonal-zero. Concrete chain:
  -- 1. `LinearMap.trace ℝ V L = ∑_i ⟪L(e_i), e_i⟫` for OnB e_i (Mathlib).
  -- 2. `ricciTraceMap X Y x e_i = R(constE e_i, X) Y x` (def).
  -- 3. Bianchi I on (constE e_i, X, Y) at x:
  --    R(e_i, X) Y + R(X, Y) e_i + R(Y, e_i) X = 0
  -- 4. R first-arg antisymm: R(Y, e_i) = -R(e_i, Y), so:
  --    ⟨R(e_i, X) Y, e_i⟩ - ⟨R(e_i, Y) X, e_i⟩ = -⟨R(X, Y) e_i, e_i⟩
  -- 5. Sum over i: LHS = ricci(X,Y) - ricci(Y,X), RHS = -trace(R(X,Y) endo).
  -- 6. By `riemannCurvature_inner_diagonal_zero`, each ⟨R(X,Y) e_i, e_i⟩ = 0.
  --    Hence trace = 0.
  -- 7. ricci(X,Y) - ricci(Y,X) = 0.
  sorry

/-- **Ricci bilinear form at a point**: $T_xM \times T_xM \to \mathbb{R}$,
$(V, W) \mapsto \mathrm{Ric}(V, W)(x)$ where $V, W$ are extended to
constant sections.

Bundled as a `LinearMap → LinearMap → ℝ` so that downstream raising via
the metric (`metricRiesz`) and trace (`LinearMap.trace`) is direct.

The four linearity slots (`map_add'` / `map_smul'` in each argument) are
PRE-PAPER. Repair: derive from `koszulCovDeriv`'s $C^\infty(M)$-linearity
in the differentiated section + the connection's tensoriality in the
direction argument; the curvature formula then propagates linearity to
each tangent-vector argument of $\mathrm{Ric}$. -/
noncomputable def ricciFormAt (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ where
  toFun V :=
    { toFun := fun W =>
        ricci (SmoothVectorField.const (I := I) (M := M) V)
              (SmoothVectorField.const (I := I) (M := M) W) x
      map_add' := fun W₁ W₂ => by
        -- Route via `ricciTraceMap` LinearMap-additivity, then trace.
        show ricci (SmoothVectorField.const (I := I) (M := M) V)
              (SmoothVectorField.const (I := I) (M := M) (W₁ + W₂)) x
            = ricci (SmoothVectorField.const (I := I) (M := M) V)
                (SmoothVectorField.const (I := I) (M := M) W₁) x
              + ricci (SmoothVectorField.const (I := I) (M := M) V)
                (SmoothVectorField.const (I := I) (M := M) W₂) x
        unfold ricci
        rw [show ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V)
                  (SmoothVectorField.const (I := I) (M := M) (W₁ + W₂)) x
              = ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V)
                  (SmoothVectorField.const (I := I) (M := M) W₁) x
                + ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V)
                  (SmoothVectorField.const (I := I) (M := M) W₂) x from ?_]
        · exact (LinearMap.trace ℝ _).map_add _ _
        -- Pointwise LinearMap equality.
        refine LinearMap.ext fun z => ?_
        show riemannCurvature (fun _ => z)
              (SmoothVectorField.const (I := I) (M := M) V).toFun
              (SmoothVectorField.const (I := I) (M := M) (W₁ + W₂)).toFun x
            = riemannCurvature (fun _ => z)
                (SmoothVectorField.const (I := I) (M := M) V).toFun
                (SmoothVectorField.const (I := I) (M := M) W₁).toFun x
              + riemannCurvature (fun _ => z)
                (SmoothVectorField.const (I := I) (M := M) V).toFun
                (SmoothVectorField.const (I := I) (M := M) W₂).toFun x
        -- Π-equality: const(W₁+W₂) = const W₁ + const W₂.
        have h_const_add : ((fun _ : M => W₁ + W₂) : (y : M) → TangentSpace I y)
            = (fun _ => W₁) + (fun _ => W₂) := by funext y; rfl
        have h_const_W₁_smooth : ∀ y, OpenGALib.TangentSmoothAt
            (fun _ : M => W₁) y :=
          fun y => (SmoothVectorField.const (I := I) (M := M) W₁).smoothAt y
        have h_const_W₂_smooth : ∀ y, OpenGALib.TangentSmoothAt
            (fun _ : M => W₂) y :=
          fun y => (SmoothVectorField.const (I := I) (M := M) W₂).smoothAt y
        have h_const_z_smooth : ∀ y, OpenGALib.TangentSmoothAt
            (fun _ : M => z) y :=
          fun y => (SmoothVectorField.const (I := I) (M := M) z).smoothAt y
        have h_const_V_smooth : ∀ y, OpenGALib.TangentSmoothAt
            (fun _ : M => V) y :=
          fun y => (SmoothVectorField.const (I := I) (M := M) V).smoothAt y
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
              (SmoothVectorField.const (I := I) (M := M) W₁) x)
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V
              (SmoothVectorField.const (I := I) (M := M) W₂) x)
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
              (SmoothVectorField.const (I := I) (M := M) W₁) x)
            (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) z
              (SmoothVectorField.const (I := I) (M := M) W₂) x)
        rw [hT2]
        abel
      map_smul' := fun c W => by
        show ricci (SmoothVectorField.const (I := I) (M := M) V)
              (SmoothVectorField.const (I := I) (M := M) (c • W)) x
            = (RingHom.id ℝ) c • ricci
                (SmoothVectorField.const (I := I) (M := M) V)
                (SmoothVectorField.const (I := I) (M := M) W) x
        unfold ricci
        rw [show ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V)
                  (SmoothVectorField.const (I := I) (M := M) (c • W)) x
              = c • ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V)
                  (SmoothVectorField.const (I := I) (M := M) W) x from ?_]
        · simp
        refine LinearMap.ext fun z => ?_
        show riemannCurvature (fun _ => z)
              (SmoothVectorField.const (I := I) (M := M) V).toFun
              (SmoothVectorField.const (I := I) (M := M) (c • W)).toFun x
            = c • riemannCurvature (fun _ => z)
                (SmoothVectorField.const (I := I) (M := M) V).toFun
                (SmoothVectorField.const (I := I) (M := M) W).toFun x
        have h_const_smul : ((fun _ : M => c • W) : (y : M) → TangentSpace I y)
            = c • (fun _ => W) := by funext y; rfl
        have h_const_W_smooth : ∀ y, OpenGALib.TangentSmoothAt
            (fun _ : M => W) y :=
          fun y => (SmoothVectorField.const (I := I) (M := M) W).smoothAt y
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
              (SmoothVectorField.const (I := I) (M := M) W) x)
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
              (SmoothVectorField.const (I := I) (M := M) W) x)
        rw [hT2]
        rw [smul_sub, smul_sub] }
  map_add' V₁ V₂ := by
    -- LinearMap-level additivity in V slot.
    refine LinearMap.ext fun W => ?_
    show ricci (SmoothVectorField.const (I := I) (M := M) (V₁ + V₂))
            (SmoothVectorField.const (I := I) (M := M) W) x
        = ricci (SmoothVectorField.const (I := I) (M := M) V₁)
            (SmoothVectorField.const (I := I) (M := M) W) x
          + ricci (SmoothVectorField.const (I := I) (M := M) V₂)
            (SmoothVectorField.const (I := I) (M := M) W) x
    unfold ricci
    rw [show ricciTraceMap (SmoothVectorField.const (I := I) (M := M) (V₁ + V₂))
              (SmoothVectorField.const (I := I) (M := M) W) x
          = ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V₁)
              (SmoothVectorField.const (I := I) (M := M) W) x
            + ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V₂)
              (SmoothVectorField.const (I := I) (M := M) W) x from ?_]
    · exact (LinearMap.trace ℝ _).map_add _ _
    refine LinearMap.ext fun z => ?_
    show riemannCurvature (fun _ => z)
          (SmoothVectorField.const (I := I) (M := M) (V₁ + V₂)).toFun
          (SmoothVectorField.const (I := I) (M := M) W).toFun x
        = riemannCurvature (fun _ => z)
            (SmoothVectorField.const (I := I) (M := M) V₁).toFun
            (SmoothVectorField.const (I := I) (M := M) W).toFun x
          + riemannCurvature (fun _ => z)
            (SmoothVectorField.const (I := I) (M := M) V₂).toFun
            (SmoothVectorField.const (I := I) (M := M) W).toFun x
    have h_const_add : ((fun _ : M => V₁ + V₂) : (y : M) → TangentSpace I y)
        = (fun _ => V₁) + (fun _ => V₂) := by funext y; rfl
    have h_const_V₁_smooth : ∀ y, OpenGALib.TangentSmoothAt
        (fun _ : M => V₁) y :=
      fun y => (SmoothVectorField.const (I := I) (M := M) V₁).smoothAt y
    have h_const_V₂_smooth : ∀ y, OpenGALib.TangentSmoothAt
        (fun _ : M => V₂) y :=
      fun y => (SmoothVectorField.const (I := I) (M := M) V₂).smoothAt y
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
          (SmoothVectorField.const (I := I) (M := M) W) x)
        (covDeriv_const_smoothVF_smoothAt (I := I) (M := M) V₂
          (SmoothVectorField.const (I := I) (M := M) W) x)
    rw [hT1, hT3]
    abel
  map_smul' c V := by
    refine LinearMap.ext fun W => ?_
    show ricci (SmoothVectorField.const (I := I) (M := M) (c • V))
            (SmoothVectorField.const (I := I) (M := M) W) x
        = ((RingHom.id ℝ) c • ricci (SmoothVectorField.const (I := I) (M := M) V)
            (SmoothVectorField.const (I := I) (M := M) W) x : ℝ)
    unfold ricci
    rw [show ricciTraceMap (SmoothVectorField.const (I := I) (M := M) (c • V))
              (SmoothVectorField.const (I := I) (M := M) W) x
          = c • ricciTraceMap (SmoothVectorField.const (I := I) (M := M) V)
              (SmoothVectorField.const (I := I) (M := M) W) x from ?_]
    · simp [LinearMap.map_smul]
    refine LinearMap.ext fun z => ?_
    show riemannCurvature (fun _ => z)
          (SmoothVectorField.const (I := I) (M := M) (c • V)).toFun
          (SmoothVectorField.const (I := I) (M := M) W).toFun x
        = c • riemannCurvature (fun _ => z)
            (SmoothVectorField.const (I := I) (M := M) V).toFun
            (SmoothVectorField.const (I := I) (M := M) W).toFun x
    have h_const_smul : ((fun _ : M => c • V) : (y : M) → TangentSpace I y)
        = c • (fun _ => V) := by funext y; rfl
    have h_const_V_smooth : ∀ y, OpenGALib.TangentSmoothAt
        (fun _ : M => V) y :=
      fun y => (SmoothVectorField.const (I := I) (M := M) V).smoothAt y
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
          (SmoothVectorField.const (I := I) (M := M) W) x)
    rw [hT1]
    rw [smul_sub, smul_sub]

/-- **Ricci endomorphism** $\mathrm{Ric}^{\sharp}_x : T_xM \to T_xM$,
defined by metric raising of the Ricci bilinear form:
$\langle \mathrm{Ric}^{\sharp}_x(V), W\rangle_g = \mathrm{Ric}(V, W)(x)$.

This is the basis-free Ricci-as-endomorphism whose trace is the scalar
curvature. Linearity is inherited from `metricToDualEquiv.symm` (a
`LinearEquiv`) composed with `ricciFormAt x V` (auto-continuous in
finite dim via `LinearMap.toContinuousLinearMap`). -/
noncomputable def ricciEndo (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun V :=
    metricRiesz (g := ‹_›) x (ricciFormAt (I := I) (M := M) x V).toContinuousLinearMap
  map_add' V₁ V₂ := by
    show metricRiesz x ((ricciFormAt x (V₁ + V₂)).toContinuousLinearMap)
        = metricRiesz x ((ricciFormAt x V₁).toContinuousLinearMap)
        + metricRiesz x ((ricciFormAt x V₂).toContinuousLinearMap)
    rw [show ricciFormAt (I := I) (M := M) x (V₁ + V₂)
          = ricciFormAt x V₁ + ricciFormAt x V₂ from
        (ricciFormAt (I := I) (M := M) x).map_add V₁ V₂]
    show (metricToDualEquiv x).symm
          ((ricciFormAt x V₁ + ricciFormAt x V₂).toContinuousLinearMap)
        = (metricToDualEquiv x).symm ((ricciFormAt x V₁).toContinuousLinearMap)
        + (metricToDualEquiv x).symm ((ricciFormAt x V₂).toContinuousLinearMap)
    rw [show (ricciFormAt (I := I) (M := M) x V₁
                + ricciFormAt x V₂).toContinuousLinearMap
          = (ricciFormAt x V₁).toContinuousLinearMap
            + (ricciFormAt x V₂).toContinuousLinearMap from
        LinearMap.toContinuousLinearMap.map_add _ _]
    exact (metricToDualEquiv x).symm.map_add _ _
  map_smul' c V := by
    show metricRiesz x ((ricciFormAt x (c • V)).toContinuousLinearMap)
        = c • metricRiesz x ((ricciFormAt x V).toContinuousLinearMap)
    rw [show ricciFormAt (I := I) (M := M) x (c • V)
          = c • ricciFormAt x V from
        (ricciFormAt (I := I) (M := M) x).map_smul c V]
    show (metricToDualEquiv x).symm ((c • ricciFormAt x V).toContinuousLinearMap)
        = c • (metricToDualEquiv x).symm ((ricciFormAt x V).toContinuousLinearMap)
    rw [show (c • ricciFormAt (I := I) (M := M) x V).toContinuousLinearMap
          = c • (ricciFormAt x V).toContinuousLinearMap from
        LinearMap.toContinuousLinearMap.map_smul _ _]
    exact (metricToDualEquiv x).symm.map_smul c _

/-- The **scalar curvature** $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x)
= \mathrm{tr}(\mathrm{Ric}^{\sharp}_x)$.

**Basis-free** definition: trace of the Ricci endomorphism (Ricci
bilinear form raised by the metric). This avoids the previous
`stdOrthonormalBasis` definition, which was orthonormal w.r.t. the
background `inner E` — not the Riemannian metric `g_x` — and would
have produced the wrong value on any non-Euclidean manifold.

Equivalent to $\sum_i \mathrm{Ric}(e_i, e_i)$ for any $g$-orthonormal
basis $\{e_i\}$ of $T_xM$, but the basis-free form is the canonical
mathematical definition.

**Ground truth**: do Carmo 1992 §4 (defined as $g^{ij} \mathrm{Ric}_{ij}$,
i.e., metric trace of the Ricci $(0,2)$-tensor). -/
noncomputable def scalarCurvature (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) (M := M) x)

end Riemannian

/-! ## UXTest

Self-test verifying curvature primitives resolve their typeclass
cascade. -/
section UXTest

open Riemannian

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x := riemannCurvature X Y Z x

/-- Antisymmetry corollary `riemannCurvature_antisymm` is invocable. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x = -riemannCurvature Y X Z x :=
  riemannCurvature_antisymm X Y Z x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (X Y : SmoothVectorField I M) (x : M) : ℝ := ricci X Y x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (x : M) : ℝ :=
  scalarCurvature (I := I) x

end UXTest
