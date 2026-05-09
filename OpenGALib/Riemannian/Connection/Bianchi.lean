import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Util.Attributes

/-!
# Riemannian.Connection.Bianchi

Algebraic (first) Bianchi identity for the Levi-Civita connection:

  $$R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0$$

where $R(X,Y)Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X,Y]} Z$.

## Architectural placement

Algebraic Bianchi I is a **connection-level** statement: its proof
depends only on torsion-freeness of $\nabla$ and the Jacobi identity for
the Lie bracket. Metric compatibility, inner-product structure, Riesz
extraction, Koszul formula are **not** used. We state Bianchi I directly
for the framework's `covDeriv` (Levi-Civita), but the proof technique
generalizes verbatim to any torsion-free affine connection on the
tangent bundle.

## Proof structure

Let $S := R(X,Y)Z + R(Y,Z)X + R(Z,X)Y$. Pair the nine terms as three
$\nabla_A B - \nabla_A C$ pairs (with `covDeriv_sub_field`) plus the
three $\nabla_{[\cdot,\cdot]}$ terms:

$$S = \nabla_X (\nabla_Y Z - \nabla_Z Y) + \nabla_Y (\nabla_Z X - \nabla_X Z)
    + \nabla_Z (\nabla_X Y - \nabla_Y X)
    - \nabla_{[X,Y]} Z - \nabla_{[Y,Z]} X - \nabla_{[Z,X]} Y.$$

Each inner difference is $[\cdot, \cdot]$ by torsion-freeness:

$$S = \nabla_X [Y,Z] + \nabla_Y [Z,X] + \nabla_Z [X,Y]
    - \nabla_{[X,Y]} Z - \nabla_{[Y,Z]} X - \nabla_{[Z,X]} Y.$$

Pair again as $\nabla_A B - \nabla_B A = [A,B]$ (torsion-freeness):

$$S = [X, [Y,Z]] + [Y, [Z,X]] + [Z, [X,Y]] = 0,$$

the last by the Jacobi identity for `mlieBracket`
(`leibniz_identity_mlieBracket_apply`).

## Used by

  * `Riemannian.Curvature` — closes `ricci_symm` (full Riemann tensor
    $(0,4)$-symmetry under metric compatibility, traced).
  * Future Mathlib upstream PR candidate (connection-level statement,
    free of metric assumptions; second Bianchi follows the same path).

**Ground truth**: do Carmo 1992 §4 Proposition 2.5 (ii).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-! ## Framework helpers

Three pointwise lemmas exposed from the Levi-Civita connection's
`CovariantDerivative` structure: torsion-freeness, additivity in the
differentiated field, and subtractivity (corollary). -/

/-- **Pointwise torsion-freeness** of the Levi-Civita connection:
$\nabla_X Y - \nabla_Y X = [X, Y]$ at any point where $X, Y$ are
differentiable as bundle sections. -/
theorem covDeriv_sub_swap_eq_mlieBracket
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    covDeriv X Y x - covDeriv Y X x = mlieBracket I X Y x :=
  (CovariantDerivative.torsion_eq_zero_iff
    (cov := leviCivitaConnection (I := I) (M := M))).mp
    leviCivitaConnection_torsion_zero hX hY

/-- **Additivity of `covDeriv` in the differentiated field**:
$\nabla_X (Y_1 + Y_2)(x) = \nabla_X Y_1(x) + \nabla_X Y_2(x)$ when
$Y_1, Y_2$ are `TangentSmoothAt` at $x$.

Direct from `IsCovariantDerivativeOn.add` applied to
`leviCivitaConnection.isCovariantDerivativeOnUniv`, evaluated at $X(x)$. -/
theorem covDeriv_add_field
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x) :
    covDeriv X (Y₁ + Y₂) x = covDeriv X Y₁ x + covDeriv X Y₂ x := by
  have h := leviCivitaConnection.isCovariantDerivativeOnUniv.add (σ := Y₁) (σ' := Y₂)
    (x := x) hY₁ hY₂
  show (leviCivitaConnection.toFun (Y₁ + Y₂) x) (X x)
    = (leviCivitaConnection.toFun Y₁ x) (X x) + (leviCivitaConnection.toFun Y₂ x) (X x)
  rw [h]
  rfl

/-- **`covDeriv` of a constant scalar multiple in the differentiated field**:
$\nabla_X (a \cdot Y)(x) = a \cdot \nabla_X Y(x)$ for $a : \mathbb{R}$.

Direct from `IsCovariantDerivativeOn.smul_const`. -/
theorem covDeriv_smul_const_field
    (X Y : Π x : M, TangentSpace I x) (x : M) (a : ℝ)
    (hY : TangentSmoothAt Y x) :
    covDeriv X (a • Y) x = a • covDeriv X Y x := by
  have h := leviCivitaConnection.isCovariantDerivativeOnUniv.smul_const (σ := Y)
    (x := x) a hY
  show (leviCivitaConnection.toFun (a • Y) x) (X x)
    = a • (leviCivitaConnection.toFun Y x) (X x)
  rw [h]
  rfl

/-- **Subtractivity of `covDeriv` in the differentiated field**:
$\nabla_X (Y_1 - Y_2)(x) = \nabla_X Y_1(x) - \nabla_X Y_2(x)$.

Derived from additivity + `smul_const a := -1`. -/
theorem covDeriv_sub_field
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x) :
    covDeriv X (Y₁ - Y₂) x = covDeriv X Y₁ x - covDeriv X Y₂ x := by
  -- Y₁ - Y₂ = Y₁ + (-1) • Y₂
  have h_eq : (Y₁ - Y₂ : Π x : M, TangentSpace I x) = Y₁ + ((-1 : ℝ) • Y₂) := by
    funext z
    show Y₁ z - Y₂ z = Y₁ z + (-1 : ℝ) • Y₂ z
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h_eq]
  -- Smoothness of (-1) • Y₂: from TangentSmoothAt.neg via Y₁ - Y₂ form.
  have h_neg : TangentSmoothAt ((-1 : ℝ) • Y₂) x := by
    have h_eq' : ((-1 : ℝ) • Y₂ : Π x : M, TangentSpace I x) = -Y₂ := by
      funext z
      show (-1 : ℝ) • Y₂ z = -Y₂ z
      exact neg_one_smul _ _
    rw [h_eq']
    exact hY₂.neg
  rw [covDeriv_add_field X Y₁ ((-1 : ℝ) • Y₂) x hY₁ h_neg,
      covDeriv_smul_const_field X Y₂ x (-1) hY₂]
  show covDeriv X Y₁ x + (-1 : ℝ) • covDeriv X Y₂ x = covDeriv X Y₁ x - covDeriv X Y₂ x
  rw [neg_one_smul, sub_eq_add_neg]

/-! ## Riemann curvature tensor (connection-level definition)

The Riemann curvature tensor depends only on $\nabla$ (and the Lie
bracket) — no metric required. We place its definition here at the
connection-level layer so Bianchi I can reference it without circular
import. Metric-dependent extensions (Ricci as trace, full $(0,4)$-symmetry,
sectional curvature) live in `Riemannian.Curvature`. -/

/-- The **Riemann curvature tensor**:
$R(X, Y)Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.

Connection-level definition: only `covDeriv` (Levi-Civita) and `mlieBracket`
appear. Metric-dependent properties (full antisymmetry, Ricci as trace,
sectional curvature) belong in `Riemannian.Curvature`.

**Ground truth**: do Carmo 1992 §4 Definition 2.1. -/
noncomputable def riemannCurvature
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  let nablaYZ : Π x : M, TangentSpace I x := fun x => covDeriv Y Z x
  let nablaXZ : Π x : M, TangentSpace I x := fun x => covDeriv X Z x
  let bracketXY : Π x : M, TangentSpace I x := fun x => mlieBracket I X Y x
  covDeriv X nablaYZ x - covDeriv Y nablaXZ x - covDeriv bracketXY Z x

/-! ### `riem_simp` lemmas

Two rewrites that drive the `riem_simp` simp set, populated for the
Riemann curvature operator built from the framework's `covDeriv`. Together
with `abel` they discharge the algebraic identities of `riemannCurvature`
without exposing the underlying connection plumbing. -/

/-- **Definitional unfold** of `riemannCurvature` to the
$\nabla \nabla - \nabla \nabla - \nabla_{[\cdot,\cdot]}$ form.
Pure rewrite — no smoothness hypotheses. -/
@[riem_simp]
theorem riemannCurvature_unfold
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x
      = covDeriv X (fun y => covDeriv Y Z y) x
        - covDeriv Y (fun y => covDeriv X Z y) x
        - covDeriv (fun y => mlieBracket I X Y y) Z x := rfl

/-- **Lie-bracket antisymmetry pulled through the connection's direction
argument**: $\nabla_{[Y,X]} Z = -\nabla_{[X,Y]} Z$ pointwise. Combines
`VectorField.mlieBracket_swap_apply` with the ℝ-linearity of
`leviCivitaConnection.toFun Z x` (a CLM, so it commutes with negation).
Pure rewrite — no smoothness hypotheses.

Used as an explicit `rw` step (not in `riem_simp`): the rewrite is
symmetric in `X ↔ Y`, so adding it to a simp set causes loop. -/
theorem covDeriv_lambda_mlieBracket_swap
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    covDeriv (fun y => mlieBracket I Y X y) Z x
      = -covDeriv (fun y => mlieBracket I X Y y) Z x := by
  unfold covDeriv
  rw [show (fun y => mlieBracket I Y X y) x = -mlieBracket I X Y x from
        VectorField.mlieBracket_swap_apply,
      (leviCivitaConnection.toFun Z x).map_neg]

/-- **Riemann tensor antisymmetry in the first two arguments**:
$R(X, Y) Z = -R(Y, X) Z$ pointwise.

Math: Lie bracket is antisymmetric and the connection is linear in its
direction argument. `simp only [riem_simp]` unfolds `R` to its
$\nabla \nabla - \nabla \nabla - \nabla_{[\cdot,\cdot]}$ form;
`covDeriv_lambda_mlieBracket_swap` pulls the bracket-swap negation
through `covDeriv`; `abel` finishes.

**Ground truth**: do Carmo 1992 §4 Proposition 2.5 (i). -/
theorem riemannCurvature_antisymm
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x = -riemannCurvature Y X Z x := by
  simp only [riem_simp]
  rw [covDeriv_lambda_mlieBracket_swap]
  abel

/-! ## Algebraic Bianchi I

Under **global** smoothness of `X, Y, Z` (i.e. `∀ y, TangentSmoothAt _ y`),
the torsion-free identity lifts from pointwise to a **section-level
equality** (Pi-equality via `funext`):

  `(fun y => covDeriv Y Z y) = (fun y => covDeriv Z Y y) + mlieBracket I Y Z`

This bypasses any locality / nbhd-congruence lemma — once the sections
are literally equal as Π-functions, `covDeriv X (·) x` accepts the
substitution directly.

The two derivations needed at section level: -/

/-- **Section-level torsion-freeness**: under global smoothness, the
torsion-free pointwise identity becomes a Π-equality. -/
theorem covDeriv_section_eq_swap_add_mlieBracket
    (Y Z : Π x : M, TangentSpace I x)
    (hY : ∀ y, TangentSmoothAt Y y) (hZ : ∀ y, TangentSmoothAt Z y) :
    (fun y => covDeriv Y Z y)
      = (fun y => covDeriv Z Y y) + (fun y => mlieBracket I Y Z y) := by
  funext y
  have h := covDeriv_sub_swap_eq_mlieBracket Y Z y (hY y) (hZ y)
  -- h : covDeriv Y Z y - covDeriv Z Y y = mlieBracket I Y Z y
  show covDeriv Y Z y = covDeriv Z Y y + mlieBracket I Y Z y
  rw [← h]; abel

/-- **Algebraic (first) Bianchi identity** for the Levi-Civita connection:

$$R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0.$$

Smoothness hypotheses (all `TangentSmoothAt` at `x`):
  * `X, Y, Z` — the three input fields,
  * `∇_Y Z, ∇_Z Y, ∇_Z X, ∇_X Z, ∇_X Y, ∇_Y X` — six first-derivative
    fields appearing in the $\nabla \nabla$ terms,
  * `[X, Y], [Y, Z], [Z, X]` — three Lie brackets appearing in the
    $\nabla_{[\cdot, \cdot]}$ terms.

These match the standard textbook setup ($X, Y, Z$ are $C^2$ smooth,
which makes all derived fields $C^1$ and hence differentiable). The
explicit-hypothesis form lets the lemma fire pointwise without a global
$C^2$ premise.

**Ground truth**: do Carmo 1992 §4 Proposition 2.5 (ii). -/
theorem bianchi_first
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : ∀ y, TangentSmoothAt X y) (hY : ∀ y, TangentSmoothAt Y y)
    (hZ : ∀ y, TangentSmoothAt Z y)
    (h_dXZ : ∀ y, TangentSmoothAt (fun y' => covDeriv X Z y') y)
    (h_dYX : ∀ y, TangentSmoothAt (fun y' => covDeriv Y X y') y)
    (h_dZY : ∀ y, TangentSmoothAt (fun y' => covDeriv Z Y y') y)
    (h_XY : ∀ y, TangentSmoothAt (fun y' => mlieBracket I X Y y') y)
    (h_YX : ∀ y, TangentSmoothAt (fun y' => mlieBracket I Y X y') y)
    (h_YZ : ∀ y, TangentSmoothAt (fun y' => mlieBracket I Y Z y') y)
    (h_ZX : ∀ y, TangentSmoothAt (fun y' => mlieBracket I Z X y') y)
    (h_XZ : ∀ y, TangentSmoothAt (fun y' => mlieBracket I X Z y') y)
    (h_jac : mlieBracket I X (mlieBracket I Y Z) x
              = mlieBracket I (mlieBracket I X Y) Z x
                + mlieBracket I Y (mlieBracket I X Z) x) :
    riemannCurvature X Y Z x + riemannCurvature Y Z X x + riemannCurvature Z X Y x = 0 := by
  -- Step 1: section-level torsion-freeness (Π-equalities, via global smoothness).
  have eq_YZ : (fun y => covDeriv Y Z y) = (fun y => covDeriv Z Y y)
                  + (fun y => mlieBracket I Y Z y) :=
    covDeriv_section_eq_swap_add_mlieBracket Y Z hY hZ
  have eq_ZX : (fun y => covDeriv Z X y) = (fun y => covDeriv X Z y)
                  + (fun y => mlieBracket I Z X y) :=
    covDeriv_section_eq_swap_add_mlieBracket Z X hZ hX
  have eq_XY : (fun y => covDeriv X Y y) = (fun y => covDeriv Y X y)
                  + (fun y => mlieBracket I X Y y) :=
    covDeriv_section_eq_swap_add_mlieBracket X Y hX hY
  -- Step 2: unfold riemannCurvature, substitute section equalities, split via add_field.
  show covDeriv X (fun y => covDeriv Y Z y) x
        - covDeriv Y (fun y => covDeriv X Z y) x
        - covDeriv (fun y => mlieBracket I X Y y) Z x
      + (covDeriv Y (fun y => covDeriv Z X y) x
        - covDeriv Z (fun y => covDeriv Y X y) x
        - covDeriv (fun y => mlieBracket I Y Z y) X x)
      + (covDeriv Z (fun y => covDeriv X Y y) x
        - covDeriv X (fun y => covDeriv Z Y y) x
        - covDeriv (fun y => mlieBracket I Z X y) Y x) = 0
  rw [eq_YZ, eq_ZX, eq_XY]
  rw [covDeriv_add_field X (fun y => covDeriv Z Y y) (fun y => mlieBracket I Y Z y) x
        (h_dZY x) (h_YZ x),
      covDeriv_add_field Y (fun y => covDeriv X Z y) (fun y => mlieBracket I Z X y) x
        (h_dXZ x) (h_ZX x),
      covDeriv_add_field Z (fun y => covDeriv Y X y) (fun y => mlieBracket I X Y y) x
        (h_dYX x) (h_XY x)]
  -- Step 3: pointwise torsion-free pairings (∇_A B - ∇_B A = [A,B]):
  have pair_X : covDeriv X (fun y => mlieBracket I Y Z y) x
                  - covDeriv (fun y => mlieBracket I Y Z y) X x
                = mlieBracket I X (mlieBracket I Y Z) x :=
    covDeriv_sub_swap_eq_mlieBracket X (fun y => mlieBracket I Y Z y) x (hX x) (h_YZ x)
  have pair_Y : covDeriv Y (fun y => mlieBracket I Z X y) x
                  - covDeriv (fun y => mlieBracket I Z X y) Y x
                = mlieBracket I Y (mlieBracket I Z X) x :=
    covDeriv_sub_swap_eq_mlieBracket Y (fun y => mlieBracket I Z X y) x (hY x) (h_ZX x)
  have pair_Z : covDeriv Z (fun y => mlieBracket I X Y y) x
                  - covDeriv (fun y => mlieBracket I X Y y) Z x
                = mlieBracket I Z (mlieBracket I X Y) x :=
    covDeriv_sub_swap_eq_mlieBracket Z (fun y => mlieBracket I X Y y) x (hZ x) (h_XY x)
  -- Step 4: rearrange so abel collapses all 12 cov-terms via pair_X/Y/Z.
  -- The goal after rewrites is (with shorthand):
  --   (∇_X∇_Z Y + ∇_X[Y,Z]) - ∇_Y∇_X Z - ∇_{[X,Y]} Z
  --   + (∇_Y∇_X Z + ∇_Y[Z,X]) - ∇_Z∇_Y X - ∇_{[Y,Z]} X
  --   + (∇_Z∇_Y X + ∇_Z[X,Y]) - ∇_X∇_Z Y - ∇_{[Z,X]} Y = 0
  -- Three pairs of mixed ∇∇ terms cancel; remaining 6 terms group via pair_X/Y/Z to:
  --   [X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0   (Jacobi).
  -- We rewrite using pair_X/Y/Z by isolating the LHS shapes.
  -- pair_X gives ∇_X[Y,Z] = pair_X.lhs.lhs ↦ … — to use pair_X as a substitution,
  -- we set up the equations as A = mlie + B and rewrite ∇_X[Y,Z] = mlie + ∇_{[Y,Z]} X:
  have h_subX : covDeriv X (fun y => mlieBracket I Y Z y) x
                  = mlieBracket I X (mlieBracket I Y Z) x
                    + covDeriv (fun y => mlieBracket I Y Z y) X x := by
    rw [← pair_X]; abel
  have h_subY : covDeriv Y (fun y => mlieBracket I Z X y) x
                  = mlieBracket I Y (mlieBracket I Z X) x
                    + covDeriv (fun y => mlieBracket I Z X y) Y x := by
    rw [← pair_Y]; abel
  have h_subZ : covDeriv Z (fun y => mlieBracket I X Y y) x
                  = mlieBracket I Z (mlieBracket I X Y) x
                    + covDeriv (fun y => mlieBracket I X Y y) Z x := by
    rw [← pair_Z]; abel
  rw [h_subX, h_subY, h_subZ]
  -- Goal now has 3 outer-bracket terms + 6 ∇_·_ terms; three pairs of ∇_{[·,·]} ·
  -- match (positive in subX/Y/Z, negative in 3 outer ∇_{[·,·]} · slots) — abel kills.
  -- 3 pairs of mixed ∇∇ terms also cancel (∇_X∇_Z Y, ∇_Y∇_X Z, ∇_Z∇_Y X).
  -- Result: [X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0.
  -- Step 5: convert [Y,[Z,X]] and [Z,[X,Y]] into Jacobi-compatible forms via antisymm.
  -- Section-level antisymm:
  have sec_ZX : (fun y => mlieBracket I Z X y) = -(fun y => mlieBracket I X Z y) := by
    funext y; exact VectorField.mlieBracket_swap_apply
  have sec_XY : (fun y => mlieBracket I X Y y) = -(fun y => mlieBracket I Y X y) := by
    funext y; exact VectorField.mlieBracket_swap_apply
  -- Use Mathlib `mlieBracket_const_smul_right` (with c = -1) to pull negation out.
  have h_YZX : mlieBracket I Y (mlieBracket I Z X) x
                = -mlieBracket I Y (mlieBracket I X Z) x := by
    have h_eq : (mlieBracket I Z X : Π y : M, TangentSpace I y)
              = (-1 : ℝ) • mlieBracket I X Z := by
      funext y
      show mlieBracket I Z X y = (-1 : ℝ) • mlieBracket I X Z y
      rw [neg_one_smul]
      exact VectorField.mlieBracket_swap_apply
    rw [h_eq, VectorField.mlieBracket_const_smul_right (h_XZ x), neg_one_smul]
  have h_ZXY : mlieBracket I Z (mlieBracket I X Y) x
                = -mlieBracket I Z (mlieBracket I Y X) x := by
    have h_eq : (mlieBracket I X Y : Π y : M, TangentSpace I y)
              = (-1 : ℝ) • mlieBracket I Y X := by
      funext y
      show mlieBracket I X Y y = (-1 : ℝ) • mlieBracket I Y X y
      rw [neg_one_smul]
      exact VectorField.mlieBracket_swap_apply
    rw [h_eq, VectorField.mlieBracket_const_smul_right (h_YX x), neg_one_smul]
  -- Outer antisymm: [[X,Y], Z] x = -[Z, [X,Y]] x
  have asym_outer : mlieBracket I (mlieBracket I X Y) Z x
                  = -mlieBracket I Z (mlieBracket I X Y) x :=
    VectorField.mlieBracket_swap_apply
  -- Now: goal (after abel-cancels) reduces to:
  --   [X,[Y,Z]] x + [Y,[Z,X]] x + [Z,[X,Y]] x = 0
  -- = ([[X,Y],Z] + [Y,[X,Z]]) + (-[Y,[X,Z]]) + [Z,[X,Y]]    (h_jac, h_YZX)
  -- = [[X,Y],Z] + [Z,[X,Y]]
  -- = -[Z,[X,Y]] + [Z,[X,Y]] = 0                              (asym_outer)
  -- We chain these into the goal via abel.
  rw [h_jac, h_YZX, asym_outer]
  abel

end Riemannian
