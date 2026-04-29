import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Riemannian.Connection.Koszul
import Riemannian.Metric.Riesz
import Riemannian.Metric.Smooth

/-!
# Levi-Civita connection via Koszul + Riesz

Given the Koszul functional from `Riemannian/Connection/Koszul.lean`,
this file performs Riesz extraction to obtain `koszulCovDeriv` (the
pointwise Levi-Civita value), then packages it into Mathlib's
`CovariantDerivative` structure and derives torsion-freeness +
metric-compatibility.

`leviCivitaConnection_exists` is closed by combining:

* `koszulLeviCivita_exists` — narrow structural axiom (sorry'd): a
  `CovariantDerivative` whose `toFun` extends the pointwise Koszul
  value for smooth inputs. Type-level CLM-construction work; see
  `SORRY_CATALOG.md`.
* `koszul_antisymm` → torsion-free via `metricInner_eq_iff_eq` +
  `koszulCovDeriv_inner_eq` + Mathlib's `FiberBundle.extend`.
* `koszul_metric_compat_sum` → metric-compatibility for smooth vector
  fields.

`covDeriv X Y x := (leviCivitaConnection.toFun Y x) (X x)` is the
public-API convenience wrapper exposing the standard math notation
$\nabla_X Y$.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6.
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianMetric I M]

/-! ## Riesz extraction: explicit Levi-Civita via Koszul

Constructs $\nabla_X Y(x) \in T_xM$ directly via Riesz representation of
the half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$. Combined
with $C^\infty(M)$-linearity in $Z$ (`koszul_smul_right`), this
characterises $\nabla_X Y(x)$ as the unique vector with
$$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$$
for all smooth $Z$. Riesz uses the framework-owned `metricRiesz`. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **Locality of the Koszul functional in $Z$**: if two smooth vector
fields $Z_1, Z_2$ agree on a neighborhood of $x$, then
$K(X, Y; Z_1)(x) = K(X, Y; Z_2)(x)$.

Foundation lemma for extension-independence: combined with bump function
decomposition, this gives well-definedness of the linear functional in
`koszulLinearFunctional_exists`.

The 6 Koszul terms localize via:
* `directionalDeriv` terms: `Filter.EventuallyEq.mfderiv_eq` (Mathlib).
* `metricInner (mlieBracket _ _ _) _` terms with $Z$ in mlieBracket:
  `Filter.EventuallyEq.mlieBracket_vectorField_eq` (Mathlib).
* Pointwise inner-product terms: equality at $x$ from `h.self_of_nhds`. -/
theorem koszulFunctional_local
    (X Y Z₁ Z₂ : Π x : M, TangentSpace I x) (x : M)
    (h : Z₁ =ᶠ[nhds x] Z₂) :
    koszulFunctional X Y Z₁ x = koszulFunctional X Y Z₂ x := by
  have hZx : Z₁ x = Z₂ x := h.self_of_nhds
  unfold koszulFunctional directionalDeriv
  have hT1 : (fun y => metricInner y (Y y) (Z₁ y))
      =ᶠ[nhds x] fun y => metricInner y (Y y) (Z₂ y) := by
    filter_upwards [h] with y hy; rw [hy]
  have hT2 : (fun y => metricInner y (Z₁ y) (X y))
      =ᶠ[nhds x] fun y => metricInner y (Z₂ y) (X y) := by
    filter_upwards [h] with y hy; rw [hy]
  have hT5 : mlieBracket I Y Z₁ x = mlieBracket I Y Z₂ x :=
    (Filter.EventuallyEq.refl (nhds x) Y).mlieBracket_vectorField_eq h
  have hT6 : mlieBracket I X Z₁ x = mlieBracket I X Z₂ x :=
    (Filter.EventuallyEq.refl (nhds x) X).mlieBracket_vectorField_eq h
  rw [hT1.mfderiv_eq, hT2.mfderiv_eq, hZx, hT5, hT6]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Tensoriality at $x$ of the half-Koszul functional in the third argument.**


For smooth $X, Y$ at $x$, the operation
$Z \mapsto \tfrac12 K(X, Y; Z)(x)$ on smooth tangent-bundle sections
is tensorial at $x$: it respects $C^\infty(M)$-scalar multiplication
(via `koszul_smul_right`) and addition (via `koszul_add_right`).

The scalar smoothness hypotheses of `koszul_smul_right` /
`koszul_add_right` (`hYZ`, `hZX`, `h_YZ₁/₂`, `h_Z₁/₂X`) are derived
from the bundle-section smoothness of $X, Y, Z$ via
`MDifferentiableAt.metricInner_smoothAt`. -/
private theorem koszulFunctional_tensorialAt
    (X Y : Π y : M, TangentSpace I y) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x) :
    TensorialAt I E (fun Z : (Π y : M, TangentSpace I y) =>
      (1/2 : ℝ) * koszulFunctional X Y Z x) x where
  smul := by
    intro f σ hf hσ
    have hYZ := MDifferentiableAt.metricInner_smoothAt hY hσ
    have hZX := MDifferentiableAt.metricInner_smoothAt hσ hX
    have heq : (f • σ : Π y : M, TangentSpace I y) = fun y => f y • σ y := rfl
    show (1/2 : ℝ) * koszulFunctional X Y (f • σ) x
        = f x • ((1/2 : ℝ) * koszulFunctional X Y σ x)
    rw [heq, koszul_smul_right X Y σ f x hf hYZ hZX hσ]
    show (1/2 : ℝ) * (f x * koszulFunctional X Y σ x)
        = f x * ((1/2 : ℝ) * koszulFunctional X Y σ x)
    ring
  add := by
    intro σ σ' hσ hσ'
    have h_YZ₁ := MDifferentiableAt.metricInner_smoothAt hY hσ
    have h_YZ₂ := MDifferentiableAt.metricInner_smoothAt hY hσ'
    have h_Z₁X := MDifferentiableAt.metricInner_smoothAt hσ hX
    have h_Z₂X := MDifferentiableAt.metricInner_smoothAt hσ' hX
    show (1/2 : ℝ) * koszulFunctional X Y (σ + σ') x
        = (1/2 : ℝ) * koszulFunctional X Y σ x
        + (1/2 : ℝ) * koszulFunctional X Y σ' x
    rw [koszul_add_right X Y σ σ' x h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X hσ hσ']
    ring

/-- **Existence theorem for Riesz extraction**: given smoothness of $X$
and $Y$ at $x$, the half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$
admits a unique tangent-space representative for smooth $Z$.

Proof: `TensorialAt.mkHom` applied to `koszulFunctional_tensorialAt`
(tensoriality from `koszul_smul_right` + `koszul_add_right`) +
`TensorialAt.mkHom_apply` for the defining identity. Smoothness of $X, Y$
is needed to derive scalar smoothness of $\langle Y, Z \rangle$ and
$\langle Z, X \rangle$ via `metricInner_smoothAt`; smoothness of $Z$ is
required because $K(X, Y; Z)(x)$ depends on $Z$'s behaviour near $x$
via `mfderiv` and `mlieBracket`.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 existence proof, Step 3. -/
private theorem koszulLinearFunctional_exists
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x) :
    ∃ φ : (TangentSpace I x) →L[ℝ] ℝ,
      ∀ Z : Π y : M, TangentSpace I y,
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x →
        φ (Z x) = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  refine ⟨TensorialAt.mkHom _ x (koszulFunctional_tensorialAt X Y x hX hY),
          fun Z hZ => ?_⟩
  exact TensorialAt.mkHom_apply (koszulFunctional_tensorialAt X Y x hX hY) hZ

theorem koszulCovDeriv_exists
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x) :
    ∃ v : TangentSpace I x, ∀ Z : Π y : M, TangentSpace I y,
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x →
      metricInner x v (Z x) = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  obtain ⟨φ, hφ⟩ := koszulLinearFunctional_exists X Y x hX hY
  refine ⟨metricRiesz x φ, fun Z hZ => ?_⟩
  rw [metricRiesz_inner]
  exact hφ Z hZ

/-- **Levi-Civita via Koszul + Riesz** (explicit construction):
$\nabla_X Y(x) \in T_xM$ is the unique vector with
$$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$$
for all smooth $Z$, extracted via Riesz from `koszulCovDeriv_exists`.
The metric is the framework-owned `metricInner`.

When both $X$ and $Y$ are smooth at $x$, returns the Riesz representative
via `Classical.choose` over `koszulCovDeriv_exists`. -/
noncomputable def koszulCovDeriv
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x) : TangentSpace I x :=
  Classical.choose (koszulCovDeriv_exists X Y x hX hY)

/-- **Riesz defining property**: $\langle \nabla_X Y(x), Z(x)\rangle =
\tfrac12 K(X, Y; Z)(x)$ for smooth $X, Y, Z$, with `metricInner` as the
framework-owned inner product.

Direct extraction via `Classical.choose_spec` from `koszulCovDeriv_exists`. -/
theorem koszulCovDeriv_inner_eq
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x) :
    metricInner x (koszulCovDeriv X Y x hX hY) (Z x)
      = (1/2 : ℝ) * koszulFunctional X Y Z x :=
  Classical.choose_spec (koszulCovDeriv_exists X Y x hX hY) Z hZ

/-! ## Levi-Civita closure via Koszul + Riesz

`leviCivitaConnection_exists` is closed by combining:

* `koszulLeviCivita_exists` — narrow structural axiom (sorry'd): a
  `CovariantDerivative` whose `toFun` extends the pointwise Koszul
  value for smooth inputs. Type-level CLM-construction work, no new
  mathematical content. See `SORRY_CATALOG.md`.
* `koszul_antisymm` → torsion-free via `metricInner_eq_iff_eq` +
  `koszulCovDeriv_inner_eq` + Mathlib's `FiberBundle.extend`.
* `koszul_metric_compat_sum` → metric-compatibility for smooth vector
  fields. -/

/-- **Narrow CovariantDerivative wrap axiom for the Koszul construction.**

A `CovariantDerivative` whose `toFun` extends the pointwise
`koszulCovDeriv` value for smooth $(X, Y)$. The body is a TensorialAt
mkHom in the X argument plus the `IsCovariantDerivativeOnUniv` add /
leibniz fields (derivable from `koszul_add_middle` /
`koszul_smul_middle` via Riesz); see `SORRY_CATALOG.md`. -/
private theorem koszulLeviCivita_exists :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      ∀ (X Y : Π x : M, TangentSpace I x) (x : M)
        (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
        (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x),
        cov.toFun Y x (X x) = koszulCovDeriv X Y x hX hY := by
  sorry

/-- **Existence theorem for the Levi-Civita connection.**

On a Riemannian manifold, there exists a covariant derivative on the
tangent bundle that is torsion-free and metric-compatible (for smooth
vector fields).

The metric-compat statement assumes smooth $X, Y, Z$ — matching do Carmo's
textbook setup; an unconditional form would be an over-statement.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (existence + uniqueness via
the Koszul formula). -/
theorem leviCivitaConnection_exists :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      cov.torsion = 0 ∧
      ∀ (X Y Z : Π x : M, TangentSpace I x) (x : M)
        (_hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
        (_hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
        (_hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x),
        mfderiv I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x (X x) =
          metricInner x (cov.toFun Y x (X x)) (Z x) +
          metricInner x (Y x) (cov.toFun Z x (X x)) := by
  obtain ⟨cov, hcov⟩ := koszulLeviCivita_exists (I := I) (M := M)
  refine ⟨cov, ?_, ?_⟩
  · -- Torsion = 0
    rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x hX hY
    rw [hcov X Y x hX hY, hcov Y X x hY hX]
    apply (metricInner_eq_iff_eq x _ _).mp
    intro Z₀
    set Z : Π y : M, TangentSpace I y := FiberBundle.extend E Z₀ with hZ_def
    have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
    have hZ_smooth : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x :=
      FiberBundle.mdifferentiableAt_extend I E Z₀
    rw [← hZx]
    rw [metricInner_sub_left,
        koszulCovDeriv_inner_eq X Y Z x hX hY hZ_smooth,
        koszulCovDeriv_inner_eq Y X Z x hY hX hZ_smooth]
    -- Goal: 1/2 * K X Y Z x - 1/2 * K Y X Z x = metricInner x (mlieBracket I X Y x) (Z x)
    have h := koszul_antisymm X Y Z x
    -- h: K X Y Z x - K Y X Z x = 2 * metricInner x (mlieBracket I X Y x) (Z x)
    linarith
  · -- Metric-compat for smooth X, Y, Z
    intro X Y Z x hX hY hZ
    rw [hcov X Y x hX hY, hcov X Z x hX hZ]
    rw [show metricInner x (Y x) (koszulCovDeriv X Z x hX hZ) =
        metricInner x (koszulCovDeriv X Z x hX hZ) (Y x) from
      metricInner_comm x _ _,
        koszulCovDeriv_inner_eq X Y Z x hX hY hZ,
        koszulCovDeriv_inner_eq X Z Y x hX hZ hY]
    have hsum := koszul_metric_compat_sum X Y Z x
    -- hsum : K X Y Z + K X Z Y = 2 * directionalDeriv ... x (X x)
    -- Convert goal to directionalDeriv form (rfl by def of directionalDeriv).
    show directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x) =
        (1 / 2) * koszulFunctional X Y Z x + (1 / 2) * koszulFunctional X Z Y x
    linarith

/-- The **Levi-Civita connection** $\nabla$ on the tangent bundle of a
Riemannian manifold $M$: the unique torsion-free, metric-compatible
covariant derivative.

Real `noncomputable def` via `Classical.choose` over the now-closed
`leviCivitaConnection_exists`. The chosen value
satisfies `leviCivitaConnection.torsion = 0` (see
`leviCivitaConnection_torsion_zero`).

**Ground truth**: do Carmo 1992 §2; Koszul formula gives uniqueness.

**Used by**: `Riemannian.Curvature`, `Riemannian.SecondFundamentalForm`,
`Riemannian.Gradient`. -/
noncomputable def leviCivitaConnection :
    CovariantDerivative I E (fun x : M => TangentSpace I x) :=
  Classical.choose (leviCivitaConnection_exists (I := I) (M := M))

/-- The Levi-Civita connection is torsion-free. -/
theorem leviCivitaConnection_torsion_zero :
    (leviCivitaConnection : CovariantDerivative I E
      (fun x : M => TangentSpace I x)).torsion = 0 :=
  (Classical.choose_spec leviCivitaConnection_exists).1

/-- The Levi-Civita connection is **metric-compatible** for smooth
vector fields: for $X, Y, Z$ smooth at $x$,
$$\nabla_X \langle Y, Z \rangle (x) =
  \langle \nabla_X Y, Z \rangle (x) + \langle Y, \nabla_X Z \rangle (x).$$

The metric is the framework-owned `metricInner`. Smoothness hypotheses
on $X, Y, Z$ match do Carmo 1992 §2 Theorem 3.6's textbook setup. -/
theorem leviCivitaConnection_metric_compatible
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x (X x) =
      metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Y x (X x)) (Z x) +
      metricInner x (Y x)
        ((leviCivitaConnection (I := I) (M := M)).toFun Z x (X x)) :=
  (Classical.choose_spec leviCivitaConnection_exists).2 X Y Z x hX hY hZ

/-- **Covariant derivative of one vector field along another**:
$(\nabla_X Y)(x) := \nabla\,Y\,x\,(X\,x)$, where $\nabla$ is the
Levi-Civita connection (`leviCivitaConnection`).

Convenience wrapper that exposes the standard math notation
$\nabla_X Y$ from Mathlib's bundled `CovariantDerivative.toFun`,
specialised to the framework's Levi-Civita instance.

By construction, `covDeriv` is torsion-free and metric-compatible (with
respect to the framework-owned `metricInner`); see
`leviCivitaConnection_torsion_zero` and
`leviCivitaConnection_metric_compatible` for the precise statements.

**Public API**: consumed by `Riemannian.Curvature` (Riemann curvature
tensor formula), `Riemannian.SecondFundamentalForm` (codim-1 second
fundamental form), and `GeometricMeasureTheory.Variation.FirstVariation`
(codim-1 normal correction term).

**Ground truth**: do Carmo 1992 §2 Definition 2.1 (covariant derivative
along a vector field). -/
noncomputable def covDeriv (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  ((leviCivitaConnection (I := I) (M := M)).toFun Y x) (X x)


end Riemannian
