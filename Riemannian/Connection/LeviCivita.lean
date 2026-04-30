import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Riemannian.Connection.Koszul
import Riemannian.Metric.Riesz

/-!
# Levi-Civita connection via Koszul + Riesz

Given the Koszul functional from `Riemannian/Connection/Koszul.lean`,
this file performs Riesz extraction to obtain `koszulCovDeriv` (the
pointwise Levi-Civita value), then packages it into Mathlib's
`CovariantDerivative` structure and derives torsion-freeness +
metric-compatibility.

`leviCivitaConnection_exists` is closed by combining:

* `koszulLeviCivita_exists` — `TensorialAt.mkHom` packaging of
  `koszulCovDeriv` into a `CovariantDerivative`. Tensoriality in $X$
  comes from `koszulCovDerivAux_tensorialAt` (Riesz uniqueness against
  `metricInner_eq_iff_eq` + `koszul_add_left` / `koszul_smul_left`);
  `IsCovariantDerivativeOn.add` / `.leibniz` from `koszul_add_middle` /
  `koszul_smul_middle` via the same uniqueness pattern. Real proof,
  no `sorry`.
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
open scoped ContDiff Manifold Topology

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

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
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
    [FiniteDimensional ℝ E]
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π y : M, TangentSpace I y) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
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

omit [CompleteSpace E] in
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
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    ∃ φ : (TangentSpace I x) →L[ℝ] ℝ,
      ∀ Z : Π y : M, TangentSpace I y,
        TangentSmoothAt Z x →
        φ (Z x) = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  refine ⟨TensorialAt.mkHom _ x (koszulFunctional_tensorialAt X Y x hX hY),
          fun Z hZ => ?_⟩
  exact TensorialAt.mkHom_apply (koszulFunctional_tensorialAt X Y x hX hY) hZ

omit [CompleteSpace E] in
private theorem koszulCovDeriv_exists
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    ∃ v : TangentSpace I x, ∀ Z : Π y : M, TangentSpace I y,
      TangentSmoothAt Z x →
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
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) : TangentSpace I x :=
  Classical.choose (koszulCovDeriv_exists X Y x hX hY)

omit [CompleteSpace E] in
/-- **Riesz defining property**: $\langle \nabla_X Y(x), Z(x)\rangle =
\tfrac12 K(X, Y; Z)(x)$ for smooth $X, Y, Z$, with `metricInner` as the
framework-owned inner product.

Direct extraction via `Classical.choose_spec` from `koszulCovDeriv_exists`. -/
theorem koszulCovDeriv_inner_eq
    [IsLocallyConstantChartedSpace H M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    metricInner x (koszulCovDeriv X Y x hX hY) (Z x)
      = (1/2 : ℝ) * koszulFunctional X Y Z x :=
  Classical.choose_spec (koszulCovDeriv_exists X Y x hX hY) Z hZ

/-! ## Levi-Civita closure via Koszul + Riesz

`leviCivitaConnection_exists` is closed by combining:

* `koszulLeviCivita_exists` — real `CovariantDerivative` whose `toFun`
  extends the pointwise Koszul value for smooth inputs. Construction:
  `TensorialAt.mkHom` over `koszulCovDerivAux` (smoothness-erased
  variant), with tensoriality via Riesz uniqueness against
  `metricInner_eq_iff_eq`. Real proof, no `sorry`.
* `koszul_antisymm` → torsion-free via `metricInner_eq_iff_eq` +
  `koszulCovDeriv_inner_eq` + Mathlib's `FiberBundle.extend`.
* `koszul_metric_compat_sum` → metric-compatibility for smooth vector
  fields. -/

/-! ### Construction of the Levi-Civita `CovariantDerivative`

Build the `CovariantDerivative` via:

1. `koszulCovDerivAux Y x hY` — smoothness-erased function `(X) ↦ ∇_X Y(x)`,
   defined as `koszulCovDeriv X Y x hX hY` for smooth `X` and `0` otherwise.
2. `koszulCovDerivAux_tensorialAt` — tensorality in `X` (the
   `C^∞`-linearity of $\nabla_\cdot Y$ at $x$), via `koszul_smul_left` /
   `koszul_add_left` + Riesz uniqueness.
3. `TensorialAt.mkHom` to obtain the CLM `T_xM →L[ℝ] T_xM`.
4. `IsCovariantDerivativeOn` add / leibniz from `koszul_add_middle` /
   `koszul_smul_middle` via Riesz uniqueness.
-/

/-- Smoothness-erased version of `koszulCovDeriv` in the `X` argument:
returns `koszulCovDeriv X Y x hX hY` for smooth `X`, `0` otherwise.
Needed because Mathlib's `TensorialAt` requires `Φ` to be defined on
**all** sections, not just smooth ones. -/
private noncomputable def koszulCovDerivAux
    [IsLocallyConstantChartedSpace H M]
    (Y : Π y : M, TangentSpace I y) (x : M) (hY : TangentSmoothAt Y x)
    (X : Π y : M, TangentSpace I y) : TangentSpace I x := by
  classical
  exact if hX : TangentSmoothAt X x then koszulCovDeriv X Y x hX hY else 0

/-- Tensorality of `koszulCovDerivAux Y x hY` in the `X` argument: for
smooth `X`, `f`, `koszulCovDerivAux` respects scalar multiplication and
addition. Uses `koszul_smul_left` / `koszul_add_left` together with
Riesz uniqueness (`metricInner_eq_iff_eq` against an arbitrary
extended test vector). -/
private theorem koszulCovDerivAux_tensorialAt
    [IsLocallyConstantChartedSpace H M]
    (Y : Π y : M, TangentSpace I y) (x : M) (hY : TangentSmoothAt Y x) :
    TensorialAt I E (koszulCovDerivAux Y x hY) x where
  smul := by
    intro f X hf hX_raw
    classical
    -- Cast hX_raw (which has type def-equal to TangentSmoothAt X x) into the
    -- canonical TangentSmoothAt form, so that `dif_pos` rewrites fire.
    have hX : TangentSmoothAt X x := hX_raw
    have h_fX : TangentSmoothAt (f • X) x := TangentSmoothAt.smul hf hX
    show koszulCovDerivAux Y x hY (f • X) = f x • koszulCovDerivAux Y x hY X
    simp only [koszulCovDerivAux, dif_pos hX, dif_pos h_fX]
    apply (metricInner_eq_iff_eq x _ _).mp
    intro Z₀
    set Z : Π y : M, TangentSpace I y := FiberBundle.extend E Z₀
    have hZ_smooth : TangentSmoothAt Z x :=
      FiberBundle.mdifferentiableAt_extend I E Z₀
    have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
    have h_ZX := MDifferentiableAt.metricInner_smoothAt hZ_smooth hX
    have h_XY := MDifferentiableAt.metricInner_smoothAt hX hY
    -- Convert the Pi-smul `f • X` form on the LHS to `fun y => f y • X y` so
    -- that `koszul_smul_left` (stated in the latter form) rewrites.
    have h_smul_left :
        koszulFunctional (f • X) Y Z x = f x * koszulFunctional X Y Z x :=
      koszul_smul_left X Y Z f x hf h_ZX h_XY hX
    rw [← hZx,
        koszulCovDeriv_inner_eq _ _ _ x h_fX hY hZ_smooth,
        h_smul_left,
        metricInner_smul_left,
        koszulCovDeriv_inner_eq X Y Z x hX hY hZ_smooth]
    ring
  add := by
    intro X X' hX_raw hX'_raw
    classical
    have hX : TangentSmoothAt X x := hX_raw
    have hX' : TangentSmoothAt X' x := hX'_raw
    have h_sum : TangentSmoothAt (X + X') x := TangentSmoothAt.add hX hX'
    show koszulCovDerivAux Y x hY (X + X')
        = koszulCovDerivAux Y x hY X + koszulCovDerivAux Y x hY X'
    simp only [koszulCovDerivAux, dif_pos hX, dif_pos hX', dif_pos h_sum]
    apply (metricInner_eq_iff_eq x _ _).mp
    intro Z₀
    set Z : Π y : M, TangentSpace I y := FiberBundle.extend E Z₀
    have hZ_smooth : TangentSmoothAt Z x :=
      FiberBundle.mdifferentiableAt_extend I E Z₀
    have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
    have h_ZX₁ := MDifferentiableAt.metricInner_smoothAt hZ_smooth hX
    have h_ZX₂ := MDifferentiableAt.metricInner_smoothAt hZ_smooth hX'
    have h_X₁Y := MDifferentiableAt.metricInner_smoothAt hX hY
    have h_X₂Y := MDifferentiableAt.metricInner_smoothAt hX' hY
    have h_add_left :
        koszulFunctional (X + X') Y Z x
          = koszulFunctional X Y Z x + koszulFunctional X' Y Z x :=
      koszul_add_left X X' Y Z x h_ZX₁ h_ZX₂ h_X₁Y h_X₂Y hX hX'
    rw [← hZx,
        koszulCovDeriv_inner_eq _ _ _ x h_sum hY hZ_smooth,
        h_add_left,
        metricInner_add_left,
        koszulCovDeriv_inner_eq X Y Z x hX hY hZ_smooth,
        koszulCovDeriv_inner_eq X' Y Z x hX' hY hZ_smooth]
    ring

/-- **Levi-Civita `CovariantDerivative` existence.**

A `CovariantDerivative` whose `toFun` extends the pointwise
`koszulCovDeriv` value for smooth $(X, Y)$. Construction:

* `toFun Y x` is `TensorialAt.mkHom (koszulCovDerivAux Y x hY) x ...`
  for smooth `Y`, `0` otherwise.
* `IsCovariantDerivativeOn.add` follows from `koszul_add_middle` +
  Riesz uniqueness.
* `IsCovariantDerivativeOn.leibniz` follows from `koszul_smul_middle` +
  Riesz uniqueness; the extra `2 * X(g) * ⟨Y, Z⟩` term in
  `koszul_smul_middle` is exactly the `(extDerivFun g x).smulRight (Y x)`
  term in the Leibniz field after the `1/2` factor cancels. -/
private theorem koszulLeviCivita_exists [IsLocallyConstantChartedSpace H M] :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      ∀ (X Y : Π x : M, TangentSpace I x) (x : M)
        (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x),
        cov.toFun Y x (X x) = koszulCovDeriv X Y x hX hY := by
  classical
  -- Step 1: build cov.toFun Y x as the mkHom CLM for smooth Y, else 0.
  let toFun : (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun Y x =>
      if hY : TangentSmoothAt Y x then
        TensorialAt.mkHom (koszulCovDerivAux Y x hY) x
          (koszulCovDerivAux_tensorialAt Y x hY)
      else 0
  -- Step 2: prove IsCovariantDerivativeOn for `toFun`.
  refine ⟨⟨toFun, ?_⟩, ?_⟩
  · refine ⟨?add, ?leibniz⟩
    case add =>
      -- toFun (Y₁ + Y₂) x = toFun Y₁ x + toFun Y₂ x for smooth Y₁, Y₂.
      intro Y₁ Y₂ x hY₁ hY₂ _
      have hY₁' : TangentSmoothAt Y₁ x := hY₁
      have hY₂' : TangentSmoothAt Y₂ x := hY₂
      have h_sum : TangentSmoothAt (Y₁ + Y₂) x := TangentSmoothAt.add hY₁' hY₂'
      simp only [toFun, dif_pos hY₁', dif_pos hY₂', dif_pos h_sum]
      ext v
      -- It suffices to show (mkHom_sum) v = (mkHom_Y₁) v + (mkHom_Y₂) v.
      set V : Π y : M, TangentSpace I y := FiberBundle.extend E v
      have hV_smooth : TangentSmoothAt V x :=
        FiberBundle.mdifferentiableAt_extend I E v
      have hVx : V x = v := FiberBundle.extend_apply_self _ _
      rw [ContinuousLinearMap.add_apply]
      rw [← hVx]
      rw [TensorialAt.mkHom_apply _ hV_smooth,
          TensorialAt.mkHom_apply _ hV_smooth,
          TensorialAt.mkHom_apply _ hV_smooth]
      -- Goal: koszulCovDerivAux (Y₁+Y₂) x h_sum V
      --     = koszulCovDerivAux Y₁ x hY₁ V + koszulCovDerivAux Y₂ x hY₂ V
      simp only [koszulCovDerivAux, dif_pos hV_smooth]
      -- Goal: koszulCovDeriv V (Y₁+Y₂) x ... = koszulCovDeriv V Y₁ x ... + koszulCovDeriv V Y₂ x ...
      apply (metricInner_eq_iff_eq x _ _).mp
      intro Z₀
      set Z : Π y : M, TangentSpace I y := FiberBundle.extend E Z₀
      have hZ_smooth : TangentSmoothAt Z x :=
        FiberBundle.mdifferentiableAt_extend I E Z₀
      have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
      have h_Y₁Z := MDifferentiableAt.metricInner_smoothAt hY₁ hZ_smooth
      have h_Y₂Z := MDifferentiableAt.metricInner_smoothAt hY₂ hZ_smooth
      have h_VY₁ := MDifferentiableAt.metricInner_smoothAt hV_smooth hY₁
      have h_VY₂ := MDifferentiableAt.metricInner_smoothAt hV_smooth hY₂
      rw [← hZx,
          koszulCovDeriv_inner_eq _ _ _ x hV_smooth h_sum hZ_smooth,
          koszul_add_middle V Y₁ Y₂ Z x h_Y₁Z h_Y₂Z h_VY₁ h_VY₂ hY₁ hY₂,
          metricInner_add_left,
          koszulCovDeriv_inner_eq V Y₁ Z x hV_smooth hY₁ hZ_smooth,
          koszulCovDeriv_inner_eq V Y₂ Z x hV_smooth hY₂ hZ_smooth]
      ring
    case leibniz =>
      -- toFun (g • Y) x = g x • toFun Y x + (extDerivFun g x).smulRight (Y x)
      intro Y g x hY hg _
      have hY' : TangentSmoothAt Y x := hY
      have h_gY_lambda : TangentSmoothAt (fun y => g y • Y y) x :=
        TangentSmoothAt.smul hg hY'
      -- Note: g • Y = fun y => g y • Y y (Pi-smul, definitionally)
      have h_gY' : TangentSmoothAt (g • Y) x := h_gY_lambda
      simp only [toFun, dif_pos hY', dif_pos h_gY']
      ext v
      set V : Π y : M, TangentSpace I y := FiberBundle.extend E v
      have hV_smooth : TangentSmoothAt V x :=
        FiberBundle.mdifferentiableAt_extend I E v
      have hVx : V x = v := FiberBundle.extend_apply_self _ _
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      rw [← hVx]
      rw [TensorialAt.mkHom_apply _ hV_smooth,
          TensorialAt.mkHom_apply _ hV_smooth]
      simp only [koszulCovDerivAux, dif_pos hV_smooth]
      -- Goal: koszulCovDeriv V (g•Y) x ... = g x • koszulCovDeriv V Y x ... +
      --       (extDerivFun g x).smulRight (Y x) v
      apply (metricInner_eq_iff_eq x _ _).mp
      intro Z₀
      set Z : Π y : M, TangentSpace I y := FiberBundle.extend E Z₀
      have hZ_smooth : TangentSmoothAt Z x :=
        FiberBundle.mdifferentiableAt_extend I E Z₀
      have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
      have h_YZ := MDifferentiableAt.metricInner_smoothAt hY hZ_smooth
      have h_VY := MDifferentiableAt.metricInner_smoothAt hV_smooth hY
      rw [← hZx,
          koszulCovDeriv_inner_eq _ _ _ x hV_smooth h_gY' hZ_smooth]
      -- LHS = (1/2) * koszulFunctional V (g • Y) Z x
      -- by koszul_smul_middle:
      --     = (1/2) * (g x * K V Y Z x + 2 * directionalDeriv g x (V x) * ⟨Y x, Z x⟩)
      rw [show (g • Y : Π y : M, TangentSpace I y) = fun y => g y • Y y from rfl]
      rw [koszul_smul_middle V Y Z g x hg h_YZ h_VY hY]
      -- RHS expands via koszulCovDeriv_inner_eq V Y Z and metricInner_add/smul.
      rw [metricInner_add_left, metricInner_smul_left,
          koszulCovDeriv_inner_eq V Y Z x hV_smooth hY hZ_smooth]
      -- Remaining goal (modulo extDerivFun = directionalDeriv):
      -- (1/2) * (g x * K V Y Z + 2 * dDeriv g x (V x) * ⟨Y x, Z x⟩)
      --   = g x * (1/2) * K V Y Z + (extDerivFun g x).smulRight (Y x) v • Z x
      show (1 / 2 : ℝ) *
          (g x * koszulFunctional V Y Z x
            + 2 * directionalDeriv g x (V x) * metricInner x (Y x) (Z x))
          = g x *
              ((1 / 2 : ℝ) * koszulFunctional V Y Z x)
            + metricInner x ((extDerivFun g x).smulRight (Y x) (V x)) (Z x)
      -- Unfold extDerivFun and smulRight at (V x).
      have h_smulRight :
          ((extDerivFun (I := I) g x).smulRight (Y x) (V x) : TangentSpace I x)
            = directionalDeriv g x (V x) • Y x := by
        show (extDerivFun (I := I) g x (V x)) • Y x
            = directionalDeriv g x (V x) • Y x
        rfl
      rw [h_smulRight, metricInner_smul_left]
      ring
  -- Step 3: prove the main equation cov.toFun Y x (X x) = koszulCovDeriv X Y x hX hY.
  · intro X Y x hX hY
    show toFun Y x (X x) = koszulCovDeriv X Y x hX hY
    simp only [toFun, dif_pos hY]
    rw [TensorialAt.mkHom_apply _ hX]
    -- Goal: koszulCovDerivAux Y x hY X = koszulCovDeriv X Y x hX hY
    simp only [koszulCovDerivAux, dif_pos hX]

/-- **Existence theorem for the Levi-Civita connection.**

On a Riemannian manifold, there exists a covariant derivative on the
tangent bundle that is torsion-free and metric-compatible (for smooth
vector fields).

The metric-compat statement assumes smooth $X, Y, Z$ — matching do Carmo's
textbook setup; an unconditional form would be an over-statement.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (existence + uniqueness via
the Koszul formula). -/
theorem leviCivitaConnection_exists [IsLocallyConstantChartedSpace H M] :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      cov.torsion = 0 ∧
      ∀ (X Y Z : Π x : M, TangentSpace I x) (x : M)
        (_hX : TangentSmoothAt X x) (_hY : TangentSmoothAt Y x)
        (_hZ : TangentSmoothAt Z x),
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
    have hZ_smooth : TangentSmoothAt Z x :=
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
noncomputable def leviCivitaConnection
    [IsLocallyConstantChartedSpace H M] :
    CovariantDerivative I E (fun x : M => TangentSpace I x) :=
  Classical.choose (leviCivitaConnection_exists (I := I) (M := M))

/-- The Levi-Civita connection is torsion-free. -/
theorem leviCivitaConnection_torsion_zero
    [IsLocallyConstantChartedSpace H M] :
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
    [IsLocallyConstantChartedSpace H M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
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
noncomputable def covDeriv
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  ((leviCivitaConnection (I := I) (M := M)).toFun Y x) (X x)

/-- **Riesz formula for the covariant derivative**: for smooth $X, Y, Z$,
$$\langle \nabla_X Y, Z\rangle_g(x) = \tfrac12 K(X, Y; Z)(x).$$

Standard Levi-Civita derivation: cycling the metric-compat identity over
$(X, Y, Z)$, $(Y, Z, X)$, $(Z, X, Y)$ and substituting torsion-freeness
$\nabla_Y X = \nabla_X Y - [X, Y]$ etc. isolates
$\langle \nabla_X Y, Z\rangle$. -/
theorem covDeriv_inner_eq_half_koszul
    [IsLocallyConstantChartedSpace H M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    metricInner x (covDeriv X Y x) (Z x)
      = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  -- Notation: write `cov A B := leviCivitaConnection.toFun B x (A x)` (= covDeriv A B x).
  -- We'll identify these via `show` against the unfolded form and use linarith.
  -- Spec from Classical.choose: torsion-free + metric-compat for smooth fields.
  obtain ⟨h_tors, h_compat⟩ := Classical.choose_spec
    (leviCivitaConnection_exists (I := I) (M := M))
  -- Three cyclic metric-compat instances + 3 torsion-free instances.
  -- Wrap each LHS into `directionalDeriv` (= mfderiv) so that all
  -- arithmetic happens uniformly in `ℝ`.
  have hXY : directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x)
      = metricInner x ((leviCivitaConnection.toFun Y x) (X x)) (Z x)
        + metricInner x (Y x) ((leviCivitaConnection.toFun Z x) (X x)) :=
    h_compat X Y Z x hX hY hZ
  have hYZ : directionalDeriv (fun y => metricInner y (Z y) (X y)) x (Y x)
      = metricInner x ((leviCivitaConnection.toFun Z x) (Y x)) (X x)
        + metricInner x (Z x) ((leviCivitaConnection.toFun X x) (Y x)) :=
    h_compat Y Z X x hY hZ hX
  have hZX : directionalDeriv (fun y => metricInner y (X y) (Y y)) x (Z x)
      = metricInner x ((leviCivitaConnection.toFun X x) (Z x)) (Y x)
        + metricInner x (X x) ((leviCivitaConnection.toFun Y x) (Z x)) :=
    h_compat Z X Y x hZ hX hY
  rw [CovariantDerivative.torsion_eq_zero_iff] at h_tors
  have h_torsXY := @h_tors X Y x hX hY
  have h_torsYZ := @h_tors Y Z x hY hZ
  have h_torsZX := @h_tors Z X x hZ hX
  -- Symmetrize the right slot of each metric-compat equation, then convert to
  -- the unfolded `leviCivitaConnection` form so all cov-quantities live in
  -- the same syntactic namespace.
  rw [metricInner_comm x (Y x)] at hXY
  rw [metricInner_comm x (Z x)] at hYZ
  rw [metricInner_comm x (X x)] at hZX
  -- Convert torsion-free identities to inner-product form, in the
  -- `leviCivitaConnection` syntactic form.
  have htXY :
      metricInner x (leviCivitaConnection.toFun Y x (X x)) (Z x)
      - metricInner x (leviCivitaConnection.toFun X x (Y x)) (Z x)
      = metricInner x (mlieBracket I X Y x) (Z x) := by
    have := congrArg (fun v => metricInner x v (Z x)) h_torsXY
    simpa [metricInner_sub_left] using this
  have htYZ :
      metricInner x (leviCivitaConnection.toFun Z x (Y x)) (X x)
      - metricInner x (leviCivitaConnection.toFun Y x (Z x)) (X x)
      = metricInner x (mlieBracket I Y Z x) (X x) := by
    have := congrArg (fun v => metricInner x v (X x)) h_torsYZ
    simpa [metricInner_sub_left] using this
  have htZX :
      metricInner x (leviCivitaConnection.toFun X x (Z x)) (Y x)
      - metricInner x (leviCivitaConnection.toFun Z x (X x)) (Y x)
      = metricInner x (mlieBracket I Z X x) (Y x) := by
    have := congrArg (fun v => metricInner x v (Y x)) h_torsZX
    simpa [metricInner_sub_left] using this
  -- [Z,X] = -[X,Z], so its inner product flips sign.
  have h_brXZ : metricInner x (mlieBracket I Z X x) (Y x)
      = -metricInner x (mlieBracket I X Z x) (Y x) := by
    rw [show mlieBracket I Z X x = -mlieBracket I X Z x from
        VectorField.mlieBracket_swap_apply, metricInner_neg_left]
  -- Goal: 2⟨covXY, Z⟩ = K. linarith closes after combining hypotheses linearly.
  show metricInner x ((leviCivitaConnection.toFun Y x) (X x)) (Z x)
    = (1/2 : ℝ) * (
        directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x)
      + directionalDeriv (fun y => metricInner y (Z y) (X y)) x (Y x)
      - directionalDeriv (fun y => metricInner y (X y) (Y y)) x (Z x)
      + metricInner x (mlieBracket I X Y x) (Z x)
      - metricInner x (mlieBracket I Y Z x) (X x)
      - metricInner x (mlieBracket I X Z x) (Y x))
  linarith [hXY, hYZ, hZX, htXY, htYZ, htZX, h_brXZ]


/-! ## Locality of Koszul + covariant derivative

If two sections agree on a nbhd of `x`, their Koszul functional values at `x`
agree, and consequently their Levi-Civita derivatives at `x` agree (Riesz
uniqueness). -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **Locality of `koszulFunctional` in the middle argument**: if
$Y_1 =ᶠ[𝓝 x] Y_2$, then $K(X, Y_1; Z)(x) = K(X, Y_2; Z)(x)$.

All 6 terms are local at `x`:
* 3 directional derivative terms: 2 functions depend on $Y$ via metric
  inner products (use `Filter.EventuallyEq.mfderiv_eq`); 1 uses $Y(x)$ as
  the direction (constant from `EventuallyEq` evaluated at `x`).
* 3 Lie-bracket inner-product terms: the bracket
  `mlieBracket I · Y ·` is local in `Y` at `x`. -/
theorem koszulFunctional_eventuallyEq_middle
    (X Y₁ Y₂ Z : Π x : M, TangentSpace I x) (x : M)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    koszulFunctional X Y₁ Z x = koszulFunctional X Y₂ Z x := by
  -- Pointwise equality at `x` follows from `EventuallyEq` membership.
  have hx : Y₁ x = Y₂ x := h.self_of_nhds
  -- Function-level eventual equalities for the 3 directionalDeriv arguments.
  have h_metYZ : (fun y => metricInner y (Y₁ y) (Z y))
      =ᶠ[𝓝 x] (fun y => metricInner y (Y₂ y) (Z y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have h_metXY : (fun y => metricInner y (X y) (Y₁ y))
      =ᶠ[𝓝 x] (fun y => metricInner y (X y) (Y₂ y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  -- Lie bracket pointwise equalities at `x`.
  have h_brXY : mlieBracket I X Y₁ x = mlieBracket I X Y₂ x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq (Filter.EventuallyEq.refl _ X) h
  have h_brYZ : mlieBracket I Y₁ Z x = mlieBracket I Y₂ Z x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq h (Filter.EventuallyEq.refl _ Z)
  -- Unfold koszulFunctional and directionalDeriv (definitional) and assemble.
  unfold koszulFunctional directionalDeriv
  rw [h_metYZ.mfderiv_eq, h_metXY.mfderiv_eq, hx, h_brXY, h_brYZ]
  rfl

/-- **Locality of `covDeriv` in the middle argument** (Riesz uniqueness):
if $Y_1 =ᶠ[𝓝 x] Y_2$ and both are smooth at $x$, then for smooth $X$,
$\nabla_X Y_1(x) = \nabla_X Y_2(x)$. -/
theorem covDeriv_congr_eventuallyEq_middle
    [IsLocallyConstantChartedSpace H M]
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    covDeriv X Y₁ x = covDeriv X Y₂ x := by
  -- By Riesz uniqueness on `metricInner_eq_iff_eq`: equal inner-products against
  -- arbitrary test vector ⇒ equal vectors. Test via the smooth FiberBundle.extend
  -- of a model-fiber test, lift through `covDeriv_inner_eq_half_koszul`, then use
  -- `koszulFunctional_eventuallyEq_middle`.
  apply (metricInner_eq_iff_eq x _ _).mp
  intro Z₀
  set Z : Π y : M, TangentSpace I y := FiberBundle.extend E Z₀ with hZ_def
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
  have hZ_smooth : TangentSmoothAt Z x :=
    FiberBundle.mdifferentiableAt_extend I E Z₀
  rw [← hZx]
  rw [covDeriv_inner_eq_half_koszul X Y₁ Z x hX hY₁ hZ_smooth,
      covDeriv_inner_eq_half_koszul X Y₂ Z x hX hY₂ hZ_smooth,
      koszulFunctional_eventuallyEq_middle X Y₁ Y₂ Z x h]

end Riemannian
