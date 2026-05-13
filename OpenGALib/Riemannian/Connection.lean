import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import OpenGALib.Riemannian.Manifold
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Riemannian.Tensor.MusicalIso
import OpenGALib.Riemannian.Connection.TangentHelpers
import OpenGALib.Riemannian.Connection.Koszul
import OpenGALib.Riemannian.Connection.CotangentFunctional
import OpenGALib.Util.Attributes

/-!
# Levi-Civita connection

The unique torsion-free, metric-compatible affine connection on a
Riemannian manifold $(M, g)$, together with the Riemann curvature tensor
and the algebraic Bianchi identity.

The connection is constructed via the **Koszul formula**:
$$2\langle \nabla_X Y,\, Z\rangle = K(X, Y; Z),$$
where $K(X, Y; Z) = X\langle Y, Z\rangle + Y\langle Z, X\rangle -
Z\langle X, Y\rangle + \langle [X, Y], Z\rangle - \langle [Y, Z], X\rangle
- \langle [X, Z], Y\rangle$. The $C^\infty(M)$-tensoriality of
$Z \mapsto K(X, Y; Z)$ together with Riesz extraction yields a unique
vector $\nabla_X Y(x) \in T_xM$ satisfying the formula.

The Koszul construction (`koszulFunctional`, algebraic identities,
chart-pullback cotangent continuous linear map, Riesz extraction `koszulCovDeriv`) is
engineering scaffolding under `private`; the mathematical surface is
`leviCivitaConnection`, `covDeriv`, `riemannCurvature`.

Reference: do Carmo, *Riemannian Geometry*, §2 Theorem 3.6;
§4 Proposition 2.5 (Bianchi I).
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology Riemannian

namespace Riemannian

/-! ## from `Connection.lean` (private) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

-- Bundle ↔ function-form / componentwise continuous linear map / mlieBracket smoothness
-- helpers live in `Connection/TangentHelpers.lean` (Foundation module).
-- Smoothness of `metricInner` on bundle sections lives in `Manifold.lean`
-- as the public `Riemannian.metricInner_contMDiff` (parametric over `n`).

/-! ## from `Connection.lean` (LeviCivita section) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [hm : HasMetric I M]

/-! ## Riesz extraction: explicit Levi-Civita via Koszul

Constructs $\nabla_X Y(x) \in T_xM$ directly via Riesz representation of
the half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$. Combined
with $C^\infty(M)$-linearity in $Z$ (`koszul_smul_right`), this
characterises $\nabla_X Y(x)$ as the unique vector with
$$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$$
for all smooth $Z$. Riesz uses the framework-owned `metricRiesz`. -/

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** **Riesz extraction existence**: under smoothness of $X, Y$
at $x$, the half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$
admits a unique tangent-space representative for smooth $Z$.

Closed via `TensorialAt.mkHom` on `koszulFunctional_tensorialAt`.

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

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** Riesz-extracted tangent vector `v ∈ T_xM` satisfying
$\langle v, Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$ for all smooth $Z$.
The Levi-Civita value $\nabla_X Y(x)$. -/
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

/-- **Math.** **Levi-Civita via Koszul + Riesz** (explicit construction):
$\nabla_X Y(x) \in T_xM$ is the unique vector with
$$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$$
for all smooth $Z$, extracted via Riesz over the framework-owned
`metricInner`. -/
private noncomputable def koszulCovDeriv
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) : TangentSpace I x :=
  Classical.choose (koszulCovDeriv_exists X Y x hX hY)

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** **Riesz defining property**:
$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$ for smooth
$X, Y, Z$, with `metricInner` as the framework-owned inner product. -/
private theorem koszulCovDeriv_inner_eq
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
3. `TensorialAt.mkHom` to obtain the continuous linear map `T_xM →L[ℝ] T_xM`.
4. `IsCovariantDerivativeOn` add / leibniz from `koszul_add_middle` /
   `koszul_smul_middle` via Riesz uniqueness.
-/

/-- **Eng.** Smoothness-erased version of `koszulCovDeriv` in the `X`
argument: returns `koszulCovDeriv X Y x hX hY` for smooth `X`, `0`
otherwise. Required because Mathlib's `TensorialAt` quantifies over all
sections, not just smooth ones. -/
private noncomputable def koszulCovDerivAux
    [IsLocallyConstantChartedSpace H M]
    (Y : Π y : M, TangentSpace I y) (x : M) (hY : TangentSmoothAt Y x)
    (X : Π y : M, TangentSpace I y) : TangentSpace I x := by
  classical
  exact if hX : TangentSmoothAt X x then koszulCovDeriv X Y x hX hY else 0

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] in
/-- **Mixed.** Tensoriality of `koszulCovDerivAux Y x hY` in the `X`
argument. Math: $\nabla_\cdot Y$ is $C^\infty(M)$-linear in $X$ (`koszul_smul_left`,
`koszul_add_left`). Eng: lifted from `koszulFunctional` to `koszulCovDeriv`
through `metricInner_eq_iff_eq` against extended test vectors. -/
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
    have h_ZX := metricInner_mdifferentiableAt hZ_smooth hX
    have h_XY := metricInner_mdifferentiableAt hX hY
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
    have h_ZX₁ := metricInner_mdifferentiableAt hZ_smooth hX
    have h_ZX₂ := metricInner_mdifferentiableAt hZ_smooth hX'
    have h_X₁Y := metricInner_mdifferentiableAt hX hY
    have h_X₂Y := metricInner_mdifferentiableAt hX' hY
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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] in
/-- **Math.** **Levi-Civita `CovariantDerivative` existence.** Builds a
`CovariantDerivative` whose `toFun` extends `koszulCovDeriv` for smooth
$(X, Y)$. `IsCovariantDerivativeOn.add` follows from `koszul_add_middle`
via Riesz uniqueness; `IsCovariantDerivativeOn.leibniz` from
`koszul_smul_middle` (the $2 \cdot X(g) \cdot \langle Y, Z\rangle$ term
matches `(extDerivFun g x).smulRight (Y x)` after the $\tfrac12$ factor
cancels). -/
private theorem koszulLeviCivita_exists [IsLocallyConstantChartedSpace H M] :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      ∀ (X Y : Π x : M, TangentSpace I x) (x : M)
        (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x),
        cov.toFun Y x (X x) = koszulCovDeriv X Y x hX hY := by
  classical
  -- Step 1: build cov.toFun Y x as the mkHom continuous linear map for smooth Y, else 0.
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
      have h_Y₁Z := metricInner_mdifferentiableAt hY₁ hZ_smooth
      have h_Y₂Z := metricInner_mdifferentiableAt hY₂ hZ_smooth
      have h_VY₁ := metricInner_mdifferentiableAt hV_smooth hY₁
      have h_VY₂ := metricInner_mdifferentiableAt hV_smooth hY₂
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
      have h_YZ := metricInner_mdifferentiableAt hY hZ_smooth
      have h_VY := metricInner_mdifferentiableAt hV_smooth hY
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

/-! ### Bridge: smoothness of `koszulCovDeriv X.toFun Y.toFun y` at `x` -/

set_option backward.isDefEq.respectTransparency false in
/-- **Mixed.** For `X, Y : SmoothVectorField I M`, the section
`y ↦ koszulCovDeriv X.toFun Y.toFun y` is `TangentSmoothAt` everywhere.

Math: smoothness of the Levi-Civita section under smooth inputs.
Eng: identifies `koszulCovDeriv` with `metricRiesz y (Φ y)` via Riesz
uniqueness, then reduces through `metricRiesz_section_contMDiffAt_of_within`
to per-chart-basis-index ContMDiffWithinAt of the six Koszul terms
transferred from a bumped global extension via `koszulFunctional_local`. -/
private theorem koszulCovDeriv_smoothVF_smoothAt
    [IsLocallyConstantChartedSpace H M]
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => koszulCovDeriv X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y)) x := by
  classical
  -- Step 1: Identify `koszulCovDeriv X Y y h h = metricRiesz y (Φ y)` via Riesz uniqueness.
  set Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ := fun y =>
    TensorialAt.mkHom _ y
      (koszulFunctional_tensorialAt X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y))
  have hRiesz : ∀ y : M,
      koszulCovDeriv X.toFun Y.toFun y (X.smoothAt y) (Y.smoothAt y)
        = metricRiesz y (Φ y) := by
    intro y
    refine metricRiesz_unique y _ (Φ y) ?_
    intro W
    -- Reduce to evaluating at a smooth extension of W via `FiberBundle.extend`.
    set V : Π z : M, TangentSpace I z := FiberBundle.extend E W
    have hV_smooth : TangentSmoothAt V y :=
      FiberBundle.mdifferentiableAt_extend I E W
    have hVy : V y = W := FiberBundle.extend_apply_self _ _
    rw [← hVy]
    rw [koszulCovDeriv_inner_eq X.toFun Y.toFun V y
      (X.smoothAt y) (Y.smoothAt y) hV_smooth]
    exact (TensorialAt.mkHom_apply
      (koszulFunctional_tensorialAt X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y)) hV_smooth).symm
  -- Rewrite the goal via `hRiesz`.
  have h_eq : (fun y : M =>
        koszulCovDeriv X.toFun Y.toFun y (X.smoothAt y) (Y.smoothAt y))
      = (fun y : M => metricRiesz y (Φ y)) := funext hRiesz
  rw [h_eq]
  -- Step 2: apply `metricRiesz_section_contMDiffAt_of_within` with α := x.
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) x]
    exact mem_chart_source H x
  refine TangentSmoothAt.mk
    ((Riemannian.Tensor.metricRiesz_section_contMDiffAt_of_within
      (g := hm.metric) (α := x) hx_base (Φ := Φ) ?_).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0))
  -- Step 3: per-j ContMDiffWithinAt for `y ↦ Φ y (chartBasisVecFiber x j y)` at `x`.
  -- Bump-extension approach: build a SmoothVectorField `Z̃ j` agreeing with
  -- `chartBasisVecFiber x j` on a neighbourhood of x. The koszulFunctional applied
  -- to globally-smooth `(X, Y, Z̃ j)` is globally smooth. On the agreement
  -- neighbourhood it equals the chartBasisVec version (via `koszulFunctional_local`).
  intro j
  -- Bump function at x.
  obtain ⟨bump⟩ : Nonempty (SmoothBumpFunction I x) := inferInstance
  -- Bumped global section: equal to `chartBasisVecFiber x j` near x, zero off
  -- `tsupport bump ⊆ (chartAt H x).source`.
  set chartBV : Π y : M, TangentSpace I y :=
    fun y => Riemannian.Tensor.chartBasisVecFiber (I := I) x j y with hchartBV_def
  set Ztilde : Π y : M, TangentSpace I y := fun y => bump y • chartBV y with hZtilde_def
  -- Smoothness of `Ztilde` as bundle section via `smul_section_of_tsupport`.
  have htsupp : tsupport bump ⊆ (chartAt H x).source :=
    bump.tsupport_subset_chartAt_source
  have htriv_base : (trivializationAt E (TangentSpace I) x).baseSet =
      (chartAt H x).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) x
  have hbump_smoothOn :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun y => bump y) (chartAt H x).source :=
    bump.contMDiff.contMDiffOn
  have hchartBV_smooth_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (chartBV y) :
        TotalSpace E (TangentSpace I : M → Type _)))
      (chartAt H x).source := by
    have := Riemannian.Tensor.chartBasisVec_contMDiffOn (I := I) x j
    rw [htriv_base] at this
    exact this
  have hZtilde_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (Ztilde y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    have hkey := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (s := chartBV) (ψ := fun y => bump y) (u := (chartAt H x).source)
      hbump_smoothOn (chartAt H x).open_source htsupp hchartBV_smooth_on
    -- `(ψ • s) y = bump y • chartBV y = Ztilde y` by `Pi.smul_apply'`.
    exact hkey
  -- Build `Z̃` as a SmoothVectorField.
  let Ztilde_VF : SmoothVectorField I M := ⟨Ztilde, hZtilde_smooth⟩
  -- On the open set `U := interior {b = 1}`, `Ztilde y = chartBV y`.
  let U : Set M := interior {y : M | bump y = 1}
  have hU_open : IsOpen U := isOpen_interior
  have hx_U : x ∈ U := by
    have hb1 : bump =ᶠ[nhds x] 1 := bump.eventuallyEq_one
    have hsub : {y | bump y = 1} ∈ nhds x := by
      filter_upwards [hb1] with y hy
      exact hy
    exact mem_interior_iff_mem_nhds.mpr hsub
  have hU_subset_base : U ⊆ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [htriv_base]
    refine subset_trans interior_subset ?_
    intro y hy
    have hy_eq : bump y = 1 := hy
    have hy_supp : y ∈ Function.support (fun z => bump z) := by
      simp only [Function.mem_support]; rw [hy_eq]; norm_num
    have : y ∈ tsupport bump := subset_tsupport _ hy_supp
    exact htsupp this
  have hbumpOne_in_nhd : ∀ y ∈ U, {z : M | bump z = 1} ∈ nhds y := by
    intro y hy
    exact mem_interior_iff_mem_nhds.mp hy
  -- Locality of koszulFunctional: on `U`, `koszulFunctional X Y Ztilde = koszulFunctional X Y chartBV`.
  have hZtilde_local : ∀ y ∈ U,
      koszulFunctional X.toFun Y.toFun Ztilde y
        = koszulFunctional X.toFun Y.toFun chartBV y := by
    intro y hy
    refine koszulFunctional_local X.toFun Y.toFun Ztilde chartBV y ?_
    filter_upwards [hbumpOne_in_nhd y hy] with z hz
    show bump z • chartBV z = chartBV z
    rw [show bump z = 1 from hz, one_smul]
  -- Smoothness of `y ↦ (1/2) * koszulFunctional X.toFun Y.toFun Ztilde y` globally.
  -- 6 koszul terms, each globally `ContMDiff` because X, Y, Z̃ are all SmoothVectorFields.
  -- (i) Inner-product smoothness for ⟨Y, Z̃⟩, ⟨Z̃, X⟩, ⟨X, Y⟩.
  have h_YZtilde_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' => hm.metric.metricInner y' (Y.toFun y') (Ztilde y')) :=
    metricInner_contMDiff Y.smooth hZtilde_smooth
  have h_ZtildeX_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' => hm.metric.metricInner y' (Ztilde y') (X.toFun y')) :=
    metricInner_contMDiff hZtilde_smooth X.smooth
  have h_XY_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' => hm.metric.metricInner y' (X.toFun y') (Y.toFun y')) :=
    metricInner_contMDiff X.smooth Y.smooth
  -- (ii) Three directional derivative terms via `mfderiv_apply_section_contMDiff`.
  have hT1_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => directionalDeriv (fun y' => metricInner y' (Y.toFun y') (Ztilde y')) y
        (X.toFun y)) := by
    unfold directionalDeriv
    exact Riemannian.Tensor.mfderiv_apply_section_contMDiff (I := I)
      h_YZtilde_inner X.smooth
  have hT2_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => directionalDeriv (fun y' => metricInner y' (Ztilde y') (X.toFun y')) y
        (Y.toFun y)) := by
    unfold directionalDeriv
    exact Riemannian.Tensor.mfderiv_apply_section_contMDiff (I := I)
      h_ZtildeX_inner Y.smooth
  have hT3_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => directionalDeriv (fun y' => metricInner y' (X.toFun y') (Y.toFun y')) y
        (Ztilde y)) := by
    unfold directionalDeriv
    exact Riemannian.Tensor.mfderiv_apply_section_contMDiff (I := I)
      h_XY_inner hZtilde_smooth
  -- (iii) Three Lie bracket terms via Mathlib `ContMDiffAt.mlieBracket_vectorField`.
  -- Need `IsManifold I (minSmoothness ℝ 2) M` and `IsManifold I (∞ + 1) M`
  -- (both reduce to `IsManifold I ∞ M`) for the bracket smoothness lemma.
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI hIM_succ : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h_eq : (∞ : ℕ∞ω) + 1 = ∞ := by
      change ((⊤ : ℕ∞) : ℕ∞ω) + (1 : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω)
      rfl
    rw [h_eq]
    infer_instance
  have h_brXY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (mlieBracket I X.toFun Y.toFun y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    intro y
    exact X.smooth.contMDiffAt.mlieBracket_vectorField Y.smooth.contMDiffAt (by simp)
  have h_brYZtilde_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (mlieBracket I Y.toFun Ztilde y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    intro y
    exact Y.smooth.contMDiffAt.mlieBracket_vectorField hZtilde_smooth.contMDiffAt (by simp)
  have h_brXZtilde_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (mlieBracket I X.toFun Ztilde y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    intro y
    exact X.smooth.contMDiffAt.mlieBracket_vectorField hZtilde_smooth.contMDiffAt (by simp)
  have hT4_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => metricInner y (mlieBracket I X.toFun Y.toFun y) (Ztilde y)) :=
    metricInner_contMDiff h_brXY_smooth hZtilde_smooth
  have hT5_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => metricInner y (mlieBracket I Y.toFun Ztilde y) (X.toFun y)) :=
    metricInner_contMDiff h_brYZtilde_smooth X.smooth
  have hT6_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => metricInner y (mlieBracket I X.toFun Ztilde y) (Y.toFun y)) :=
    metricInner_contMDiff h_brXZtilde_smooth Y.smooth
  -- Sum: koszulFunctional X.toFun Y.toFun Ztilde y is globally ContMDiff.
  have hKoszul_Ztilde_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => koszulFunctional X.toFun Y.toFun Ztilde y) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y =>
      directionalDeriv (fun y' => metricInner y' (Y.toFun y') (Ztilde y')) y (X.toFun y)
      + directionalDeriv (fun y' => metricInner y' (Ztilde y') (X.toFun y')) y (Y.toFun y)
      - directionalDeriv (fun y' => metricInner y' (X.toFun y') (Y.toFun y')) y (Ztilde y)
      + metricInner y (mlieBracket I X.toFun Y.toFun y) (Ztilde y)
      - metricInner y (mlieBracket I Y.toFun Ztilde y) (X.toFun y)
      - metricInner y (mlieBracket I X.toFun Ztilde y) (Y.toFun y))
    exact ((((hT1_smooth.add hT2_smooth).sub hT3_smooth).add hT4_smooth).sub
      hT5_smooth).sub hT6_smooth
  -- ContMDiffOn on U for the chartBV version (via koszulFunctional_local).
  have hKoszul_chartBV_on_U :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => (1 / 2 : ℝ) * koszulFunctional X.toFun Y.toFun chartBV y) U := by
    have hKoszulZtilde_half : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => (1 / 2 : ℝ) * koszulFunctional X.toFun Y.toFun Ztilde y) U :=
      (contMDiffOn_const.mul hKoszul_Ztilde_smooth.contMDiffOn)
    refine hKoszulZtilde_half.congr ?_
    intro y hy
    rw [hZtilde_local y hy]
  -- Lift to ContMDiffAt at x.
  have hKoszul_chartBV_at_x :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y => (1 / 2 : ℝ) * koszulFunctional X.toFun Y.toFun chartBV y) x :=
    (hKoszul_chartBV_on_U x hx_U).contMDiffAt (hU_open.mem_nhds hx_U)
  -- Identify with `Φ y (chartBasisVecFiber x j y)` on baseSet via TensorialAt.mkHom.
  have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hPhi_eq : ∀ y ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      Φ y (chartBV y)
        = (1 / 2 : ℝ) * koszulFunctional X.toFun Y.toFun chartBV y := by
    intro y hy
    have hy_chart : y ∈ (chartAt H x).source := by rw [← htriv_base]; exact hy
    -- chartBasisVec x j is TangentSmoothAt at y (since y ∈ baseSet).
    have hchartBV_smoothAt : TangentSmoothAt chartBV y := by
      refine TangentSmoothAt.mk ?_
      exact (hchartBV_smooth_on.contMDiffAt
        ((chartAt H x).open_source.mem_nhds hy_chart)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    exact TensorialAt.mkHom_apply
      (koszulFunctional_tensorialAt X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y)) hchartBV_smoothAt
  -- Conclude ContMDiffWithinAt at x for `Φ y (chartBasisVecFiber x j y)`.
  have hPhi_chartBV_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => Φ y (chartBV y)) x := by
    refine hKoszul_chartBV_at_x.congr_of_eventuallyEq ?_
    filter_upwards [hbaseSet_open.mem_nhds hx_base] with y hy
    exact hPhi_eq y hy
  exact hPhi_chartBV_at.contMDiffWithinAt

/-- **Eng.** Constant-direction specialisation of
`koszulCovDeriv_smoothVF_smoothAt` via `SmoothVectorField.const v`. -/
private theorem koszulCovDeriv_const_smoothAt
    [IsLocallyConstantChartedSpace H M]
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => koszulCovDeriv (fun _ : M => v) Y.toFun y
        ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        (Y.smoothAt y)) x :=
  koszulCovDeriv_smoothVF_smoothAt (SmoothVectorField.const v) Y x

/-- **Math.** **Existence theorem for the Levi-Civita connection.**

On a Riemannian manifold there exists a covariant derivative on the
tangent bundle that is torsion-free, metric-compatible (for smooth
$X, Y, Z$), and produces smooth sections under smooth inputs:
`(X, Y) ↦ ∇_X Y` carries `SmoothVectorField × SmoothVectorField` to
`TangentSmoothAt` at every point. The smoothness clause is the form
required by downstream curvature identities (Bochner stack).

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (existence + uniqueness
via the Koszul formula); Lee 2018 Prop. 4.26 (smoothness on smooth
manifolds). -/
theorem leviCivitaConnection_exists [IsLocallyConstantChartedSpace H M] :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      cov.torsion = 0 ∧
      (∀ (X Y Z : Π x : M, TangentSpace I x) (x : M)
        (_hX : TangentSmoothAt X x) (_hY : TangentSmoothAt Y x)
        (_hZ : TangentSmoothAt Z x),
        mfderiv I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x (X x) =
          metricInner x (cov.toFun Y x (X x)) (Z x) +
          metricInner x (Y x) (cov.toFun Z x (X x))) ∧
      (∀ (X Y : SmoothVectorField I M) (x : M),
        TangentSmoothAt
          (fun y : M => cov.toFun Y.toFun y (X.toFun y)) x) := by
  obtain ⟨cov, hcov⟩ := koszulLeviCivita_exists (I := I) (M := M)
  refine ⟨cov, ?_, ?_, ?_⟩
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
  · -- Smoothness clause (smooth-VF direction): reduce via `hcov` eq spec
    -- to smoothness of `(fun y => koszulCovDeriv X.toFun Y.toFun y _ _)`,
    -- then forward to `koszulCovDeriv_smoothVF_smoothAt`.
    intro X Y x
    have h_eq : (fun y : M => cov.toFun Y.toFun y (X.toFun y))
        = (fun y : M => koszulCovDeriv X.toFun Y.toFun y
            (X.smoothAt y) (Y.smoothAt y)) := by
      funext y
      exact hcov X.toFun Y.toFun y (X.smoothAt y) (Y.smoothAt y)
    rw [h_eq]
    exact koszulCovDeriv_smoothVF_smoothAt X Y x

/-- **Math.** The **Levi-Civita connection** $\nabla$ on the tangent
bundle of a Riemannian manifold: the unique torsion-free,
metric-compatible covariant derivative. Real `noncomputable def` via
`Classical.choose` over `leviCivitaConnection_exists`.

**Ground truth**: do Carmo 1992 §2 (Koszul formula gives uniqueness). -/
noncomputable def leviCivitaConnection
    [IsLocallyConstantChartedSpace H M] :
    CovariantDerivative I E (fun x : M => TangentSpace I x) :=
  Classical.choose (leviCivitaConnection_exists (I := I) (M := M))

/-- **Math.** The Levi-Civita connection is torsion-free. -/
theorem leviCivitaConnection_torsion_zero
    [IsLocallyConstantChartedSpace H M] :
    (leviCivitaConnection : CovariantDerivative I E
      (fun x : M => TangentSpace I x)).torsion = 0 :=
  (Classical.choose_spec leviCivitaConnection_exists).1

/-- **Math.** The Levi-Civita connection is **metric-compatible** for
smooth $X, Y, Z$ at $x$:
$$\nabla_X \langle Y, Z \rangle (x) =
  \langle \nabla_X Y, Z \rangle (x) + \langle Y, \nabla_X Z \rangle (x).$$
Metric is the framework-owned `metricInner`. Smoothness hypotheses match
do Carmo 1992 §2 Theorem 3.6. -/
theorem leviCivitaConnection_metric_compatible
    [IsLocallyConstantChartedSpace H M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x (X x) =
      metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Y x (X x)) (Z x) +
      metricInner x (Y x)
        ((leviCivitaConnection (I := I) (M := M)).toFun Z x (X x)) :=
  (Classical.choose_spec leviCivitaConnection_exists).2.1 X Y Z x hX hY hZ

/-- **Math.** Smoothness of the Levi-Civita connection along a smooth
direction: for `X, Y : SmoothVectorField I M`, the section
`y ↦ ∇_{X(y)} Y(y)` is smooth at every point. Direct projection from
the 3rd conjunct of `leviCivitaConnection_exists`. -/
theorem leviCivitaConnection_smoothAt_smoothVF_dir
    [IsLocallyConstantChartedSpace H M]
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => (leviCivitaConnection (I := I) (M := M)).toFun Y.toFun y
        (X.toFun y)) x :=
  (Classical.choose_spec leviCivitaConnection_exists).2.2 X Y x

/-- **Mixed.** Constant-direction specialisation: for `v : E` and
`Y : SmoothVectorField I M`, the section `y ↦ ∇ Y y v` is smooth.
Math: smoothness of `∇Y` is symmetric in direction. Eng: backward-
compatible accessor over `leviCivitaConnection_smoothAt_smoothVF_dir`
with `X := SmoothVectorField.const v`. -/
theorem leviCivitaConnection_smoothAt_const_dir
    [IsLocallyConstantChartedSpace H M]
    (Y : SmoothVectorField I M) (v : E) (x : M) :
    TangentSmoothAt
      (fun y : M => (leviCivitaConnection (I := I) (M := M)).toFun Y.toFun y v) x :=
  leviCivitaConnection_smoothAt_smoothVF_dir
    (SmoothVectorField.const v) Y x

/-- **Math.** **Covariant derivative of one vector field along another**:
$(\nabla_X Y)(x) := \nabla\,Y\,x\,(X\,x)$, where $\nabla$ is the
Levi-Civita connection. Torsion-free and metric-compatible w.r.t.
`metricInner`.

**Ground truth**: do Carmo 1992 §2 Definition 2.1. -/
noncomputable def covDeriv
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  ((leviCivitaConnection (I := I) (M := M)).toFun Y x) (X x)

/-- **Math.** Notation `∇[X] Y` for `covDeriv X Y`. -/
scoped[Riemannian] notation:max "∇[" X "] " Y:max => covDeriv X Y

/-- **Math.** Notation `⟦X, Y⟧` for the manifold Lie bracket
`mlieBracket _ X Y` (model `I` inferred from section types). -/
scoped[Riemannian] notation:max "⟦" X ", " Y "⟧" =>
  VectorField.mlieBracket _ X Y

/-- **Mixed.** Covariant derivative at a point as a continuous linear map in the direction
slot: $\nabla\,Y|_x : T_xM \to_L T_xM$, $v \mapsto (\nabla_v Y)(x)$.
Math: pointwise linearity in direction. Eng: decouples direction-linearity
from section-level `covDeriv` so identities reduce to standard continuous linear map lemmas. -/
noncomputable def covDerivAt
    [IsLocallyConstantChartedSpace H M]
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (leviCivitaConnection (I := I) (M := M)).toFun Y x

/-- **Eng.** `covDeriv X Y x = covDerivAt Y x (X x)`: section-level
`covDeriv` factors through the pointwise continuous linear map `covDerivAt`. -/
@[simp]
theorem covDeriv_eq_covDerivAt
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    covDeriv X Y x = covDerivAt Y x (X x) :=
  rfl

/-- **Eng.** Constant-section specialization:
`covDeriv (fun _ => v) Y x = covDerivAt Y x v`. -/
@[simp]
theorem covDeriv_const_eq_covDerivAt
    [IsLocallyConstantChartedSpace H M]
    (v : E) (Y : Π x : M, TangentSpace I x) (x : M) :
    covDeriv (fun _ : M => v) Y x = covDerivAt Y x v :=
  rfl

/-- **Math.** **Riesz formula for the covariant derivative**: for smooth
$X, Y, Z$,
$$\langle \nabla_X Y, Z\rangle_g(x) = \tfrac12 K(X, Y; Z)(x).$$
Cycling metric-compat over $(X, Y, Z)$, $(Y, Z, X)$, $(Z, X, Y)$ and
substituting torsion-freeness isolates $\langle \nabla_X Y, Z\rangle$. -/
private theorem covDeriv_inner_eq_half_koszul
    [IsLocallyConstantChartedSpace H M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    metricInner x (covDeriv X Y x) (Z x)
      = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  -- Notation: write `cov A B := leviCivitaConnection.toFun B x (A x)` (= covDeriv A B x).
  -- We'll identify these via `show` against the unfolded form and use linarith.
  -- Spec from Classical.choose: torsion-free + metric-compat for smooth fields.
  obtain ⟨h_tors, h_compat, _h_smooth⟩ := Classical.choose_spec
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

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
omit [CompleteSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
/-- **Math.** **Locality of `koszulFunctional` in the middle argument**:
if $Y_1 =ᶠ[𝓝 x] Y_2$, then $K(X, Y_1; Z)(x) = K(X, Y_2; Z)(x)$. -/
private theorem koszulFunctional_eventuallyEq_middle
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

/-- **Math.** **Locality of `covDeriv` in the middle argument** (Riesz
uniqueness): if $Y_1 =ᶠ[𝓝 x] Y_2$ and both are smooth at $x$, then for
smooth $X$, $\nabla_X Y_1(x) = \nabla_X Y_2(x)$. -/
private theorem covDeriv_congr_eventuallyEq_middle
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

/-! ## from `Connection.lean` (Bianchi section) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-! ## Framework helpers

Three pointwise lemmas exposed from the Levi-Civita connection's
`CovariantDerivative` structure: torsion-freeness, additivity in the
differentiated field, and subtractivity (corollary). -/

/-- **Math.** Pointwise torsion-freeness of the Levi-Civita connection:
$\nabla_X Y - \nabla_Y X = [X, Y]$ at any point where $X, Y$ are
differentiable as bundle sections. -/
theorem covDeriv_sub_swap_eq_mlieBracket
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    (∇[X] Y) x - (∇[Y] X) x = (⟦X, Y⟧) x :=
  (CovariantDerivative.torsion_eq_zero_iff
    (cov := leviCivitaConnection (I := I) (M := M))).mp
    leviCivitaConnection_torsion_zero hX hY

/-- **Math.** Additivity of `covDeriv` in the differentiated field:
$\nabla_X (Y_1 + Y_2)(x) = \nabla_X Y_1(x) + \nabla_X Y_2(x)$ for
$Y_1, Y_2$ smooth at $x$. -/
theorem covDeriv_add_field
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x) :
    (∇[X] (Y₁ + Y₂)) x = (∇[X] Y₁) x + (∇[X] Y₂) x := by
  have h := leviCivitaConnection.isCovariantDerivativeOnUniv.add (σ := Y₁) (σ' := Y₂)
    (x := x) hY₁ hY₂
  show (leviCivitaConnection.toFun (Y₁ + Y₂) x) (X x)
    = (leviCivitaConnection.toFun Y₁ x) (X x) + (leviCivitaConnection.toFun Y₂ x) (X x)
  rw [h]
  rfl

/-- **Math.** Locality of `covDeriv` in the differentiated field: if
$Y_1 =ᶠ[𝓝 x] Y_2$ and both are smooth at $x$, then
$\nabla_X Y_1(x) = \nabla_X Y_2(x)$. Smoothness of $X$ is not required
(the connection is continuous linear map in the direction slot). -/
theorem covDeriv_congr_eventuallyEq_field
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    (∇[X] Y₁) x = (∇[X] Y₂) x := by
  show (leviCivitaConnection.toFun Y₁ x) (X x)
      = (leviCivitaConnection.toFun Y₂ x) (X x)
  rw [leviCivitaConnection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hY₁ hY₂ Filter.univ_mem h]

/-- **Math.** `covDeriv` of a constant scalar multiple:
$\nabla_X (a \cdot Y)(x) = a \cdot \nabla_X Y(x)$ for $a : \mathbb{R}$. -/
theorem covDeriv_smul_const_field
    (X Y : Π x : M, TangentSpace I x) (x : M) (a : ℝ)
    (hY : TangentSmoothAt Y x) :
    (∇[X] (a • Y)) x = a • (∇[X] Y) x := by
  have h := leviCivitaConnection.isCovariantDerivativeOnUniv.smul_const (σ := Y)
    (x := x) a hY
  show (leviCivitaConnection.toFun (a • Y) x) (X x)
    = a • (leviCivitaConnection.toFun Y x) (X x)
  rw [h]
  rfl

/-- **Math.** Subtractivity of `covDeriv` in the differentiated field:
$\nabla_X (Y_1 - Y_2)(x) = \nabla_X Y_1(x) - \nabla_X Y_2(x)$. -/
theorem covDeriv_sub_field
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x) :
    (∇[X] (Y₁ - Y₂)) x = (∇[X] Y₁) x - (∇[X] Y₂) x := by
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

/-- **Math.** Leibniz rule: the connection acts as a derivation in the
scalar factor of `g • Y`:
$$\nabla_X (g \cdot Y)(x) = g(x) \cdot \nabla_X Y(x) + (\mathrm{d}g \cdot X)(x) \cdot Y(x).$$ -/
theorem covDeriv_smul_scalar_field
    (X : Π y : M, TangentSpace I y)
    (g : M → ℝ) (Y : Π y : M, TangentSpace I y) (x : M)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x)
    (hY : TangentSmoothAt Y x) :
    covDeriv X (g • Y) x
      = g x • covDeriv X Y x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g x (X x)) • Y x := by
  have h := leviCivitaConnection.isCovariantDerivativeOnUniv.leibniz
    (σ := Y) (g := g) (x := x) hY hg trivial
  -- h : leviCivitaConnection.toFun (g • Y) x
  --     = g x • leviCivitaConnection.toFun Y x + (extDerivFun g x).smulRight (Y x)
  show (leviCivitaConnection.toFun (g • Y) x) (X x) = _
  rw [h]
  show g x • (leviCivitaConnection.toFun Y x) (X x)
      + ((extDerivFun g x).smulRight (Y x)) (X x)
    = g x • (leviCivitaConnection.toFun Y x) (X x)
      + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g x (X x)) • Y x
  -- `((extDerivFun g x).smulRight (Y x)) v = (extDerivFun g x v) • Y x` (def-eq).
  -- `extDerivFun g x v = mfderiv g x v` via `NormedSpace.fromTangentSpace` identity
  -- on the scalar tangent space `TangentSpace 𝓘(ℝ, ℝ) (g x) ≃L ℝ`.
  congr 1

/-! ## Riemann curvature tensor (connection-level definition)

The Riemann curvature tensor depends only on $\nabla$ (and the Lie
bracket) — no metric required. We place its definition here at the
connection-level layer so Bianchi I can reference it without circular
import. Metric-dependent extensions (Ricci as trace, full $(0,4)$-symmetry,
sectional curvature) live in `Riemannian.Curvature`. -/

/-- **Math.** The **Riemann curvature tensor**:
$R(X, Y)Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.
Connection-level definition (no metric). Metric-dependent extensions
(full antisymmetry, Ricci as trace, sectional curvature) live in
`Riemannian.Curvature`.

**Ground truth**: do Carmo 1992 §4 Definition 2.1. -/
noncomputable def riemannCurvature
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  covDeriv X (covDeriv Y Z) x - covDeriv Y (covDeriv X Z) x
    - covDeriv (mlieBracket I X Y) Z x

/-- **Math.** Notation `Riem(X, Y) Z` for `riemannCurvature X Y Z`. -/
scoped[Riemannian] notation:max "Riem(" X ", " Y ") " Z:max =>
  riemannCurvature X Y Z

/-! ### `riem_simp` lemmas

Two rewrites that drive the `riem_simp` simp set, populated for the
Riemann curvature operator built from the framework's `covDeriv`. Together
with `abel` they discharge the algebraic identities of `riemannCurvature`
without exposing the underlying connection plumbing. -/

/-- **Eng.** Definitional unfold of `riemannCurvature` to its
$\nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$ form
for the `riem_simp` simp set. Pure rewrite — no hypotheses. -/
@[riem_simp]
theorem riemannCurvature_def
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x
      = covDeriv X (covDeriv Y Z) x - covDeriv Y (covDeriv X Z) x
        - covDeriv (VectorField.mlieBracket I X Y) Z x := rfl

/-- **Math.** Lie-bracket antisymmetry through the direction slot:
$\nabla_{[Y,X]} Z = -\nabla_{[X,Y]} Z$ pointwise. Used as explicit `rw`
step (kept out of `riem_simp` to avoid the $X \leftrightarrow Y$ loop). -/
theorem covDeriv_mlieBracket_swap_apply
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    covDeriv (VectorField.mlieBracket I Y X) Z x
      = -covDeriv (VectorField.mlieBracket I X Y) Z x := by
  unfold covDeriv
  rw [show mlieBracket I Y X x = -mlieBracket I X Y x from
        VectorField.mlieBracket_swap_apply,
      (leviCivitaConnection.toFun Z x).map_neg]

-- riemannCurvature_antisymm lives in Curvature.lean: its statement
-- uses the post-Bianchi `Riem(X, Y) Z` notation, so it must be in a
-- file that imports `Util/Notation/Curvature`.

/-! ## Algebraic Bianchi I

Under **global** smoothness of `X, Y, Z` (i.e. `∀ y, TangentSmoothAt _ y`),
the torsion-free identity lifts from pointwise to a **section-level
equality** (Pi-equality via `funext`):

  `(fun y => covDeriv Y Z y) = (fun y => covDeriv Z Y y) + mlieBracket I Y Z`

This bypasses any locality / nbhd-congruence lemma — once the sections
are literally equal as Π-functions, `covDeriv X (·) x` accepts the
substitution directly.

The two derivations needed at section level: -/

/-- **Eng.** Section-level torsion-freeness: under global smoothness, the
pointwise torsion-free identity lifts to a Π-equality, enabling direct
substitution under `covDeriv X (·) x`. -/
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

/-- **Math.** **Algebraic (first) Bianchi identity** for the Levi-Civita
connection:
$$R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0.$$
The explicit smoothness hypotheses on $X, Y, Z$, their first
covariant derivatives, and their pairwise Lie brackets match the
standard $C^2$ textbook setup but fire pointwise.

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

/-! ## from `Connection.lean` (smoothness section) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Math.** $\nabla_{\,\mathrm{const}\,v}\, Y$ is smooth at every $x$
for any `SmoothVectorField Y` and any constant direction $v : E$. -/
theorem covDeriv_const_smoothVF_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => covDeriv (fun _ : M => v) Y.toFun y) x :=
  Riemannian.leviCivitaConnection_smoothAt_const_dir Y v x

/-- **Math.** $\nabla_X Y$ is smooth at every $x$ for any smooth vector
fields `X, Y : SmoothVectorField I M`. Smooth-VF-direction strengthening
of `covDeriv_const_smoothVF_smoothAt`. -/
theorem covDeriv_smoothVF_smoothAt
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => covDeriv X.toFun Y.toFun y) x :=
  Riemannian.leviCivitaConnection_smoothAt_smoothVF_dir X Y x

end Riemannian
