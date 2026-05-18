import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import OpenGALib.Riemannian.Manifold.SmoothManifold
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.TensorBundle.MusicalIso
import OpenGALib.Riemannian.Util.TangentHelpers
import OpenGALib.Riemannian.Connection.Koszul
import OpenGALib.Riemannian.Connection.RieszExtraction
import OpenGALib.Riemannian.Util.CovDerivSmoothness
import OpenGALib.Riemannian.Util.MetricInnerSmoothness
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
-- Smoothness of `g.metricInner` on bundle sections lives in `Manifold.lean`
-- as the public `Riemannian.g.metricInner_contMDiff` (parametric over `n`).

/-! ## from `Connection.lean` (LeviCivita section) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-! ## Riesz extraction stack (`Connection/RieszExtraction.lean`)

The pointwise value $\nabla_X Y(x) \in T_xM$ is built in
`Connection/RieszExtraction.lean` as the Riesz representative of the
half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$.
`koszulCovDeriv` and its defining identity `koszulCovDeriv_inner_eq`
feed the construction of `leviCivitaConnection` below.
-/

/-! ## Levi-Civita closure via Koszul + Riesz

`leviCivitaConnection_exists` is closed by combining:

* `koszulLeviCivita_exists` — real `CovariantDerivative` whose `toFun`
  extends the pointwise Koszul value for smooth inputs. Construction:
  `TensorialAt.mkHom` over `koszulCovDerivAux` (smoothness-erased
  variant), with tensoriality via Riesz uniqueness against
  `g.metricInner_eq_iff_eq`. Real proof, no `sorry`.
* `koszul_antisymm` → torsion-free via `g.metricInner_eq_iff_eq` +
  `koszulCovDeriv_inner_eq` + Mathlib's `FiberBundle.extend`.
* `koszul_metric_compat_sum` → metric-compatibility for smooth vector
  fields. -/

/-! ### Construction of the Levi-Civita `CovariantDerivative`

Build the `CovariantDerivative` via the smoothness-erased aux and its
tensoriality from `Connection/CovDerivSmoothness.lean`:

1. `koszulCovDerivAux g Y x hY` — smoothness-erased function `(X) ↦ ∇_X Y(x)`,
   defined as `koszulCovDeriv g X Y x hX hY` for smooth `X` and `0` otherwise.
2. `koszulCovDerivAux_tensorialAt` — tensorality in `X` (the
   `C^∞`-linearity of $\nabla_\cdot Y$ at $x$), via `koszul_smul_left` /
   `koszul_add_left` + Riesz uniqueness.
3. `TensorialAt.mkHom` to obtain the continuous linear map `T_xM →L[ℝ] T_xM`.
4. `IsCovariantDerivativeOn` add / leibniz from `koszul_add_middle` /
   `koszul_smul_middle` via Riesz uniqueness.
-/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] in
/-- **Math.** **Levi-Civita `CovariantDerivative` existence.** Builds a
`CovariantDerivative` whose `toFun` extends `koszulCovDeriv` for smooth
$(X, Y)$. `IsCovariantDerivativeOn.add` follows from `koszul_add_middle`
via Riesz uniqueness; `IsCovariantDerivativeOn.leibniz` from
`koszul_smul_middle` (the $2 \cdot X(g) \cdot \langle Y, Z\rangle$ term
matches `(extDerivFun g x).smulRight (Y x)` after the $\tfrac12$ factor
cancels). -/
private theorem koszulLeviCivita_exists (g : RiemannianMetric I M) :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      ∀ (X Y : VectorFieldSection I M) (x : M)
        (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x),
        cov.toFun Y x (X x) = koszulCovDeriv g X Y x hX hY := by
  classical
  -- Step 1: build cov.toFun Y x as the mkHom continuous linear map for smooth Y, else 0.
  let toFun : (VectorFieldSection I M) →
      (Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun Y x =>
      if hY : TangentSmoothAt Y x then
        TensorialAt.mkHom (koszulCovDerivAux g Y x hY) x
          (koszulCovDerivAux_tensorialAt g Y x hY)
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
      set V : VectorFieldSection I M := FiberBundle.extend E v
      have hV_smooth : TangentSmoothAt V x :=
        FiberBundle.mdifferentiableAt_extend I E v
      have hVx : V x = v := FiberBundle.extend_apply_self _ _
      rw [ContinuousLinearMap.add_apply]
      rw [← hVx]
      rw [TensorialAt.mkHom_apply _ hV_smooth,
          TensorialAt.mkHom_apply _ hV_smooth,
          TensorialAt.mkHom_apply _ hV_smooth]
      -- Goal: koszulCovDerivAux g (Y₁+Y₂) x h_sum V
      --     = koszulCovDerivAux g Y₁ x hY₁ V + koszulCovDerivAux g Y₂ x hY₂ V
      simp only [koszulCovDerivAux, dif_pos hV_smooth]
      -- Goal: koszulCovDeriv g V (Y₁+Y₂) x ... = koszulCovDeriv g V Y₁ x ... + koszulCovDeriv g V Y₂ x ...
      apply (g.metricInner_eq_iff_eq x _ _).mp
      intro Z₀
      set Z : VectorFieldSection I M := FiberBundle.extend E Z₀
      have hZ_smooth : TangentSmoothAt Z x :=
        FiberBundle.mdifferentiableAt_extend I E Z₀
      have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
      have h_Y₁Z := g.metricInner_mdifferentiableAt hY₁ hZ_smooth
      have h_Y₂Z := g.metricInner_mdifferentiableAt hY₂ hZ_smooth
      have h_VY₁ := g.metricInner_mdifferentiableAt hV_smooth hY₁
      have h_VY₂ := g.metricInner_mdifferentiableAt hV_smooth hY₂
      rw [← hZx]
      simp only [koszulCovDeriv_inner_eq g _ _ _ x hV_smooth h_sum hZ_smooth,
          koszul_add_middle g V Y₁ Y₂ Z x h_Y₁Z h_Y₂Z h_VY₁ h_VY₂ hY₁ hY₂,
          g.metricInner_add_left,
          koszulCovDeriv_inner_eq g V Y₁ Z x hV_smooth hY₁ hZ_smooth,
          koszulCovDeriv_inner_eq g V Y₂ Z x hV_smooth hY₂ hZ_smooth]
      ring
    case leibniz =>
      -- toFun (f • Y) x = f x • toFun Y x + (extDerivFun f x).smulRight (Y x)
      intro Y f x hY hf _
      have hY' : TangentSmoothAt Y x := hY
      have h_fY_lambda : TangentSmoothAt (fun y => f y • Y y) x :=
        TangentSmoothAt.smul hf hY'
      -- Note: f • Y = fun y => f y • Y y (Pi-smul, definitionally)
      have h_fY' : TangentSmoothAt (f • Y) x := h_fY_lambda
      simp only [toFun, dif_pos hY', dif_pos h_fY']
      ext v
      set V : VectorFieldSection I M := FiberBundle.extend E v
      have hV_smooth : TangentSmoothAt V x :=
        FiberBundle.mdifferentiableAt_extend I E v
      have hVx : V x = v := FiberBundle.extend_apply_self _ _
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      rw [← hVx]
      rw [TensorialAt.mkHom_apply _ hV_smooth,
          TensorialAt.mkHom_apply _ hV_smooth]
      simp only [koszulCovDerivAux, dif_pos hV_smooth]
      -- Goal: koszulCovDeriv g V (f•Y) x ... = f x • koszulCovDeriv g V Y x ... +
      --       (extDerivFun f x).smulRight (Y x) v
      apply (g.metricInner_eq_iff_eq x _ _).mp
      intro Z₀
      set Z : VectorFieldSection I M := FiberBundle.extend E Z₀
      have hZ_smooth : TangentSmoothAt Z x :=
        FiberBundle.mdifferentiableAt_extend I E Z₀
      have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
      have h_YZ := g.metricInner_mdifferentiableAt hY hZ_smooth
      have h_VY := g.metricInner_mdifferentiableAt hV_smooth hY
      rw [← hZx]
      simp only [koszulCovDeriv_inner_eq g _ _ _ x hV_smooth h_fY' hZ_smooth]
      -- LHS = (1/2) * koszulFunctional g V (f • Y) Z x
      -- by koszul_smul_middle:
      --     = (1/2) * (f x * K V Y Z x + 2 * directionalDeriv f x (V x) * ⟨Y x, Z x⟩)
      rw [show (f • Y : VectorFieldSection I M) = fun y => f y • Y y from rfl]
      rw [koszul_smul_middle g V Y Z f x hf h_YZ h_VY hY]
      -- RHS expands via koszulCovDeriv_inner_eq g V Y Z and g.metricInner_add/smul.
      simp only [g.metricInner_add_left, g.metricInner_smul_left,
          koszulCovDeriv_inner_eq g V Y Z x hV_smooth hY hZ_smooth]
      -- Remaining goal (modulo extDerivFun = directionalDeriv):
      -- (1/2) * (f x * K V Y Z + 2 * dDeriv f x (V x) * ⟨Y x, Z x⟩)
      --   = f x * (1/2) * K V Y Z + (extDerivFun f x).smulRight (Y x) v • Z x
      show (1 / 2 : ℝ) *
          (f x * koszulFunctional g V Y Z x
            + 2 * directionalDeriv f x (V x) * g.metricInner x (Y x) (Z x))
          = f x *
              ((1 / 2 : ℝ) * koszulFunctional g V Y Z x)
            + g.metricInner x ((extDerivFun f x).smulRight (Y x) (V x)) (Z x)
      -- Unfold extDerivFun and smulRight at (V x).
      have h_smulRight :
          ((extDerivFun (I := I) f x).smulRight (Y x) (V x) : TangentSpace I x)
            = directionalDeriv f x (V x) • Y x := by
        show (extDerivFun (I := I) f x (V x)) • Y x
            = directionalDeriv f x (V x) • Y x
        rfl
      rw [h_smulRight, g.metricInner_smul_left]
      ring
  -- Step 3: prove the main equation cov.toFun Y x (X x) = koszulCovDeriv g X Y x hX hY.
  · intro X Y x hX hY
    show toFun Y x (X x) = koszulCovDeriv g X Y x hX hY
    simp only [toFun, dif_pos hY]
    rw [TensorialAt.mkHom_apply _ hX]
    -- Goal: koszulCovDerivAux g Y x hY X = koszulCovDeriv g X Y x hX hY
    simp only [koszulCovDerivAux, dif_pos hX]

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
theorem leviCivitaConnection_exists (g : RiemannianMetric I M) :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      cov.torsion = 0 ∧
      (∀ (X Y Z : VectorFieldSection I M) (x : M)
        (_hX : TangentSmoothAt X x) (_hY : TangentSmoothAt Y x)
        (_hZ : TangentSmoothAt Z x),
        mfderiv I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y y) (Z y)) x (X x) =
          g.metricInner x (cov.toFun Y x (X x)) (Z x) +
          g.metricInner x (Y x) (cov.toFun Z x (X x))) ∧
      (∀ (X Y : SmoothVectorField I M) (x : M),
        TangentSmoothAt
          (fun y : M => cov.toFun Y.toFun y (X.toFun y)) x) := by
  obtain ⟨cov, hcov⟩ := koszulLeviCivita_exists (I := I) (M := M) g
  refine ⟨cov, ?_, ?_, ?_⟩
  · -- Torsion = 0
    rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x hX hY
    rw [hcov X Y x hX hY, hcov Y X x hY hX]
    apply (g.metricInner_eq_iff_eq x _ _).mp
    intro Z₀
    set Z : VectorFieldSection I M := FiberBundle.extend E Z₀ with hZ_def
    have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
    have hZ_smooth : TangentSmoothAt Z x :=
      FiberBundle.mdifferentiableAt_extend I E Z₀
    rw [← hZx]
    simp only [g.metricInner_sub_left,
        koszulCovDeriv_inner_eq g X Y Z x hX hY hZ_smooth,
        koszulCovDeriv_inner_eq g Y X Z x hY hX hZ_smooth]
    -- Goal: 1/2 * K X Y Z x - 1/2 * K Y X Z x = g.metricInner x (mlieBracket I X Y x) (Z x)
    have h := koszul_antisymm g X Y Z x
    -- h: K X Y Z x - K Y X Z x = 2 * g.metricInner x (mlieBracket I X Y x) (Z x)
    linarith
  · -- Metric-compat for smooth X, Y, Z
    intro X Y Z x hX hY hZ
    rw [hcov X Y x hX hY, hcov X Z x hX hZ]
    rw [show g.metricInner x (Y x) (koszulCovDeriv g X Z x hX hZ) =
        g.metricInner x (koszulCovDeriv g X Z x hX hZ) (Y x) from
      g.metricInner_comm x _ _]
    simp only [koszulCovDeriv_inner_eq g X Y Z x hX hY hZ,
        koszulCovDeriv_inner_eq g X Z Y x hX hZ hY]
    have hsum := koszul_metric_compat_sum g X Y Z x
    -- hsum : K X Y Z + K X Z Y = 2 * directionalDeriv ... x (X x)
    -- Convert goal to directionalDeriv form (rfl by def of directionalDeriv).
    show directionalDeriv (fun y => g.metricInner y (Y y) (Z y)) x (X x) =
        (1 / 2) * koszulFunctional g X Y Z x + (1 / 2) * koszulFunctional g X Z Y x
    linarith
  · -- Smoothness clause (smooth-VF direction): reduce via `hcov` eq spec
    -- to smoothness of `(fun y => koszulCovDeriv g X.toFun Y.toFun y _ _)`,
    -- then forward to `koszulCovDeriv_smoothVF_smoothAt`.
    intro X Y x
    have h_eq : (fun y : M => cov.toFun Y.toFun y (X.toFun y))
        = (fun y : M => koszulCovDeriv g X.toFun Y.toFun y
            (X.smoothAt y) (Y.smoothAt y)) := by
      funext y
      exact hcov X.toFun Y.toFun y (X.smoothAt y) (Y.smoothAt y)
    rw [h_eq]
    exact koszulCovDeriv_smoothVF_smoothAt g X Y x

/-- **Math.** The **Levi-Civita connection** $\nabla$ on the tangent
bundle of a Riemannian manifold: the unique torsion-free,
metric-compatible covariant derivative. Real `noncomputable def` via
`Classical.choose` over `leviCivitaConnection_exists`.

**Ground truth**: do Carmo 1992 §2 (Koszul formula gives uniqueness). -/
noncomputable def leviCivitaConnection (g : RiemannianMetric I M) :
    CovariantDerivative I E (fun x : M => TangentSpace I x) :=
  Classical.choose (leviCivitaConnection_exists (I := I) (M := M) g)

/-- **Math.** **Covariant derivative of one vector field along another**:
$(\nabla_X Y)(x) := \nabla\,Y\,x\,(X\,x)$, where $\nabla$ is the
Levi-Civita connection. Torsion-free and metric-compatible w.r.t.
`g.metricInner`.

**Ground truth**: do Carmo 1992 §2 Definition 2.1. -/
noncomputable def covDeriv
    (g : RiemannianMetric I M)
    (X Y : VectorFieldSection I M) (x : M) :
    TangentSpace I x :=
  ((leviCivitaConnection (I := I) (M := M) g).toFun Y x) (X x)

/-- **Math.** Notation `∇[X] Y` for `covDeriv (HasMetric.metric) X Y`. The
notation pipes the ambient `[HasMetric I M]` metric so downstream code
continues to write `∇[X] Y` unchanged during Phase 1 (typeclass retained
until #19). -/
scoped[Riemannian] notation:max "∇[" X "] " Y:max =>
  covDeriv (HasMetric.metric) X Y

/-- **Math.** Notation `⟦X, Y⟧` for the manifold Lie bracket
`mlieBracket _ X Y` (model `I` inferred from section types). -/
scoped[Riemannian] notation:max "⟦" X ", " Y "⟧" =>
  VectorField.mlieBracket _ X Y

/-- **Math.** The Levi-Civita connection is torsion-free. -/
theorem leviCivitaConnection_torsion_zero (g : RiemannianMetric I M) :
    (leviCivitaConnection (I := I) (M := M) g).torsion = 0 :=
  (Classical.choose_spec (leviCivitaConnection_exists (I := I) (M := M) g)).1

/-- **Math.** The Levi-Civita connection is **metric-compatible** for
smooth $X, Y, Z$ at $x$:
$$\nabla_X \langle Y, Z \rangle (x) =
  \langle \nabla_X Y, Z \rangle (x) + \langle Y, \nabla_X Z \rangle (x).$$
Metric is the framework-owned `g.metricInner`. Smoothness hypotheses match
do Carmo 1992 §2 Theorem 3.6. -/
theorem leviCivitaConnection_metric_compatible
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y y) (Z y)) x (X x) =
      g.metricInner x (covDeriv g X Y x) (Z x)
        + g.metricInner x (Y x) (covDeriv g X Z x) :=
  (Classical.choose_spec (leviCivitaConnection_exists (I := I) (M := M) g)).2.1
    X Y Z x hX hY hZ

/-- **Math.** Smoothness of the Levi-Civita connection along a smooth
direction: for `X, Y : SmoothVectorField I M`, the section
`y ↦ ∇_{X(y)} Y(y)` is smooth at every point. Direct projection from
the 3rd conjunct of `leviCivitaConnection_exists`. -/
theorem leviCivitaConnection_smoothAt_smoothVF_dir
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt (fun y : M => covDeriv g X Y y) x :=
  (Classical.choose_spec (leviCivitaConnection_exists (I := I) (M := M) g)).2.2 X Y x

/-- **Math.** Covariant derivative at a point as a continuous linear map
in the direction slot: $\nabla\,Y|_x : T_xM \to_L T_xM$,
$v \mapsto (\nabla_v Y)(x)$. Pointwise linearity in direction lets
identities involving the direction slot reduce to standard CLM lemmas. -/
noncomputable def covDerivAt
    (g : RiemannianMetric I M)
    (Y : VectorFieldSection I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (leviCivitaConnection (I := I) (M := M) g).toFun Y x

/-- **Math.** **Riesz formula for the covariant derivative**: for smooth
$X, Y, Z$,
$$\langle \nabla_X Y, Z\rangle_g(x) = \tfrac12 K(X, Y; Z)(x).$$
Cycling metric-compat over $(X, Y, Z)$, $(Y, Z, X)$, $(Z, X, Y)$ and
substituting torsion-freeness isolates $\langle \nabla_X Y, Z\rangle$. -/
private theorem covDeriv_inner_eq_half_koszul
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    g.metricInner x (covDeriv g X Y x) (Z x)
      = (1/2 : ℝ) * koszulFunctional g X Y Z x := by
  -- Notation: write `cov A B := (leviCivitaConnection g).toFun B x (A x)` (= covDeriv A B x).
  -- We'll identify these via `show` against the unfolded form and use linarith.
  -- Spec from Classical.choose: torsion-free + metric-compat for smooth fields.
  obtain ⟨h_tors, h_compat, _h_smooth⟩ := Classical.choose_spec
    (leviCivitaConnection_exists (I := I) (M := M) g)
  -- Three cyclic metric-compat instances + 3 torsion-free instances.
  -- Wrap each LHS into `directionalDeriv` (= mfderiv) so that all
  -- arithmetic happens uniformly in `ℝ`.
  have hXY : directionalDeriv (fun y => g.metricInner y (Y y) (Z y)) x (X x)
      = g.metricInner x (((leviCivitaConnection g).toFun Y x) (X x)) (Z x)
        + g.metricInner x (Y x) (((leviCivitaConnection g).toFun Z x) (X x)) :=
    h_compat X Y Z x hX hY hZ
  have hYZ : directionalDeriv (fun y => g.metricInner y (Z y) (X y)) x (Y x)
      = g.metricInner x (((leviCivitaConnection g).toFun Z x) (Y x)) (X x)
        + g.metricInner x (Z x) (((leviCivitaConnection g).toFun X x) (Y x)) :=
    h_compat Y Z X x hY hZ hX
  have hZX : directionalDeriv (fun y => g.metricInner y (X y) (Y y)) x (Z x)
      = g.metricInner x (((leviCivitaConnection g).toFun X x) (Z x)) (Y x)
        + g.metricInner x (X x) (((leviCivitaConnection g).toFun Y x) (Z x)) :=
    h_compat Z X Y x hZ hX hY
  rw [CovariantDerivative.torsion_eq_zero_iff] at h_tors
  have h_torsXY := @h_tors X Y x hX hY
  have h_torsYZ := @h_tors Y Z x hY hZ
  have h_torsZX := @h_tors Z X x hZ hX
  -- Symmetrize the right slot of each metric-compat equation, then convert to
  -- the unfolded `leviCivitaConnection` form so all cov-quantities live in
  -- the same syntactic namespace.
  rw [g.metricInner_comm x (Y x)] at hXY
  rw [g.metricInner_comm x (Z x)] at hYZ
  rw [g.metricInner_comm x (X x)] at hZX
  -- Convert torsion-free identities to inner-product form, in the
  -- `leviCivitaConnection` syntactic form.
  have htXY :
      g.metricInner x ((leviCivitaConnection g).toFun Y x (X x)) (Z x)
      - g.metricInner x ((leviCivitaConnection g).toFun X x (Y x)) (Z x)
      = g.metricInner x (mlieBracket I X Y x) (Z x) := by
    have := congrArg (fun v => g.metricInner x v (Z x)) h_torsXY
    simpa [g.metricInner_sub_left] using this
  have htYZ :
      g.metricInner x ((leviCivitaConnection g).toFun Z x (Y x)) (X x)
      - g.metricInner x ((leviCivitaConnection g).toFun Y x (Z x)) (X x)
      = g.metricInner x (mlieBracket I Y Z x) (X x) := by
    have := congrArg (fun v => g.metricInner x v (X x)) h_torsYZ
    simpa [g.metricInner_sub_left] using this
  have htZX :
      g.metricInner x ((leviCivitaConnection g).toFun X x (Z x)) (Y x)
      - g.metricInner x ((leviCivitaConnection g).toFun Z x (X x)) (Y x)
      = g.metricInner x (mlieBracket I Z X x) (Y x) := by
    have := congrArg (fun v => g.metricInner x v (Y x)) h_torsZX
    simpa [g.metricInner_sub_left] using this
  -- [Z,X] = -[X,Z], so its inner product flips sign.
  have h_brXZ : g.metricInner x (mlieBracket I Z X x) (Y x)
      = -g.metricInner x (mlieBracket I X Z x) (Y x) := by
    rw [show mlieBracket I Z X x = -mlieBracket I X Z x from
        VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  -- Goal: 2⟨covXY, Z⟩ = K. linarith closes after combining hypotheses linearly.
  show g.metricInner x (((leviCivitaConnection g).toFun Y x) (X x)) (Z x)
    = (1/2 : ℝ) * (
        directionalDeriv (fun y => g.metricInner y (Y y) (Z y)) x (X x)
      + directionalDeriv (fun y => g.metricInner y (Z y) (X y)) x (Y x)
      - directionalDeriv (fun y => g.metricInner y (X y) (Y y)) x (Z x)
      + g.metricInner x (mlieBracket I X Y x) (Z x)
      - g.metricInner x (mlieBracket I Y Z x) (X x)
      - g.metricInner x (mlieBracket I X Z x) (Y x))
  linarith [hXY, hYZ, hZX, htXY, htYZ, htZX, h_brXZ]


/-! ## Locality of Koszul + covariant derivative

If two sections agree on a nbhd of `x`, their Koszul functional values at `x`
agree, and consequently their Levi-Civita derivatives at `x` agree (Riesz
uniqueness). -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
omit [CompleteSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [IsLocallyConstantChartedSpace H M] in
/-- **Math.** **Locality of `koszulFunctional` in the middle argument**:
if $Y_1 =ᶠ[𝓝 x] Y_2$, then $K(X, Y_1; Z)(x) = K(X, Y_2; Z)(x)$. -/
private theorem koszulFunctional_eventuallyEq_middle
    (g : RiemannianMetric I M)
    (X Y₁ Y₂ Z : VectorFieldSection I M) (x : M)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    koszulFunctional g X Y₁ Z x = koszulFunctional g X Y₂ Z x := by
  -- Pointwise equality at `x` follows from `EventuallyEq` membership.
  have hx : Y₁ x = Y₂ x := h.self_of_nhds
  -- Function-level eventual equalities for the 3 directionalDeriv arguments.
  have h_metYZ : (fun y => g.metricInner y (Y₁ y) (Z y))
      =ᶠ[𝓝 x] (fun y => g.metricInner y (Y₂ y) (Z y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have h_metXY : (fun y => g.metricInner y (X y) (Y₁ y))
      =ᶠ[𝓝 x] (fun y => g.metricInner y (X y) (Y₂ y)) := by
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
    (g : RiemannianMetric I M)
    (X Y₁ Y₂ : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    covDeriv g X Y₁ x = covDeriv g X Y₂ x := by
  -- By Riesz uniqueness on `g.metricInner_eq_iff_eq`: equal inner-products against
  -- arbitrary test vector ⇒ equal vectors. Test via the smooth FiberBundle.extend
  -- of a model-fiber test, lift through `covDeriv_inner_eq_half_koszul`, then use
  -- `koszulFunctional_eventuallyEq_middle`.
  apply (g.metricInner_eq_iff_eq x _ _).mp
  intro Z₀
  set Z : VectorFieldSection I M := FiberBundle.extend E Z₀ with hZ_def
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
  have hZ_smooth : TangentSmoothAt Z x :=
    FiberBundle.mdifferentiableAt_extend I E Z₀
  rw [← hZx]
  simp only [covDeriv_inner_eq_half_koszul g X Y₁ Z x hX hY₁ hZ_smooth,
      covDeriv_inner_eq_half_koszul g X Y₂ Z x hX hY₂ hZ_smooth,
      koszulFunctional_eventuallyEq_middle g X Y₁ Y₂ Z x h]

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
    (g : RiemannianMetric I M)
    (X Y : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    covDeriv g X Y x - covDeriv g Y X x = (⟦X, Y⟧) x :=
  (CovariantDerivative.torsion_eq_zero_iff
    (cov := leviCivitaConnection (I := I) (M := M) g)).mp
    (leviCivitaConnection_torsion_zero g) hX hY

/-- **Math.** Additivity of `covDeriv` in the differentiated field:
$\nabla_X (Y_1 + Y_2)(x) = \nabla_X Y_1(x) + \nabla_X Y_2(x)$ for
$Y_1, Y_2$ smooth at $x$. -/
theorem covDeriv_add_field
    (g : RiemannianMetric I M)
    (X Y₁ Y₂ : VectorFieldSection I M) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x) :
    covDeriv g X (Y₁ + Y₂) x = covDeriv g X Y₁ x + covDeriv g X Y₂ x := by
  have h := (leviCivitaConnection g).isCovariantDerivativeOnUniv.add (σ := Y₁) (σ' := Y₂)
    (x := x) hY₁ hY₂
  show ((leviCivitaConnection g).toFun (Y₁ + Y₂) x) (X x)
    = ((leviCivitaConnection g).toFun Y₁ x) (X x) + ((leviCivitaConnection g).toFun Y₂ x) (X x)
  rw [h]
  rfl

/-- **Math.** Locality of `covDeriv` in the differentiated field: if
$Y_1 =ᶠ[𝓝 x] Y_2$ and both are smooth at $x$, then
$\nabla_X Y_1(x) = \nabla_X Y_2(x)$. Smoothness of $X$ is not required
(the connection is continuous linear map in the direction slot). -/
theorem covDeriv_congr_eventuallyEq_field
    (g : RiemannianMetric I M)
    (X Y₁ Y₂ : VectorFieldSection I M) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    covDeriv g X Y₁ x = covDeriv g X Y₂ x := by
  show ((leviCivitaConnection g).toFun Y₁ x) (X x)
      = ((leviCivitaConnection g).toFun Y₂ x) (X x)
  rw [(leviCivitaConnection g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hY₁ hY₂ Filter.univ_mem h]

/-- **Math.** `covDeriv` of a constant scalar multiple:
$\nabla_X (a \cdot Y)(x) = a \cdot \nabla_X Y(x)$ for $a : \mathbb{R}$. -/
theorem covDeriv_smul_const_field
    (g : RiemannianMetric I M)
    (X Y : VectorFieldSection I M) (x : M) (a : ℝ)
    (hY : TangentSmoothAt Y x) :
    covDeriv g X (a • Y) x = a • covDeriv g X Y x := by
  have h := (leviCivitaConnection g).isCovariantDerivativeOnUniv.smul_const (σ := Y)
    (x := x) a hY
  show ((leviCivitaConnection g).toFun (a • Y) x) (X x)
    = a • ((leviCivitaConnection g).toFun Y x) (X x)
  rw [h]
  rfl

/-- **Math.** Subtractivity of `covDeriv` in the differentiated field:
$\nabla_X (Y_1 - Y_2)(x) = \nabla_X Y_1(x) - \nabla_X Y_2(x)$. -/
theorem covDeriv_sub_field
    (g : RiemannianMetric I M)
    (X Y₁ Y₂ : VectorFieldSection I M) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x) :
    covDeriv g X (Y₁ - Y₂) x = covDeriv g X Y₁ x - covDeriv g X Y₂ x := by
  -- Y₁ - Y₂ = Y₁ + (-1) • Y₂
  have h_eq : (Y₁ - Y₂ : VectorFieldSection I M) = Y₁ + ((-1 : ℝ) • Y₂) := by
    funext z
    show Y₁ z - Y₂ z = Y₁ z + (-1 : ℝ) • Y₂ z
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h_eq]
  -- Smoothness of (-1) • Y₂: from TangentSmoothAt.neg via Y₁ - Y₂ form.
  have h_neg : TangentSmoothAt ((-1 : ℝ) • Y₂) x := by
    have h_eq' : ((-1 : ℝ) • Y₂ : VectorFieldSection I M) = -Y₂ := by
      funext z
      show (-1 : ℝ) • Y₂ z = -Y₂ z
      exact neg_one_smul _ _
    rw [h_eq']
    exact hY₂.neg
  rw [covDeriv_add_field g X Y₁ ((-1 : ℝ) • Y₂) x hY₁ h_neg,
      covDeriv_smul_const_field g X Y₂ x (-1) hY₂]
  show covDeriv g X Y₁ x + (-1 : ℝ) • covDeriv g X Y₂ x = covDeriv g X Y₁ x - covDeriv g X Y₂ x
  rw [neg_one_smul, sub_eq_add_neg]

/-- **Math.** Leibniz rule: the connection acts as a derivation in the
scalar factor of `g • Y`:
$$\nabla_X (g \cdot Y)(x) = g(x) \cdot \nabla_X Y(x) + (\mathrm{d}g \cdot X)(x) \cdot Y(x).$$ -/
theorem covDeriv_smul_scalar_field
    (g : RiemannianMetric I M)
    (X : VectorFieldSection I M)
    (f : M → ℝ) (Y : VectorFieldSection I M) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hY : TangentSmoothAt Y x) :
    covDeriv g X (f • Y) x
      = f x • covDeriv g X Y x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (X x)) • Y x := by
  have h := (leviCivitaConnection (I := I) (M := M) g).isCovariantDerivativeOnUniv.leibniz
    (σ := Y) (g := f) (x := x) hY hf trivial
  -- h : (leviCivitaConnection g).toFun (f • Y) x
  --     = f x • (leviCivitaConnection g).toFun Y x + (extDerivFun f x).smulRight (Y x)
  show ((leviCivitaConnection (I := I) (M := M) g).toFun (f • Y) x) (X x) = _
  rw [h]
  show f x • ((leviCivitaConnection (I := I) (M := M) g).toFun Y x) (X x)
      + ((extDerivFun f x).smulRight (Y x)) (X x)
    = f x • ((leviCivitaConnection (I := I) (M := M) g).toFun Y x) (X x)
      + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (X x)) • Y x
  -- `((extDerivFun f x).smulRight (Y x)) v = (extDerivFun f x v) • Y x` (def-eq).
  -- `extDerivFun f x v = mfderiv f x v` via `NormedSpace.fromTangentSpace` identity
  -- on the scalar tangent space `TangentSpace 𝓘(ℝ, ℝ) (f x) ≃L ℝ`.
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
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) : TangentSpace I x :=
  covDeriv g X (covDeriv g Y Z) x - covDeriv g Y (covDeriv g X Z) x
    - covDeriv g (mlieBracket I X Y) Z x

/-- **Math.** Notation `Riem(X, Y) Z` for `riemannCurvature (HasMetric.metric) X Y Z`.
The notation pipes the ambient `[HasMetric I M]` metric so downstream code
continues to write `Riem(X, Y) Z` unchanged during Phase 1. -/
scoped[Riemannian] notation:max "Riem(" X ", " Y ") " Z:max =>
  riemannCurvature (HasMetric.metric) X Y Z

/-! ### `riem_simp` lemmas

Two rewrites that drive the `riem_simp` simp set, populated for the
Riemann curvature operator built from the framework's `covDeriv`. Together
with `abel` they discharge the algebraic identities of `riemannCurvature`
without exposing the underlying connection plumbing. -/

/-- **Math.** **Commutator form of the Riemann curvature**:
$$R(X, Y) Z(x)
   \;=\; \nabla_X \nabla_Y Z(x) - \nabla_Y \nabla_X Z(x) - \nabla_{[X, Y]} Z(x),$$
realising $R(X, Y)$ as the commutator $[\nabla_X, \nabla_Y]$ corrected by
$-\nabla_{[X, Y]}$ that measures non-commutativity of the covariant
derivative. Pure `rfl` from the definition of `riemannCurvature`; tagged
`@[riem_simp]` for use as a simp lemma.

Reference: do Carmo 1992 §4 Definition 2.1. -/
@[riem_simp]
theorem riemannCurvature_commutator_form
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) :
    riemannCurvature g X Y Z x
      = covDeriv g X (covDeriv g Y Z) x - covDeriv g Y (covDeriv g X Z) x
        - covDeriv g (⟦X, Y⟧) Z x := rfl

/-- **Math.** Lie-bracket antisymmetry through the direction slot:
$\nabla_{[Y,X]} Z = -\nabla_{[X,Y]} Z$ pointwise. Used as explicit `rw`
step (kept out of `riem_simp` to avoid the $X \leftrightarrow Y$ loop). -/
theorem covDeriv_mlieBracket_swap_apply
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) :
    covDeriv g (⟦Y, X⟧) Z x = -covDeriv g (⟦X, Y⟧) Z x := by
  unfold covDeriv
  rw [show mlieBracket I Y X x = -mlieBracket I X Y x from
        VectorField.mlieBracket_swap_apply,
      ((leviCivitaConnection (I := I) (M := M) g).toFun Z x).map_neg]

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

/-- **Math.** Section-level torsion-freeness: under global smoothness, the
pointwise torsion-free identity lifts to a Π-equality, enabling direct
substitution under `covDeriv X (·) x`. -/
theorem covDeriv_section_eq_swap_add_mlieBracket
    (g : RiemannianMetric I M)
    (Y Z : VectorFieldSection I M)
    (hY : ∀ y, TangentSmoothAt Y y) (hZ : ∀ y, TangentSmoothAt Z y) :
    (fun y => covDeriv g Y Z y)
      = (fun y => covDeriv g Z Y y) + (fun y => mlieBracket I Y Z y) := by
  funext y
  have h := covDeriv_sub_swap_eq_mlieBracket g Y Z y (hY y) (hZ y)
  -- h : covDeriv g Y Z y - covDeriv g Z Y y = mlieBracket I Y Z y
  show covDeriv g Y Z y = covDeriv g Z Y y + mlieBracket I Y Z y
  rw [← h]; abel

/-! ## Smoothness wrappers on `covDeriv` -/

/-- **Math.** $\nabla_{\,\mathrm{const}\,v}\, Y$ is smooth at every $x$
for any `SmoothVectorField Y` and any constant direction $v : E$. -/
theorem covDeriv_const_smoothVF_smoothAt
    (g : RiemannianMetric I M)
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt (fun y : M => covDeriv g (fun _ : M => v) Y y) x :=
  leviCivitaConnection_smoothAt_smoothVF_dir g
    (SmoothVectorField.const v) Y x

/-- **Math.** $\nabla_X Y$ is smooth at every $x$ for any smooth vector
fields `X, Y : SmoothVectorField I M`. Smooth-VF-direction strengthening
of `covDeriv_const_smoothVF_smoothAt`. -/
theorem covDeriv_smoothVF_smoothAt
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt (fun y : M => covDeriv g X Y y) x :=
  Riemannian.leviCivitaConnection_smoothAt_smoothVF_dir g X Y x

/-- **Math.** **Algebraic (first) Bianchi identity** for the Levi-Civita
connection:
$$R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0.$$
The explicit smoothness hypotheses on $X, Y, Z$, their first
covariant derivatives, and their pairwise Lie brackets match the
standard $C^2$ textbook setup but fire pointwise.

**Ground truth**: do Carmo 1992 §4 Proposition 2.5 (ii). -/
theorem bianchi_first
    (X Y Z : SmoothVectorField I M) (x : M) :
    Riem(X, Y) Z x + Riem(Y, Z) X x + Riem(Z, X) Y x = 0 := by
  -- Jacobi identity via the `SmoothVectorField.mlieBracket_jacobi` framework
  -- primitive (wraps Mathlib's `leibniz_identity_mlieBracket_apply`).
  have h_jac : (⟦X, ⟦Y, Z⟧⟧) x = (⟦⟦X, Y⟧, Z⟧) x + (⟦Y, ⟦X, Z⟧⟧) x :=
    SmoothVectorField.mlieBracket_jacobi X Y Z x
  -- Derive all 11 smoothness hypotheses internally from `X.smooth`, `Y.smooth`,
  -- `Z.smooth` via `covDeriv_smoothVF_smoothAt` and `mlieBracket_tangentSmoothAt`.
  have hX : ∀ y, TangentSmoothAt X.toFun y := X.smoothAt
  have hY : ∀ y, TangentSmoothAt Y.toFun y := Y.smoothAt
  have hZ : ∀ y, TangentSmoothAt Z.toFun y := Z.smoothAt
  have h_dXZ : ∀ y, TangentSmoothAt ∇[X] Z y :=
    fun y => covDeriv_smoothVF_smoothAt HasMetric.metric X Z y
  have h_dYX : ∀ y, TangentSmoothAt ∇[Y] X y :=
    fun y => covDeriv_smoothVF_smoothAt HasMetric.metric Y X y
  have h_dZY : ∀ y, TangentSmoothAt ∇[Z] Y y :=
    fun y => covDeriv_smoothVF_smoothAt HasMetric.metric Z Y y
  have h_XY : ∀ y, TangentSmoothAt ⟦X, Y⟧ y :=
    fun _ => mlieBracket_tangentSmoothAt X.smooth Y.smooth
  have h_YX : ∀ y, TangentSmoothAt ⟦Y, X⟧ y :=
    fun _ => mlieBracket_tangentSmoothAt Y.smooth X.smooth
  have h_YZ : ∀ y, TangentSmoothAt ⟦Y, Z⟧ y :=
    fun _ => mlieBracket_tangentSmoothAt Y.smooth Z.smooth
  have h_ZX : ∀ y, TangentSmoothAt ⟦Z, X⟧ y :=
    fun _ => mlieBracket_tangentSmoothAt Z.smooth X.smooth
  have h_XZ : ∀ y, TangentSmoothAt ⟦X, Z⟧ y :=
    fun _ => mlieBracket_tangentSmoothAt X.smooth Z.smooth
  -- Step 1: section-level torsion-freeness (Π-equalities, via global smoothness).
  have eq_YZ : (∇[Y] Z : VectorFieldSection I M) = ∇[Z] Y + ⟦Y, Z⟧ :=
    covDeriv_section_eq_swap_add_mlieBracket HasMetric.metric Y Z hY hZ
  have eq_ZX : (∇[Z] X : VectorFieldSection I M) = ∇[X] Z + ⟦Z, X⟧ :=
    covDeriv_section_eq_swap_add_mlieBracket HasMetric.metric Z X hZ hX
  have eq_XY : (∇[X] Y : VectorFieldSection I M) = ∇[Y] X + ⟦X, Y⟧ :=
    covDeriv_section_eq_swap_add_mlieBracket HasMetric.metric X Y hX hY
  -- Step 2: unfold riemannCurvature, substitute section equalities, split via add_field.
  show (∇[X] (∇[Y] Z)) x
        - (∇[Y] (∇[X] Z)) x
        - (∇[⟦X, Y⟧] Z) x
      + ((∇[Y] (∇[Z] X)) x
        - (∇[Z] (∇[Y] X)) x
        - (∇[⟦Y, Z⟧] X) x)
      + ((∇[Z] (∇[X] Y)) x
        - (∇[X] (∇[Z] Y)) x
        - (∇[⟦Z, X⟧] Y) x) = 0
  rw [eq_YZ, eq_ZX, eq_XY]
  rw [covDeriv_add_field HasMetric.metric X ∇[Z] Y ⟦Y, Z⟧ x
        (h_dZY x) (h_YZ x),
      covDeriv_add_field HasMetric.metric Y ∇[X] Z ⟦Z, X⟧ x
        (h_dXZ x) (h_ZX x),
      covDeriv_add_field HasMetric.metric Z ∇[Y] X ⟦X, Y⟧ x
        (h_dYX x) (h_XY x)]
  -- Step 3: pointwise torsion-free pairings (∇_A B - ∇_B A = [A,B]):
  have pair_X : (∇[X] ⟦Y, Z⟧) x
                  - (∇[⟦Y, Z⟧] X) x
                = (⟦X, ⟦Y, Z⟧⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket HasMetric.metric X ⟦Y, Z⟧ x (hX x) (h_YZ x)
  have pair_Y : (∇[Y] ⟦Z, X⟧) x
                  - (∇[⟦Z, X⟧] Y) x
                = (⟦Y, ⟦Z, X⟧⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket HasMetric.metric Y ⟦Z, X⟧ x (hY x) (h_ZX x)
  have pair_Z : (∇[Z] ⟦X, Y⟧) x
                  - (∇[⟦X, Y⟧] Z) x
                = (⟦Z, ⟦X, Y⟧⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket HasMetric.metric Z ⟦X, Y⟧ x (hZ x) (h_XY x)
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
  have h_subX : (∇[X] ⟦Y, Z⟧) x
                  = (⟦X, ⟦Y, Z⟧⟧) x
                    + (∇[⟦Y, Z⟧] X) x := by
    rw [← pair_X]; abel
  have h_subY : (∇[Y] ⟦Z, X⟧) x
                  = (⟦Y, ⟦Z, X⟧⟧) x
                    + (∇[⟦Z, X⟧] Y) x := by
    rw [← pair_Y]; abel
  have h_subZ : (∇[Z] ⟦X, Y⟧) x
                  = (⟦Z, ⟦X, Y⟧⟧) x
                    + (∇[⟦X, Y⟧] Z) x := by
    rw [← pair_Z]; abel
  rw [h_subX, h_subY, h_subZ]
  -- Goal now has 3 outer-bracket terms + 6 ∇_·_ terms; three pairs of ∇_{[·,·]} ·
  -- match (positive in subX/Y/Z, negative in 3 outer ∇_{[·,·]} · slots) — abel kills.
  -- 3 pairs of mixed ∇∇ terms also cancel (∇_X∇_Z Y, ∇_Y∇_X Z, ∇_Z∇_Y X).
  -- Result: [X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0.
  -- Step 5: convert [Y,[Z,X]] and [Z,[X,Y]] into Jacobi-compatible forms via antisymm.
  -- Section-level antisymm:
  have sec_ZX : ⟦Z, X⟧ = -⟦X, Z⟧ := by
    funext y; exact VectorField.mlieBracket_swap_apply
  have sec_XY : ⟦X, Y⟧ = -⟦Y, X⟧ := by
    funext y; exact VectorField.mlieBracket_swap_apply
  -- Use Mathlib `mlieBracket_const_smul_right` (with c = -1) to pull negation out.
  have h_YZX : (⟦Y, ⟦Z, X⟧⟧) x
                = -(⟦Y, ⟦X, Z⟧⟧) x := by
    have h_eq : (⟦Z, X⟧ : VectorFieldSection I M)
              = (-1 : ℝ) • ⟦X, Z⟧ := by
      funext y
      show (⟦Z, X⟧) y = (-1 : ℝ) • (⟦X, Z⟧) y
      rw [neg_one_smul]
      exact VectorField.mlieBracket_swap_apply
    rw [h_eq, VectorField.mlieBracket_const_smul_right (h_XZ x), neg_one_smul]
  have h_ZXY : (⟦Z, ⟦X, Y⟧⟧) x
                = -(⟦Z, ⟦Y, X⟧⟧) x := by
    have h_eq : (⟦X, Y⟧ : VectorFieldSection I M)
              = (-1 : ℝ) • ⟦Y, X⟧ := by
      funext y
      show (⟦X, Y⟧) y = (-1 : ℝ) • (⟦Y, X⟧) y
      rw [neg_one_smul]
      exact VectorField.mlieBracket_swap_apply
    rw [h_eq, VectorField.mlieBracket_const_smul_right (h_YX x), neg_one_smul]
  -- Outer antisymm: [[X,Y], Z] x = -[Z, [X,Y]] x
  have asym_outer : (⟦⟦X, Y⟧, Z⟧) x
                  = -(⟦Z, ⟦X, Y⟧⟧) x :=
    VectorField.mlieBracket_swap_apply
  -- Now: goal (after abel-cancels) reduces to:
  --   [X,[Y,Z]] x + [Y,[Z,X]] x + [Z,[X,Y]] x = 0
  -- = ([[X,Y],Z] + [Y,[X,Z]]) + (-[Y,[X,Z]]) + [Z,[X,Y]]    (h_jac, h_YZX)
  -- = [[X,Y],Z] + [Z,[X,Y]]
  -- = -[Z,[X,Y]] + [Z,[X,Y]] = 0                              (asym_outer)
  -- We chain these into the goal via abel.
  rw [h_jac, h_YZX, asym_outer]
  abel

/-! ## Differential (second) Bianchi identity

Covariant derivative of the Riemann curvature tensor (acting as a $(1,3)$
endomorphism-valued tensor) satisfies a cyclic identity:
$$(\nabla_X R)(Y, Z) W + (\nabla_Y R)(Z, X) W + (\nabla_Z R)(X, Y) W = 0.$$

The covariant-derivative-of-$R$ pattern follows the standard
tensor-cov-deriv recipe: $\nabla_X$ acts on each slot of $R$ as a
derivation, so the action on $R(Y, Z) W$ picks up four terms
(one for $R(Y, Z) W$ as a section, three for the slots $Y, Z, W$).
-/

/-- **Math.** **Covariant derivative of the Riemann curvature tensor**
at $x$:
$$(\nabla_X R)(Y, Z) W (x) \;=\; \nabla_X (R(Y, Z) W)(x)
    - R(\nabla_X Y, Z) W(x) - R(Y, \nabla_X Z) W(x) - R(Y, Z)(\nabla_X W)(x).$$

This is the standard $(1,4)$-tensor covariant-derivative pattern: $\nabla$
acts on each slot of $R$ as a derivation. -/
noncomputable def covDerivRiemann
    (X Y Z W : SmoothVectorField I M) (x : M) : TangentSpace I x :=
  (∇[X] (Riem(Y, Z) W)) x
    - Riem(∇[X] Y, Z) W x
    - Riem(Y, ∇[X] Z) W x
    - Riem(Y, Z) (∇[X] W) x

/-- **Math.** Notation `(∇R)[X](Y, Z) W` for `covDerivRiemann X Y Z W`. -/
scoped[Riemannian] notation:max "(∇R)[" X "](" Y ", " Z ") " W:max =>
  covDerivRiemann X Y Z W

/-- **Math.** **Second (differential) Bianchi identity** for the
Levi-Civita connection:
$$(\nabla_X R)(Y, Z) W + (\nabla_Y R)(Z, X) W + (\nabla_Z R)(X, Y) W = 0.$$

Reference: do Carmo 1992 §4 Proposition 2.5 (iii); Petersen Ch. 3.

PRE-PAPER: the standard proof composes the commutator-form of `Riem`
(`riemannCurvature_commutator_form`), distributivity of `covDeriv` in
its differentiated argument (`covDeriv_add_field`, `covDeriv_sub_field`),
the first Bianchi identity (`bianchi_first`), and the manifold
Lie-bracket Jacobi identity (`SmoothVectorField.mlieBracket_jacobi`).
Adapting the synthetic-DG version (external repo `Connection.lean:348`):
expand `(∇R)` into 12 `covDeriv∘covDeriv∘covDeriv` terms, group into 6
pairs via subtractivity of `covDeriv` in the first slot, reduce each
pair to a `mlieBracket` term via torsion-freeness, and close via Jacobi.
Estimated 80-120 LOC; repair tracked separately. -/
theorem bianchi_second
    [IsManifold I 3 M]
    (X Y Z W : SmoothVectorField I M) (x : M) :
    (∇R)[X](Y, Z) W x + (∇R)[Y](Z, X) W x + (∇R)[Z](X, Y) W x = 0 := by
  sorry

end Riemannian
