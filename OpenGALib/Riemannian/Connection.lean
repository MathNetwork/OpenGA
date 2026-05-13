import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import OpenGALib.Riemannian.Manifold
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Riemannian.Tensor.MusicalIso
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

## Main definitions

* `covDeriv X Y x = (leviCivitaConnection.toFun Y x) (X x)`.
* `leviCivitaConnection` — bundled `CovariantDerivative` structure.
* `riemannCurvature X Y Z x` — curvature tensor
  $R(X, Y) Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X,Y]} Z$.

## Main results

* `leviCivitaConnection_torsion_zero`, `leviCivitaConnection_metric_compatible`.
* `covDeriv_sub_swap_eq_mlieBracket`, `covDeriv_add_field`,
  `covDeriv_smul_const_field`, `covDeriv_sub_field`.
* `covDeriv_const_smoothVF_smoothAt` — chart-frame constant smoothness.
* `bianchi_first` — algebraic Bianchi I.

The Koszul construction (`koszulFunctional`, the 8 algebraic identities,
chart-pullback cotangent CLM, Riesz extraction `koszulCovDeriv`) is
`private` engineering.

Reference: do Carmo, *Riemannian Geometry*, §2 Theorem 3.6;
§4 Proposition 2.5 (Bianchi I).
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology Riemannian

namespace Riemannian

/-! ## from `Connection.lean` (Koszul section) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hm : HasMetric I M]

/-! ## Koszul functional + basic algebraic identities

The Koszul functional $K(X, Y; Z)$ encodes the Levi-Civita connection:
$\nabla_X Y$ is the unique vector with $\langle \nabla_X Y, Z \rangle =
\tfrac12 K(X, Y; Z)$ for all $Z$. Below we define `koszulFunctional`
and prove the foundational identities (anti-symmetry, metric
compatibility) used downstream for Riesz extraction.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6.
-/

/-- The **Koszul functional** $K(X, Y; Z) : M \to \mathbb{R}$.

Pointwise value at $x \in M$:
$$K(X, Y; Z)(x) \;=\; X\langle Y, Z\rangle\,(x) + Y\langle Z, X\rangle\,(x)
  - Z\langle X, Y\rangle\,(x) + \langle [X, Y], Z\rangle\,(x)
  - \langle [Y, Z], X\rangle\,(x) - \langle [X, Z], Y\rangle\,(x).$$

The Levi-Civita connection $\nabla_X Y$ is determined by Riesz
representation of the linear functional
$Z \mapsto \tfrac12 K(X, Y; Z)(x)$ via the inner product on
$T_xM$.

**Notation note**: $X\langle Y, Z\rangle$ denotes the directional
derivative of the real-valued function $y \mapsto \langle Y(y), Z(y)\rangle$
in direction $X(x)$ at $x$, i.e.,
`mfderiv I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x (X x)`.

**Ground truth**: do Carmo 1992 §2 (Koszul formula, equation (3) in
the proof of Theorem 3.6). -/
private noncomputable def directionalDeriv
    (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f x v

/-- The **Koszul functional** $K(X, Y; Z) : M \to \mathbb{R}$ as defined
above. Implementation uses the helper `directionalDeriv` to keep each
$X\langle Y, Z\rangle$ term typed as `ℝ` (avoiding the `TangentSpace 𝓘(ℝ,ℝ) (f x)`
basepoint mismatch under `HAdd` synthesis). The framework-owned
`metricInner` provides the inner product on tangent vectors. -/
private noncomputable def koszulFunctional
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x)
  + directionalDeriv (fun y => metricInner y (Z y) (X y)) x (Y x)
  - directionalDeriv (fun y => metricInner y (X y) (Y y)) x (Z x)
  + metricInner x (mlieBracket I X Y x) (Z x)
  - metricInner x (mlieBracket I Y Z x) (X x)
  - metricInner x (mlieBracket I X Z x) (Y x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Koszul antisymmetry identity**:
$$K(X, Y; Z)(x) - K(Y, X; Z)(x) \;=\; 2\,\langle [X, Y], Z\rangle(x).$$

This identity is the foundation of the torsion-free property (LC1) of
the Levi-Civita connection: under Riesz representation, $\nabla_X Y$
satisfies $\langle \nabla_X Y, Z\rangle = \tfrac12 K(X, Y; Z)$, so
$$\langle \nabla_X Y - \nabla_Y X, Z\rangle = \tfrac12(K(X,Y;Z) - K(Y,X;Z))
  = \langle [X, Y], Z\rangle$$
holds for all $Z$, hence $\nabla_X Y - \nabla_Y X = [X, Y]$.

**Algebraic content** (paper-level derivation):
Subtracting $K(Y, X; Z)$ from $K(X, Y; Z)$:
- The three `mfderiv` terms cancel pairwise via `metricInner_comm`
  on $\langle Y, Z\rangle, \langle Z, X\rangle, \langle X, Y\rangle$
  (the inner products are symmetric, so the underlying
  $\mathbb{R}$-valued functions coincide).
- $\langle [X,Y], Z\rangle - \langle [Y,X], Z\rangle = 2\langle [X,Y], Z\rangle$
  via `mlieBracket_swap_apply` ($[Y,X] = -[X,Y]$) +
  `metricInner_neg_left`.
- The other two Lie bracket pairs ($\langle [Y,Z], X\rangle$,
  $\langle [X,Z], Y\rangle$) cancel directly.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 proof (lines on
torsion-free derivation from Koszul). -/
private theorem koszul_antisymm
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x - koszulFunctional Y X Z x
      = 2 * metricInner x (mlieBracket I X Y x) (Z x) := by
  unfold koszulFunctional
  -- Inner symmetry as function equalities (so mfderiv values match pairwise).
  have hZY_YZ :
      (fun y : M => metricInner y (Z y) (Y y)) = fun y => metricInner y (Y y) (Z y) := by
    funext y; exact metricInner_comm y _ _
  have hXZ_ZX :
      (fun y : M => metricInner y (X y) (Z y)) = fun y => metricInner y (Z y) (X y) := by
    funext y; exact metricInner_comm y _ _
  have hYX_XY :
      (fun y : M => metricInner y (Y y) (X y)) = fun y => metricInner y (X y) (Y y) := by
    funext y; exact metricInner_comm y _ _
  rw [hZY_YZ, hXZ_ZX, hYX_XY]
  -- Lie-bracket swap on the (Y, X) bracket.
  rw [show mlieBracket I Y X x = -mlieBracket I X Y x from mlieBracket_swap_apply]
  rw [metricInner_neg_left]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Koszul metric-compatibility sum identity**:
$$K(X, Y; Z)(x) + K(X, Z; Y)(x) \;=\; 2\,X\langle Y, Z\rangle(x).$$

This identity is the foundation of metric-compatibility (LC2) of the
Levi-Civita connection: under Riesz representation,
$$\langle \nabla_X Y, Z\rangle + \langle Y, \nabla_X Z\rangle
  = \tfrac12(K(X,Y;Z) + K(X,Z;Y)) = X\langle Y, Z\rangle,$$
which is the metric-compatibility law $\nabla_X\langle Y,Z\rangle =
\langle \nabla_X Y,Z\rangle + \langle Y,\nabla_X Z\rangle$.

**Algebraic content** (paper-level derivation):
Adding $K(X, Z; Y)$ to $K(X, Y; Z)$:
- $X\langle Y, Z\rangle + X\langle Z, Y\rangle = 2 X\langle Y, Z\rangle$
  via `metricInner_comm` ($\langle Z, Y\rangle = \langle Y, Z\rangle$
  pointwise, hence equal as $\mathbb{R}$-valued functions, hence
  equal `mfderiv` value).
- The other two `mfderiv` pairs and the three Lie bracket pairs
  cancel via `metricInner_comm` + `mlieBracket_swap_apply` +
  `metricInner_neg_left`.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 proof (lines on
metric-compatibility derivation from Koszul). -/
private theorem koszul_metric_compat_sum
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x + koszulFunctional X Z Y x
      = 2 * directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x) := by
  unfold koszulFunctional
  -- Inner symmetry as function equalities.
  have hZY_YZ :
      (fun y : M => metricInner y (Z y) (Y y)) = fun y => metricInner y (Y y) (Z y) := by
    funext y; exact metricInner_comm y _ _
  have hYX_XY :
      (fun y : M => metricInner y (Y y) (X y)) = fun y => metricInner y (X y) (Y y) := by
    funext y; exact metricInner_comm y _ _
  have hXZ_ZX :
      (fun y : M => metricInner y (X y) (Z y)) = fun y => metricInner y (Z y) (X y) := by
    funext y; exact metricInner_comm y _ _
  rw [hZY_YZ, hYX_XY, hXZ_ZX]
  -- Lie-bracket swap on the (Z, Y) bracket inside K(X, Z; Y).
  rw [show mlieBracket I Z Y x = -mlieBracket I Y Z x from mlieBracket_swap_apply]
  rw [metricInner_neg_left]
  ring

/-! ## Koszul $C^\infty(M)$-linearity in $Z$

The Koszul functional $K(X, Y; Z)(x)$, viewed as a map of $Z$, is
$C^\infty(M)$-linear:
$$K(X, Y; f \cdot Z)(x) = f(x) \cdot K(X, Y; Z)(x) \qquad
  \text{for all } f \in C^\infty(M),\ Z \in \mathfrak{X}(M).$$

This is the key tensorial property enabling Riesz extraction: a
$C^\infty(M)$-linear functional on $\mathfrak{X}(M)$ descends to a
fibrewise linear functional on $T_xM$ at each $x$, and hence is
represented by a unique vector field via the Riemannian metric.

### Algebraic content (do Carmo §2 Theorem 3.6 existence proof, Step 2)

Substituting $Z \mapsto fZ$ into the 6 Koszul terms and applying
Leibniz rules:

* `directionalDeriv ⟨Y, fZ⟩ X = X(f)·⟨Y, Z⟩ + f · X⟨Y, Z⟩`
  — by `metricInner_smul_right` then product rule (`HasMFDerivAt.mul`).
* `directionalDeriv ⟨fZ, X⟩ Y = Y(f)·⟨Z, X⟩ + f · Y⟨Z, X⟩`
  — likewise (use `metricInner_smul_left`).
* `directionalDeriv ⟨X, Y⟩ (fZ) = f · directionalDeriv ⟨X, Y⟩ Z`
  — by linearity of `mfderiv` in the tangent vector
    (`ContinuousLinearMap.map_smul`).
* `⟨[X, Y], fZ⟩ = f · ⟨[X, Y], Z⟩` — `metricInner_smul_right`.
* `⟨[Y, fZ], X⟩ = Y(f)·⟨Z, X⟩ + f · ⟨[Y, Z], X⟩`
  — by `mlieBracket_smul_right` then `metricInner_smul_left/right`.
* `⟨[X, fZ], Y⟩ = X(f)·⟨Z, Y⟩ + f · ⟨[X, Z], Y⟩` — likewise.

Summing with the signs of `koszulFunctional`:
* The $X(f)$ terms: $X(f)\langle Y, Z\rangle - X(f)\langle Z, Y\rangle = 0$
  (`metricInner_comm`).
* The $Y(f)$ terms: $Y(f)\langle Z, X\rangle - Y(f)\langle Z, X\rangle = 0$.
* The $f \cdot (\ldots)$ terms reassemble into $f \cdot K(X, Y; Z)$.

This $X(f)/Y(f)$ pairwise cancellation by inner-product symmetry is
the **fundamental tensoriality** of Koszul: it is precisely why the
Levi-Civita connection is a tensor in $Z$ but not in $X$ (where no
such cancellation occurs).
-/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [hm : HasMetric I M] in
/-- **Helper**: Leibniz product rule for `directionalDeriv` on $\mathbb{R}$-valued
functions: $X(f \cdot g)(x) = f(x) \cdot X(g)(x) + g(x) \cdot X(f)(x)$.

Wraps Mathlib's `HasMFDerivAt.mul` for the framework's `directionalDeriv` helper. -/
private lemma directionalDeriv_mul
    (f g : M → ℝ) (x : M) (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    directionalDeriv (fun y => f y * g y) x v
      = f x * directionalDeriv g x v + g x * directionalDeriv f x v := by
  unfold directionalDeriv
  have heq : (fun y : M => f y * g y) = f * g := rfl
  rw [heq, (hf.hasMFDerivAt.mul hg.hasMFDerivAt).mfderiv]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [hm : HasMetric I M] in
/-- **Helper**: linearity of `directionalDeriv` in the tangent vector argument:
$X_{a \cdot v}(f) = a \cdot X_v(f)$.

Wraps `ContinuousLinearMap.map_smul` for `mfderiv` viewed as a linear map. -/
private lemma directionalDeriv_smul_arg
    (g : M → ℝ) (x : M) (a : ℝ) (v : TangentSpace I x) :
    directionalDeriv g x (a • v) = a * directionalDeriv g x v := by
  unfold directionalDeriv
  exact (mfderiv I 𝓘(ℝ, ℝ) g x).map_smul a v

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [hm : HasMetric I M] in
/-- **Helper**: additivity of `directionalDeriv` in the function argument:
$X(f + g)(x) = X(f)(x) + X(g)(x)$.

Wraps `mfderiv_add` for the framework's `directionalDeriv` helper. -/
private lemma directionalDeriv_add_fun
    (f g : M → ℝ) (x : M) (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    directionalDeriv (fun y => f y + g y) x v
      = directionalDeriv f x v + directionalDeriv g x v := by
  unfold directionalDeriv
  have heq : (fun y : M => f y + g y) = f + g := rfl
  rw [heq, mfderiv_add hf hg]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [hm : HasMetric I M] in
/-- **Helper**: additivity of `directionalDeriv` in the tangent vector argument:
$X_{v_1 + v_2}(f) = X_{v_1}(f) + X_{v_2}(f)$.

Wraps `ContinuousLinearMap.map_add` for `mfderiv` viewed as a linear map. -/
private lemma directionalDeriv_add_arg
    (f : M → ℝ) (x : M) (v₁ v₂ : TangentSpace I x) :
    directionalDeriv f x (v₁ + v₂)
      = directionalDeriv f x v₁ + directionalDeriv f x v₂ := by
  unfold directionalDeriv
  exact (mfderiv I 𝓘(ℝ, ℝ) f x).map_add v₁ v₂

omit [FiniteDimensional ℝ E] in
/-- **Koszul $C^\infty(M)$-linearity in $Z$**:
$$K(X, Y; f \cdot Z)(x) = f(x) \cdot K(X, Y; Z)(x).$$

Foundation of Riesz extraction: together with $\mathbb{R}$-linearity
in $Z$ and continuity, this property makes $\tfrac12 K(X, Y; \cdot)(x)$ a bounded
linear functional on $T_xM$, hence represented by a unique tangent vector
$\nabla_X Y(x)$ via the inner product.

**Smoothness hypotheses** (point-local at $x$):
* `hf`: `f` is smooth at `x`.
* `hYZ`: $\langle Y, Z\rangle$ is smooth at `x` (real-valued function).
* `hZX`: $\langle Z, X\rangle$ is smooth at `x` (real-valued function).
* `hZ`: `Z` is smooth at `x` as a section of `TangentBundle I M`.

The split-out scalar smoothness hypotheses on `⟨Y,Z⟩` and `⟨Z,X⟩` are needed
for the product rule on `f * inner_func`; they are derivable from vector-field
smoothness of `Y, Z, X` together with smoothness of the metric (a future
ergonomics improvement: bundle these into a single `IsSmoothRiemannianMetric`
hypothesis).

**Algebraic structure** (do Carmo §2 Theorem 3.6 existence proof, Step 2):
substituting $Z \mapsto f Z$ produces 6 expansion terms; the $X(f)$ and $Y(f)$
extra terms cancel pairwise by inner-product symmetry, leaving
$f \cdot K(X, Y; Z)$. This pairwise cancellation by `metricInner_comm` is the
fundamental tensoriality of Koszul.

**Ground truth**: do Carmo 1992 *Riemannian Geometry*, §2 Theorem 3.6
existence proof, Step 2 (cancellation calculation). -/
private theorem koszul_smul_right
    (X Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hYZ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x)
    (hZX : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X y)) x)
    (hZ : TangentSmoothAt Z x) :
    koszulFunctional X Y (fun y => f y • Z y) x = f x * koszulFunctional X Y Z x := by
  -- Step 1: factor `f` out of the inner products `⟨Y, fZ⟩` and `⟨fZ, X⟩`
  -- pointwise (these are the function-level rewrites that let the product rule fire).
  have h_inner_YfZ : (fun y : M => metricInner y (Y y) (f y • Z y))
                   = fun y => f y * metricInner y (Y y) (Z y) := by
    funext y; exact metricInner_smul_right y (f y) (Y y) (Z y)
  have h_inner_fZX : (fun y : M => metricInner y (f y • Z y) (X y))
                   = fun y => f y * metricInner y (Z y) (X y) := by
    funext y; exact metricInner_smul_left y (f y) (Z y) (X y)
  -- Step 2: convert pointwise smul back to Pi smul for `mlieBracket_smul_right`.
  have hPi : (fun y : M => f y • Z y) = (f • Z : Π y : M, TangentSpace I y) := rfl
  unfold koszulFunctional
  rw [h_inner_YfZ, h_inner_fZX]
  -- Step 3: apply Leibniz product rule to T1, T2 (terms with `f * inner_func`).
  rw [directionalDeriv_mul f (fun y => metricInner y (Y y) (Z y)) x (X x) hf hYZ]
  rw [directionalDeriv_mul f (fun y => metricInner y (Z y) (X y)) x (Y x) hf hZX]
  -- Step 4: T3 — pull `f x` out of the action vector via mfderiv linearity.
  -- (Beta-reduction `(fun y => f y • Z y) x = f x • Z x` is automatic.)
  rw [directionalDeriv_smul_arg (fun y => metricInner y (X y) (Y y)) x (f x) (Z x)]
  -- Step 5: T4 — pull `f x` out of `metricInner _ (f x • Z x)`.
  rw [metricInner_smul_right x (f x) (mlieBracket I X Y x) (Z x)]
  -- Step 6: T5, T6 — Lie bracket Leibniz; convert pointwise smul to Pi smul first.
  rw [hPi]
  rw [mlieBracket_smul_right (I := I) (V := Y) (W := Z) hf hZ]
  rw [mlieBracket_smul_right (I := I) (V := X) (W := Z) hf hZ]
  -- Step 7: distribute metricInner over the Leibniz sum + pull scalars out.
  -- After mlieBracket_smul_right: [V, f•Z] x = (df V) • Z x + f x • [V, Z] x
  -- where (df V) = fromTangentSpace (f x) (mfderiv f x (V x)) = directionalDeriv f x (V x)
  -- (since fromTangentSpace is the identity equiv on ℝ).
  simp only [metricInner_add_left, metricInner_smul_left]
  -- Step 8: align ⟨Z, Y⟩ = ⟨Y, Z⟩ for X(f) cancellation.
  have hZY : metricInner x (Z x) (Y x) = metricInner x (Y x) (Z x) := metricInner_comm x _ _
  rw [hZY]
  -- Step 9: unfold `directionalDeriv` so `fromTangentSpace _ (mfderiv ...) = mfderiv ...`
  -- (rfl by `fromTangentSpace.toFun v := v`), making X(f)/Y(f) terms align syntactically.
  unfold directionalDeriv
  have h_fromTS_X : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (X x) := rfl
  have h_fromTS_Y : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x) := rfl
  rw [h_fromTS_X, h_fromTS_Y]
  ring

/-! ## Additional koszul algebraic identities

Five identities establishing the koszul functional's additivity and
$C^\infty(M)$-linearity in the X and Y axes (Z-axis already covered by
`koszul_smul_right`). Each identity reduces, via
`koszulCovDeriv_inner_eq` + Riesz uniqueness, to a corresponding
Levi-Civita connection structural property (additivity, Leibniz). -/

omit [FiniteDimensional ℝ E] in
/-- **Koszul Z-additivity**: $K(X, Y; Z_1 + Z_2) = K(X, Y; Z_1) + K(X, Y; Z_2)$.

Each Koszul term is linear in $Z$ (via `metricInner_add_right`/`left`,
`mfderiv_add`, `mlieBracket_add_right`). -/
private theorem koszul_add_right
    (X Y Z₁ Z₂ : Π x : M, TangentSpace I x) (x : M)
    (h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z₁ y)) x)
    (h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z₂ y)) x)
    (h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z₁ y) (X y)) x)
    (h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z₂ y) (X y)) x)
    (h_Z₁ : TangentSmoothAt Z₁ x)
    (h_Z₂ : TangentSmoothAt Z₂ x) :
    koszulFunctional X Y (Z₁ + Z₂) x
      = koszulFunctional X Y Z₁ x + koszulFunctional X Y Z₂ x := by
  unfold koszulFunctional
  -- Step 1: split inner products with Z₁+Z₂ argument at function level.
  have h_YZ : (fun y : M => metricInner y (Y y) ((Z₁ + Z₂) y))
      = (fun y => metricInner y (Y y) (Z₁ y) + metricInner y (Y y) (Z₂ y)) := by
    funext y; rw [Pi.add_apply, metricInner_add_right]
  have h_ZX : (fun y : M => metricInner y ((Z₁ + Z₂) y) (X y))
      = (fun y => metricInner y (Z₁ y) (X y) + metricInner y (Z₂ y) (X y)) := by
    funext y; rw [Pi.add_apply, metricInner_add_left]
  rw [h_YZ, h_ZX]
  -- Step 2: split directionalDeriv over function addition (T1, T2).
  rw [directionalDeriv_add_fun (fun y => metricInner y (Y y) (Z₁ y))
        (fun y => metricInner y (Y y) (Z₂ y)) x (X x) h_YZ₁ h_YZ₂]
  rw [directionalDeriv_add_fun (fun y => metricInner y (Z₁ y) (X y))
        (fun y => metricInner y (Z₂ y) (X y)) x (Y x) h_Z₁X h_Z₂X]
  -- Step 3: split directionalDeriv on the action vector at point (T3).
  rw [show ((Z₁ + Z₂) x : TangentSpace I x) = Z₁ x + Z₂ x from rfl]
  rw [directionalDeriv_add_arg]
  -- Step 4: split inner product at point (T4).
  rw [metricInner_add_right]
  -- Step 5: split mlieBracket on right argument (T5, T6).
  rw [mlieBracket_add_right (V := Y) h_Z₁ h_Z₂]
  rw [mlieBracket_add_right (V := X) h_Z₁ h_Z₂]
  rw [metricInner_add_left, metricInner_add_left]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Koszul X-additivity**: $K(X_1 + X_2, Y; Z) = K(X_1, Y; Z) + K(X_2, Y; Z)$. -/
private theorem koszul_add_left
    (X₁ X₂ Y Z : Π x : M, TangentSpace I x) (x : M)
    (h_ZX₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X₁ y)) x)
    (h_ZX₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X₂ y)) x)
    (h_X₁Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X₁ y) (Y y)) x)
    (h_X₂Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X₂ y) (Y y)) x)
    (h_X₁ : TangentSmoothAt X₁ x)
    (h_X₂ : TangentSmoothAt X₂ x) :
    koszulFunctional (X₁ + X₂) Y Z x
      = koszulFunctional X₁ Y Z x + koszulFunctional X₂ Y Z x := by
  unfold koszulFunctional
  have h_ZX : (fun y : M => metricInner y (Z y) ((X₁ + X₂) y))
      = (fun y => metricInner y (Z y) (X₁ y) + metricInner y (Z y) (X₂ y)) := by
    funext y; rw [Pi.add_apply, metricInner_add_right]
  have h_XY : (fun y : M => metricInner y ((X₁ + X₂) y) (Y y))
      = (fun y => metricInner y (X₁ y) (Y y) + metricInner y (X₂ y) (Y y)) := by
    funext y; rw [Pi.add_apply, metricInner_add_left]
  rw [h_ZX, h_XY]
  -- T1: action vector (X₁+X₂) x at point.
  rw [show ((X₁ + X₂) x : TangentSpace I x) = X₁ x + X₂ x from rfl]
  rw [directionalDeriv_add_arg]
  -- T2: function addition.
  rw [directionalDeriv_add_fun (fun y => metricInner y (Z y) (X₁ y))
        (fun y => metricInner y (Z y) (X₂ y)) x (Y x) h_ZX₁ h_ZX₂]
  -- T3: function addition.
  rw [directionalDeriv_add_fun (fun y => metricInner y (X₁ y) (Y y))
        (fun y => metricInner y (X₂ y) (Y y)) x (Z x) h_X₁Y h_X₂Y]
  -- T4: mlieBracket on left argument (V axis).
  rw [mlieBracket_add_left (W := Y) h_X₁ h_X₂]
  rw [metricInner_add_left]
  -- T5: action vector (X₁+X₂) x at point.
  rw [metricInner_add_right]
  -- T6: mlieBracket on left argument.
  rw [mlieBracket_add_left (W := Z) h_X₁ h_X₂]
  rw [metricInner_add_left]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Koszul Y-additivity**: $K(X, Y_1 + Y_2; Z) = K(X, Y_1; Z) + K(X, Y_2; Z)$. -/
private theorem koszul_add_middle
    (X Y₁ Y₂ Z : Π x : M, TangentSpace I x) (x : M)
    (h_Y₁Z : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y₁ y) (Z y)) x)
    (h_Y₂Z : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y₂ y) (Z y)) x)
    (h_XY₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y₁ y)) x)
    (h_XY₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y₂ y)) x)
    (h_Y₁ : TangentSmoothAt Y₁ x)
    (h_Y₂ : TangentSmoothAt Y₂ x) :
    koszulFunctional X (Y₁ + Y₂) Z x
      = koszulFunctional X Y₁ Z x + koszulFunctional X Y₂ Z x := by
  unfold koszulFunctional
  have h_YZ : (fun y : M => metricInner y ((Y₁ + Y₂) y) (Z y))
      = (fun y => metricInner y (Y₁ y) (Z y) + metricInner y (Y₂ y) (Z y)) := by
    funext y; rw [Pi.add_apply, metricInner_add_left]
  have h_XY : (fun y : M => metricInner y (X y) ((Y₁ + Y₂) y))
      = (fun y => metricInner y (X y) (Y₁ y) + metricInner y (X y) (Y₂ y)) := by
    funext y; rw [Pi.add_apply, metricInner_add_right]
  rw [h_YZ, h_XY]
  -- T1: function addition.
  rw [directionalDeriv_add_fun (fun y => metricInner y (Y₁ y) (Z y))
        (fun y => metricInner y (Y₂ y) (Z y)) x (X x) h_Y₁Z h_Y₂Z]
  -- T2: action vector (Y₁+Y₂) x at point.
  rw [show ((Y₁ + Y₂) x : TangentSpace I x) = Y₁ x + Y₂ x from rfl]
  rw [directionalDeriv_add_arg]
  -- T3: function addition.
  rw [directionalDeriv_add_fun (fun y => metricInner y (X y) (Y₁ y))
        (fun y => metricInner y (X y) (Y₂ y)) x (Z x) h_XY₁ h_XY₂]
  -- T4: mlieBracket on right argument (Y axis).
  rw [mlieBracket_add_right (V := X) h_Y₁ h_Y₂]
  rw [metricInner_add_left]
  -- T5: mlieBracket on left argument (Y axis).
  rw [mlieBracket_add_left (W := Z) h_Y₁ h_Y₂]
  rw [metricInner_add_left]
  -- T6: action vector at point.
  rw [metricInner_add_right]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Koszul X-axis $C^\infty(M)$-linearity**:
$K(f \cdot X, Y; Z)(x) = f(x) \cdot K(X, Y; Z)(x)$.

Mirror of `koszul_smul_right` on the X axis. Same algebraic
structure: $Y(f)$ terms cancel via $\langle Z, X\rangle - \langle X, Z\rangle = 0$;
$Z(f)$ terms cancel via $\langle X, Y\rangle - \langle Y, X\rangle = 0$
(both by inner symmetry).

**Smoothness hypotheses**: `hf`, `h_ZX` (for T2 product rule), `h_XY` (for T3
product rule), `h_X` (for T4, T6 mlieBracket Leibniz). -/
private theorem koszul_smul_left
    (X Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X y)) x)
    (h_XY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y y)) x)
    (h_X : TangentSmoothAt X x) :
    koszulFunctional (fun y => f y • X y) Y Z x = f x * koszulFunctional X Y Z x := by
  -- Step 1: factor `f` out of the inner products with `f • X` argument.
  have h_inner_ZfX : (fun y : M => metricInner y (Z y) (f y • X y))
                   = fun y => f y * metricInner y (Z y) (X y) := by
    funext y; exact metricInner_smul_right y (f y) (Z y) (X y)
  have h_inner_fXY : (fun y : M => metricInner y (f y • X y) (Y y))
                   = fun y => f y * metricInner y (X y) (Y y) := by
    funext y; exact metricInner_smul_left y (f y) (X y) (Y y)
  have hPi : (fun y : M => f y • X y) = (f • X : Π y : M, TangentSpace I y) := rfl
  unfold koszulFunctional
  rw [h_inner_ZfX, h_inner_fXY]
  -- Step 2: T1 — pull `f x` out of the action vector.
  rw [directionalDeriv_smul_arg (fun y => metricInner y (Y y) (Z y)) x (f x) (X x)]
  -- Step 3: T2, T3 — apply Leibniz product rule.
  rw [directionalDeriv_mul f (fun y => metricInner y (Z y) (X y)) x (Y x) hf h_ZX]
  rw [directionalDeriv_mul f (fun y => metricInner y (X y) (Y y)) x (Z x) hf h_XY]
  -- Step 4: T5 — pull `f x` out of `metricInner _ (f x • X x)`.
  rw [metricInner_smul_right x (f x) (mlieBracket I Y Z x) (X x)]
  -- Step 5: T4, T6 — Lie bracket Leibniz on left arg.
  rw [hPi]
  rw [mlieBracket_smul_left (I := I) (W := Y) hf h_X]
  rw [mlieBracket_smul_left (I := I) (W := Z) hf h_X]
  -- Step 6: distribute metricInner over the Leibniz sum + pull scalars out.
  simp only [metricInner_add_left, metricInner_smul_left]
  -- Step 7: align inner symmetry for cancellation.
  have hZX : metricInner x (X x) (Z x) = metricInner x (Z x) (X x) :=
    metricInner_comm x (X x) (Z x)
  have hXY : metricInner x (X x) (Y x) = metricInner x (Y x) (X x) :=
    metricInner_comm x (X x) (Y x)
  rw [hZX, hXY]
  -- Step 8: unfold so fromTangentSpace identity rfl-aligns the X(f)/Y(f)/Z(f) terms.
  unfold directionalDeriv
  have h_fromTS_Y : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x) := rfl
  have h_fromTS_Z : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Z x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x) := rfl
  rw [h_fromTS_Y, h_fromTS_Z]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Koszul Y-axis Leibniz**:
$K(X, f \cdot Y; Z)(x) = f(x) \cdot K(X, Y; Z)(x) + 2 \cdot X(f)(x) \cdot \langle Y, Z\rangle(x)$.

Different from `koszul_smul_right`/`left`: $X(f)$ terms do NOT cancel — they
double via T1 (Leibniz on $X\langle f Y, Z\rangle = X(f)\langle Y, Z\rangle + f X\langle Y, Z\rangle$)
and T4 (Lie bracket Leibniz $[X, fY] = X(f) Y + f [X, Y]$). The $Z(f)$ terms
still cancel by inner symmetry.

This is the connection-Leibniz pattern that distinguishes Y-axis from X/Z axes:
$\nabla_X(fY) = X(f) Y + f \nabla_X Y$ (vs C∞-linear in X, Z).

**Smoothness hypotheses**: `hf`, `h_YZ`, `h_ZX`, `h_XY`, `h_Y`. -/
private theorem koszul_smul_middle
    (X Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x)
    (h_XY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y y)) x)
    (h_Y : TangentSmoothAt Y x) :
    koszulFunctional X (fun y => f y • Y y) Z x
      = f x * koszulFunctional X Y Z x
        + 2 * directionalDeriv f x (X x) * metricInner x (Y x) (Z x) := by
  -- Step 1: factor `f` out of the inner products with `f • Y` argument.
  have h_inner_fYZ : (fun y : M => metricInner y (f y • Y y) (Z y))
                   = fun y => f y * metricInner y (Y y) (Z y) := by
    funext y; exact metricInner_smul_left y (f y) (Y y) (Z y)
  have h_inner_XfY : (fun y : M => metricInner y (X y) (f y • Y y))
                   = fun y => f y * metricInner y (X y) (Y y) := by
    funext y; exact metricInner_smul_right y (f y) (X y) (Y y)
  have hPi : (fun y : M => f y • Y y) = (f • Y : Π y : M, TangentSpace I y) := rfl
  unfold koszulFunctional
  rw [h_inner_fYZ, h_inner_XfY]
  -- Step 2: T1, T3 — apply Leibniz product rule.
  rw [directionalDeriv_mul f (fun y => metricInner y (Y y) (Z y)) x (X x) hf h_YZ]
  rw [directionalDeriv_mul f (fun y => metricInner y (X y) (Y y)) x (Z x) hf h_XY]
  -- Step 3: T2 — pull `f x` out of action vector.
  rw [directionalDeriv_smul_arg (fun y => metricInner y (Z y) (X y)) x (f x) (Y x)]
  -- Step 4: T6 — pull `f x` out of `metricInner _ (f x • Y x)`.
  rw [metricInner_smul_right x (f x) (mlieBracket I X Z x) (Y x)]
  -- Step 5: T4 — Lie bracket Leibniz right; T5 — Lie bracket Leibniz left.
  rw [hPi]
  rw [mlieBracket_smul_right (I := I) (V := X) (W := Y) hf h_Y]
  rw [mlieBracket_smul_left (I := I) (W := Z) hf h_Y]
  -- Step 6: distribute metricInner over the Leibniz sum + pull scalars out.
  simp only [metricInner_add_left, metricInner_smul_left]
  -- Step 7: align inner symmetry — the Z(f) terms need ⟨Y, X⟩ = ⟨X, Y⟩.
  have hYX : metricInner x (Y x) (X x) = metricInner x (X x) (Y x) :=
    metricInner_comm x (Y x) (X x)
  rw [hYX]
  -- Step 8: unfold so fromTangentSpace identity rfl-aligns the X(f)/Z(f) terms.
  unfold directionalDeriv
  have h_fromTS_X : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (X x) := rfl
  have h_fromTS_Z : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Z x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x) := rfl
  rw [h_fromTS_X, h_fromTS_Z]
  ring

/-! ## from `Connection.lean` (private) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-! ## Helpers: flat-typed smoothness of `SmoothVectorField` and `metricInner` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [hm : HasMetric I M] in
set_option backward.isDefEq.respectTransparency false in
/-- A `SmoothVectorField`'s underlying `Y.toFun : Π y : M, T_yM` viewed as
`M → E` (via `T_yM = E` def-eq) is globally `ContMDiff` under
`IsLocallyConstantChartedSpace`. -/
private theorem SmoothVectorField.contMDiff_E (Y : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, E) ∞ Y.toFun := by
  intro x
  set e := trivializationAt E (TangentSpace I) x with he_def
  -- Bundle-section smoothness gives chart-coord smoothness via Trivialization.contMDiffAt_iff.
  have h_he : (Bundle.TotalSpace.mk x (Y.toFun x) : TangentBundle I M) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' (F := E) x
  have h_iff := Bundle.Trivialization.contMDiffAt_iff (IM := I) (IB := I) (e := e)
    (f := fun y : M => (Bundle.TotalSpace.mk y (Y.toFun y) : TangentBundle I M))
    (n := ∞) h_he
  have h_chart_coord : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y : M => (e ⟨y, Y.toFun y⟩).2) x :=
    (h_iff.mp (Y.smooth x)).2
  -- On baseSet, (e ⟨y, V y⟩).2 = e.continuousLinearMapAt R y (V y).
  -- Under IsLocallyConstantChartedSpace, e.cLMA R y = id near x, so equals V y.
  apply h_chart_coord.congr_of_eventuallyEq
  have h_baseSet : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_baseSet, h_chart_eq, h_chart_src] with y hy_base hy_eq hy_src
  show Y.toFun y = (e ⟨y, Y.toFun y⟩).2
  -- (e ⟨y, V y⟩).2 = e.continuousLinearMapAt R y (V y).
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy_base]
  -- e.continuousLinearMapAt R y = id near x via continuousLinearMapAtFlat = id (locally).
  show (Y.toFun y : E) = e.continuousLinearMapAt ℝ y (Y.toFun y)
  show (Y.toFun y : E) =
      TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y (Y.toFun y)
  -- continuousLinearMapAtFlat x y = id near x (locally constant chart).
  have h_id : TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
      = ContinuousLinearMap.id ℝ E := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y
        = ContinuousLinearMap.id ℝ E
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src]
    have h_achart_eq : achart H y = achart H x := Subtype.ext hy_eq
    rw [h_achart_eq]
    ext v
    exact (tangentBundleCore I M).coordChange_self (achart H x) y
      (by simpa [tangentBundleCore_baseSet] using hy_src) v
  rw [h_id]
  rfl

-- Smoothness of `metricInner` on bundle sections lives in `Manifold.lean`
-- as the public `Riemannian.metricInner_contMDiff` (parametric over `n`).

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M] [hm : HasMetric I M] in
/-- **MDifferentiableAt componentwise lift to CLM-valued**: if each component
`(fun y => T y (basis i)) : M → F₂` is `MDifferentiableAt` at `x`, then the
CLM-valued section `T : M → (F₁ →L[ℝ] F₂)` is `MDifferentiableAt` at `x`.

Proof: decompose `T y = ∑ i, (basis.coord i).toCLM.smulRight (T y (basis i))`,
each summand `MDifferentiableAt` via `clm_apply` of constant CLM `smulRightL`
with smooth scalar component, sum via `MDifferentiableAt.add`. -/
private theorem mdifferentiableAt_clm_of_components
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (T : M → F₁ →L[ℝ] F₂) {ι : Type} [Fintype ι]
    (basis : Module.Basis ι ℝ F₁) {x : M}
    (h_components : ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, F₂)
      (fun y : M => T y (basis i)) x) :
    MDifferentiableAt I 𝓘(ℝ, F₁ →L[ℝ] F₂) T x := by
  classical
  have h_decomp : T = fun y =>
      ∑ i, (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)) := by
    funext y
    ext v
    rw [ContinuousLinearMap.sum_apply]
    have hv : v = ∑ i, basis.repr v i • basis i := by simp
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      (T y).map_smul]
  rw [h_decomp]
  -- Convert (fun y => ∑ i, f i y) to (∑ i, fun y => f i y) for MDifferentiableAt.sum.
  have h_swap : (fun y : M => ∑ i,
      (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)))
      = (∑ i, fun y : M =>
          (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i))) := by
    funext y
    rw [Finset.sum_apply]
  rw [h_swap]
  apply MDifferentiableAt.sum
  intro i _
  -- Each summand: smulRight applied to scalar component.
  -- (basis.coord i).toCLM.smulRight : F₂ →L (F₁ →L F₂) is a CLM, hence smooth.
  have h_smulRightL : ContMDiff 𝓘(ℝ, F₂) 𝓘(ℝ, F₁ →L[ℝ] F₂) ∞
      (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w) := by
    have h_eq : (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w)
        = ContinuousLinearMap.smulRightL ℝ F₁ F₂ (basis.coord i).toContinuousLinearMap := by
      funext w; rfl
    rw [h_eq]
    exact (ContinuousLinearMap.smulRightL ℝ F₁ F₂
      (basis.coord i).toContinuousLinearMap).contMDiff
  -- Apply MDifferentiableAt.comp
  have h_smulRightL_at :
      MDifferentiableAt 𝓘(ℝ, F₂) 𝓘(ℝ, F₁ →L[ℝ] F₂)
        (fun w => (basis.coord i).toContinuousLinearMap.smulRight w) (T x (basis i)) :=
    (h_smulRightL (T x (basis i))).mdifferentiableAt (by decide)
  exact h_smulRightL_at.comp x (h_components i)

omit [FiniteDimensional ℝ E] [IsLocallyConstantChartedSpace H M] hm in
/-- **`mlieBracket` of two `ContMDiff` bundle sections is a smooth bundle section**.
Wrapper around Mathlib `ContMDiffAt.mlieBracket_vectorField` giving
`TangentSmoothAt` (framework's MDifferentiableAt-form predicate). -/
theorem mlieBracket_tangentSmoothAt
    {U V : (y : M) → TangentSpace I y} {x : M}
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, U y⟩ : TangentBundle I M)))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M))) :
    TangentSmoothAt (mlieBracket I U V) x := by
  -- IsManifold I a M auto-inferred from IsManifold I ∞ M + LEInfty a (Mathlib instance).
  haveI : IsManifold I (3 : ℕ∞ω) M := inferInstance
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  haveI hM_2plus1 : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    show IsManifold I (3 : ℕ∞ω) M
    infer_instance
  haveI : IsManifold I ((minSmoothness ℝ 2 : ℕ∞ω)) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have h_min : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ (2 : ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have hU2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, U y⟩ : TangentBundle I M)) x :=
    (hU x).of_le (by exact_mod_cast le_top)
  have hV2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x :=
    (hV x).of_le (by exact_mod_cast le_top)
  have h_mlb1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((1 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, mlieBracket I U V y⟩ : TangentBundle I M)) x :=
    hU2.mlieBracket_vectorField hV2 h_min
  exact h_mlb1.mdifferentiableAt (by decide)

/-- **Half-Koszul scalar value** $\tfrac12\,K(v_{\text{const}}, Y, w_{\text{const}})(y)$. -/
noncomputable def koszulCotangentScalar
    (v : E) (Y : SmoothVectorField I M) (w : E) (y : M) : ℝ :=
  (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y

/-- **Half-Koszul cotangent CLM** $w \mapsto \tfrac12\,K(v, Y; w)(y)$ as
`E →L[ℝ] ℝ`. Linearity in `w` via `koszul_smul_right` + `koszul_add_right`. -/
noncomputable def koszulCotangentCLM
    (v : E) (Y : SmoothVectorField I M) (y : M) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => koszulCotangentScalar v Y w y
      map_add' := by
        intro w₁ w₂
        unfold koszulCotangentScalar
        have hY_y : TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w₁ : TangentSmoothAt (fun _ : M => w₁) y :=
          (SmoothVectorField.const (I := I) (M := M) w₁).smoothAt y
        have h_const_w₂ : TangentSmoothAt (fun _ : M => w₂) y :=
          (SmoothVectorField.const (I := I) (M := M) w₂).smoothAt y
        have h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₁) y')) y :=
          metricInner_mdifferentiableAt hY_y h_const_w₁
        have h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₂) y')) y :=
          metricInner_mdifferentiableAt hY_y h_const_w₂
        have h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₁) y') ((fun _ : M => v) y')) y :=
          metricInner_mdifferentiableAt h_const_w₁
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₂) y') ((fun _ : M => v) y')) y :=
          metricInner_mdifferentiableAt h_const_w₂
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_add_factored :
            koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁ + w₂) y
              = koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁) y
                + koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₂) y := by
          have h_sum_eq : ((fun _ : M => w₁ + w₂) : ∀ z : M, TangentSpace I z)
              = (fun _ : M => w₁) + (fun _ : M => w₂) := by
            funext z; rfl
          rw [h_sum_eq]
          exact koszul_add_right (fun _ => v) Y.toFun (fun _ => w₁) (fun _ => w₂)
            y h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X h_const_w₁ h_const_w₂
        show (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun
              (fun _ : M => w₁ + w₂) y
            = (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁) y
              + (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₂) y
        rw [h_add_factored]
        ring
      map_smul' := by
        intro c w
        unfold koszulCotangentScalar
        -- Use koszul_smul_right with f = (const c).
        have hY_y : TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w : TangentSmoothAt (fun _ : M => w) y :=
          (SmoothVectorField.const (I := I) (M := M) w).smoothAt y
        have h_const_v : TangentSmoothAt (fun _ : M => v) y :=
          (SmoothVectorField.const (I := I) (M := M) v).smoothAt y
        have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => c) y :=
          mdifferentiableAt_const
        have h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w) y')) y :=
          metricInner_mdifferentiableAt hY_y h_const_w
        have h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w) y') ((fun _ : M => v) y')) y :=
          metricInner_mdifferentiableAt h_const_w h_const_v
        have h_smul_factored :
            koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => c • w) y
              = c * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y := by
          have h_eq : (fun _ : M => c • w : ∀ z : M, TangentSpace I z)
              = fun y' : M => (fun _ : M => c) y' • (fun _ : M => w) y' := by
            funext z; rfl
          rw [h_eq]
          exact koszul_smul_right (fun _ => v) Y.toFun (fun _ => w)
            (fun _ : M => c) y hf h_YZ h_ZX h_const_w
        show (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun
              (fun _ : M => c • w) y
            = (RingHom.id ℝ) c • ((1/2 : ℝ) *
                koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y)
        rw [h_smul_factored]
        simp
        ring }

@[simp]
lemma koszulCotangentCLM_apply (v : E) (Y : SmoothVectorField I M) (y : M) (w : E) :
    koszulCotangentCLM v Y y w = koszulCotangentScalar v Y w y := rfl

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Scalar smoothness of `koszulCotangentScalar v Y w` in `y`** at every `x`.

Decomposes into 6 koszul-term smoothness checks:
* 3 directional-derivative terms via `mfderiv_const_dir_smoothAt` /
  `mfderiv_smoothDir_smoothAt`.
* 3 mlieBracket-with-metric-inner terms via `mlieBracket_tangentSmoothAt` +
  `metricInner_mdifferentiableAt`.
Sum via `MDifferentiableAt.add` / `.sub` / `.const_mul`. -/
private theorem koszulCotangentScalar_mdifferentiableAt
    (v : E) (Y : SmoothVectorField I M) (w : E) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => koszulCotangentScalar v Y w y) x := by
  classical
  -- Function-form smoothness witnesses, used downstream for `mfderiv_*_smoothAt`.
  have hY_E : ContMDiff I 𝓘(ℝ, E) ∞ Y.toFun := SmoothVectorField.contMDiff_E Y
  -- Bundle-section smoothness witnesses, used by `metricInner_contMDiff`.
  have hY_bundle : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) := Y.smooth
  have h_const_v_bundle : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, v⟩ : TangentBundle I M)) :=
    (SmoothVectorField.const (I := I) (M := M) v).smooth
  have h_const_w_bundle : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, w⟩ : TangentBundle I M)) :=
    (SmoothVectorField.const (I := I) (M := M) w).smooth
  -- Scalar functions for terms 1, 2, 3 via metricInner_contMDiff.
  have h_f_YW : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => hm.metric.metricInner y' (Y.toFun y') w) :=
    metricInner_contMDiff hY_bundle h_const_w_bundle
  have h_f_WV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => hm.metric.metricInner y' w v) :=
    metricInner_contMDiff h_const_w_bundle h_const_v_bundle
  have h_f_VY : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => hm.metric.metricInner y' v (Y.toFun y')) :=
    metricInner_contMDiff h_const_v_bundle hY_bundle
  -- TangentSmoothAt for the 3 const + Y bundle sections.
  have hY_y : TangentSmoothAt Y.toFun x := Y.smoothAt x
  have h_const_v_y : TangentSmoothAt (fun _ : M => v) x :=
    (SmoothVectorField.const (I := I) (M := M) v).smoothAt x
  have h_const_w_y : TangentSmoothAt (fun _ : M => w) x :=
    (SmoothVectorField.const (I := I) (M := M) w).smoothAt x
  -- TangentSmoothAt of mlieBracket sections (T4, T5, T6).
  have h_mlb_vY : TangentSmoothAt
      (mlieBracket I (fun _ : M => v) Y.toFun) x :=
    mlieBracket_tangentSmoothAt
      (SmoothVectorField.const (I := I) (M := M) v).smooth Y.smooth
  have h_mlb_Yw : TangentSmoothAt
      (mlieBracket I Y.toFun (fun _ : M => w)) x :=
    mlieBracket_tangentSmoothAt Y.smooth
      (SmoothVectorField.const (I := I) (M := M) w).smooth
  have h_mlb_vw : TangentSmoothAt
      (mlieBracket I (fun _ : M => v) (fun _ : M => w)) x :=
    mlieBracket_tangentSmoothAt
      (SmoothVectorField.const (I := I) (M := M) v).smooth
      (SmoothVectorField.const (I := I) (M := M) w).smooth
  -- 6 koszul terms in mfderiv form (skip directionalDeriv unfold step).
  have hT1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner y' (Y.toFun y') w) y v) x :=
    mfderiv_const_dir_smoothAt h_f_YW x v
  have hT2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner y' w v) y (Y.toFun y)) x :=
    mfderiv_smoothDir_smoothAt h_f_WV (hY_E.contMDiffAt)
  have hT3 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner y' v (Y.toFun y')) y w) x :=
    mfderiv_const_dir_smoothAt h_f_VY x w
  have hT4 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner y (mlieBracket I (fun _ : M => v) Y.toFun y) w) x :=
    metricInner_mdifferentiableAt h_mlb_vY h_const_w_y
  have hT5 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner y (mlieBracket I Y.toFun (fun _ : M => w) y) v) x :=
    metricInner_mdifferentiableAt h_mlb_Yw h_const_v_y
  have hT6 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner y
        (mlieBracket I (fun _ : M => v) (fun _ : M => w) y) (Y.toFun y)) x :=
    metricInner_mdifferentiableAt h_mlb_vw hY_y
  -- koszulCotangentScalar unfolds to (1/2) * koszulFunctional.
  -- koszulFunctional unfolds to T1 + T2 - T3 + T4 - T5 - T6 (directionalDeriv = mfderiv by def).
  unfold koszulCotangentScalar koszulFunctional directionalDeriv
  -- Goal: MDifferentiableAt of `fun y => (1/2) * (T1 + T2 - T3 + T4 - T5 - T6)` at x.
  exact ((((((hT1.add hT2).sub hT3).add hT4).sub hT5).sub hT6).const_smul (1/2 : ℝ))

/-- **Smoothness of the koszul cotangent CLM section** as `M → (E →L[ℝ] ℝ)`.
Componentwise lift of `koszulCotangentScalar_mdifferentiableAt` via
`mdifferentiableAt_clm_of_components` with `Module.finBasis ℝ E`. -/
theorem koszulCotangentCLM_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => koszulCotangentCLM v Y y) x := by
  -- Componentwise lift: for each basis element b_i, the scalar
  -- (fun y => koszulCotangentCLM v Y y (b_i)) = (fun y => koszulCotangentScalar v Y b_i y)
  -- is MDifferentiableAt at x by koszulCotangentScalar_mdifferentiableAt.
  -- Lift to CLM via mdifferentiableAt_clm_of_components.
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  apply mdifferentiableAt_clm_of_components _ basis
  intro i
  show MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => koszulCotangentCLM v Y y (basis i)) x
  have h_eq : (fun y : M => koszulCotangentCLM v Y y (basis i))
      = (fun y : M => koszulCotangentScalar v Y (basis i) y) := by
    funext y
    exact koszulCotangentCLM_apply v Y y (basis i)
  rw [h_eq]
  exact koszulCotangentScalar_mdifferentiableAt v Y (basis i) x

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

omit [CompleteSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
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
private theorem koszulFunctional_local
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
/-- **Tensoriality at $x$ of the half-Koszul functional in the third argument.**


For smooth $X, Y$ at $x$, the operation
$Z \mapsto \tfrac12 K(X, Y; Z)(x)$ on smooth tangent-bundle sections
is tensorial at $x$: it respects $C^\infty(M)$-scalar multiplication
(via `koszul_smul_right`) and addition (via `koszul_add_right`).

The scalar smoothness hypotheses of `koszul_smul_right` /
`koszul_add_right` (`hYZ`, `hZX`, `h_YZ₁/₂`, `h_Z₁/₂X`) are derived
from the bundle-section smoothness of $X, Y, Z$ via
`metricInner_mdifferentiableAt`. -/
private theorem koszulFunctional_tensorialAt
    [FiniteDimensional ℝ E]
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π y : M, TangentSpace I y) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    TensorialAt I E (fun Z : (Π y : M, TangentSpace I y) =>
      (1/2 : ℝ) * koszulFunctional X Y Z x) x where
  smul := by
    intro f σ hf hσ
    have hYZ := metricInner_mdifferentiableAt hY hσ
    have hZX := metricInner_mdifferentiableAt hσ hX
    have heq : (f • σ : Π y : M, TangentSpace I y) = fun y => f y • σ y := rfl
    show (1/2 : ℝ) * koszulFunctional X Y (f • σ) x
        = f x • ((1/2 : ℝ) * koszulFunctional X Y σ x)
    rw [heq, koszul_smul_right X Y σ f x hf hYZ hZX hσ]
    show (1/2 : ℝ) * (f x * koszulFunctional X Y σ x)
        = f x * ((1/2 : ℝ) * koszulFunctional X Y σ x)
    ring
  add := by
    intro σ σ' hσ hσ'
    have h_YZ₁ := metricInner_mdifferentiableAt hY hσ
    have h_YZ₂ := metricInner_mdifferentiableAt hY hσ'
    have h_Z₁X := metricInner_mdifferentiableAt hσ hX
    have h_Z₂X := metricInner_mdifferentiableAt hσ' hX
    show (1/2 : ℝ) * koszulFunctional X Y (σ + σ') x
        = (1/2 : ℝ) * koszulFunctional X Y σ x
        + (1/2 : ℝ) * koszulFunctional X Y σ' x
    rw [koszul_add_right X Y σ σ' x h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X hσ hσ']
    ring

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
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

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
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
private noncomputable def koszulCovDeriv
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) : TangentSpace I x :=
  Classical.choose (koszulCovDeriv_exists X Y x hX hY)

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Riesz defining property**: $\langle \nabla_X Y(x), Z(x)\rangle =
\tfrac12 K(X, Y; Z)(x)$ for smooth $X, Y, Z$, with `metricInner` as the
framework-owned inner product.

Direct extraction via `Classical.choose_spec` from `koszulCovDeriv_exists`. -/
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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] in
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
/-- For `X, Y : SmoothVectorField I M`, the section
`y ↦ koszulCovDeriv X.toFun Y.toFun y` is `TangentSmoothAt` at every `x`.

This is the smooth-VF-direction strengthening of the original
`koszulCovDeriv_const_smoothAt` (constant `v : E` direction); the constant
case is recovered by specialising to `X := SmoothVectorField.const v`. The
generalisation is "free" from the underlying repair plan: closing
`metricRiesz_section_smoothAt` in full generality (for any smooth
linear-functional section, not just the constant case) closes both forms.

**Closure architecture** (post-Phase 4.7 + MusicalIso machinery):
1. Riesz uniqueness identifies `koszulCovDeriv X.toFun Y.toFun y _ _` with
   `metricRiesz y (Φ y)`, where `Φ y := TensorialAt.mkHom _ y
   (koszulFunctional_tensorialAt X.toFun Y.toFun y _ _)`.
2. Smoothness of `y ↦ metricRiesz y (Φ y)` at `x` reduces via
   `metricRiesz_section_contMDiffAt_of_within` (MusicalIso.lean primitive) to
   per-chart-basis-index `ContMDiffWithinAt` of `y ↦ Φ y (e_j y)` at `x`.
3. The chart-basis-index ContMDiffWithinAt follows from a bumped global
   extension `Z̃_j := chartBumpAt x • chartBasisVec x j` of the
   chartBasisVec section to a SmoothVectorField, on the bump's = 1
   neighbourhood. Each of the 6 koszulFunctional terms is then globally
   smooth via `mfderiv_apply_section_contMDiff` (3 directional derivative
   terms) and Mathlib's `ContMDiff.mlieBracket_vectorField` + metricInner
   smoothness (3 bracket terms). `koszulFunctional_local` transfers from
   the bumped global form to the original chartBasisVec form on a
   neighbourhood of `x`. -/
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

/-- Constant-direction specialisation of `koszulCovDeriv_smoothVF_smoothAt`. -/
private theorem koszulCovDeriv_const_smoothAt
    [IsLocallyConstantChartedSpace H M]
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => koszulCovDeriv (fun _ : M => v) Y.toFun y
        ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        (Y.smoothAt y)) x :=
  koszulCovDeriv_smoothVF_smoothAt (SmoothVectorField.const v) Y x

/-- **Existence theorem for the Levi-Civita connection.**

On a Riemannian manifold, there exists a covariant derivative on the
tangent bundle that is torsion-free and metric-compatible (for smooth
vector fields).

The metric-compat statement assumes smooth $X, Y, Z$ — matching do Carmo's
textbook setup; an unconditional form would be an over-statement.

**Smoothness clause** (3rd conjunct): for any pair of smooth tangent
sections `X, Y : SmoothVectorField I M`, the section
`y ↦ cov.toFun Y.toFun y (X.toFun y)` is `TangentSmoothAt` at every point.
This is the smooth-VF-direction form needed for downstream curvature
identities (`Bochner.lean` heart-of-Bochner chain); the constant-direction
case is recovered as `leviCivitaConnection_smoothAt_const_dir` via
`SmoothVectorField.const v`.

Closed via `hcov` eq spec + `koszulCovDeriv_smoothVF_smoothAt` (itself
PRE-PAPER, closed via Riesz uniqueness through `koszulCotangentCLM_smoothAt`
— the **single remaining PRE-PAPER sub-sorry** in the chain). Phase 1.6
invariant "zero existence axioms in the Riemannian package" preserved.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (existence + uniqueness via
the Koszul formula); Lee 2018 Prop. 4.26 (smoothness of covariant
derivative on smooth manifolds). -/
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
  (Classical.choose_spec leviCivitaConnection_exists).2.1 X Y Z x hX hY hZ

/-- **Smoothness of the Levi-Civita connection along a smooth vector
field direction**: for `X, Y : SmoothVectorField I M`, the section
`y ↦ ∇_{X(y)} Y(y) = leviCivitaConnection.toFun Y.toFun y (X.toFun y)`
is smooth at every point.

Direct projection from the 3rd conjunct of `leviCivitaConnection_exists`'s
strengthened existential. The smoothness clause itself is currently
`sorry` (PRE-PAPER) inside the existence proof; downstream consumers
(`Riemannian.Curvature`, `Riemannian.Operators.Bochner` smoothness
witnesses) depend on this accessor. -/
theorem leviCivitaConnection_smoothAt_smoothVF_dir
    [IsLocallyConstantChartedSpace H M]
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => (leviCivitaConnection (I := I) (M := M)).toFun Y.toFun y
        (X.toFun y)) x :=
  (Classical.choose_spec leviCivitaConnection_exists).2.2 X Y x

/-- **Constant-direction specialisation**: for `v : E` constant and
`Y : SmoothVectorField I M`, the section
`y ↦ ∇ Y y v = leviCivitaConnection.toFun Y.toFun y v` is smooth at every
point. Backward-compatible projection from
`leviCivitaConnection_smoothAt_smoothVF_dir` with `X := const v`. -/
theorem leviCivitaConnection_smoothAt_const_dir
    [IsLocallyConstantChartedSpace H M]
    (Y : SmoothVectorField I M) (v : E) (x : M) :
    TangentSmoothAt
      (fun y : M => (leviCivitaConnection (I := I) (M := M)).toFun Y.toFun y v) x :=
  leviCivitaConnection_smoothAt_smoothVF_dir
    (SmoothVectorField.const v) Y x

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

/-- The covariant derivative `∇[X] Y` as a section. Pointwise:
`(∇[X] Y)(x) = (∇_X Y)(x) = covDeriv X Y x`. -/
scoped[Riemannian] notation:max "∇[" X "] " Y:max => covDeriv X Y

/-- The manifold Lie bracket `⟦X, Y⟧` as a section. Model `I` inferred
from the section types. Pointwise: `(⟦X, Y⟧)(x) = mlieBracket _ X Y x`. -/
scoped[Riemannian] notation:max "⟦" X ", " Y "⟧" =>
  VectorField.mlieBracket _ X Y

/-- The **covariant derivative at a point** as a CLM in the direction slot:
$\nabla\,Y|_x : T_xM \to_L T_xM$, $v \mapsto (\nabla_v Y)(x)$. Decouples
linearity in the direction from the section-level `covDeriv`:
`covDeriv X Y x = covDerivAt Y x (X x)`, so any "linear in $X$ at $x$"
identity reduces to standard CLM lemmas (`map_add`, `map_smul`,
`map_zero`, `.comp`) on `covDerivAt Y x`. -/
noncomputable def covDerivAt
    [IsLocallyConstantChartedSpace H M]
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (leviCivitaConnection (I := I) (M := M)).toFun Y x

/-- `covDeriv X Y x = covDerivAt Y x (X x)`: section-level `covDeriv`
factors through the pointwise CLM `covDerivAt`. -/
@[simp]
theorem covDeriv_eq_covDerivAt
    [IsLocallyConstantChartedSpace H M]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    covDeriv X Y x = covDerivAt Y x (X x) :=
  rfl

/-- Constant-section specialization: `covDeriv (fun _ => v) Y x =
covDerivAt Y x v`. Used when only the value of the direction at $x$
matters (tensoriality of $\nabla_X Y$ in $X$). -/
@[simp]
theorem covDeriv_const_eq_covDerivAt
    [IsLocallyConstantChartedSpace H M]
    (v : E) (Y : Π x : M, TangentSpace I x) (x : M) :
    covDeriv (fun _ : M => v) Y x = covDerivAt Y x v :=
  rfl

/-- **Riesz formula for the covariant derivative**: for smooth $X, Y, Z$,
$$\langle \nabla_X Y, Z\rangle_g(x) = \tfrac12 K(X, Y; Z)(x).$$

Standard Levi-Civita derivation: cycling the metric-compat identity over
$(X, Y, Z)$, $(Y, Z, X)$, $(Z, X, Y)$ and substituting torsion-freeness
$\nabla_Y X = \nabla_X Y - [X, Y]$ etc. isolates
$\langle \nabla_X Y, Z\rangle$. -/
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
/-- **Locality of `koszulFunctional` in the middle argument**: if
$Y_1 =ᶠ[𝓝 x] Y_2$, then $K(X, Y_1; Z)(x) = K(X, Y_2; Z)(x)$.

All 6 terms are local at `x`:
* 3 directional derivative terms: 2 functions depend on $Y$ via metric
  inner products (use `Filter.EventuallyEq.mfderiv_eq`); 1 uses $Y(x)$ as
  the direction (constant from `EventuallyEq` evaluated at `x`).
* 3 Lie-bracket inner-product terms: the bracket
  `mlieBracket I · Y ·` is local in `Y` at `x`. -/
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

/-- **Locality of `covDeriv` in the middle argument** (Riesz uniqueness):
if $Y_1 =ᶠ[𝓝 x] Y_2$ and both are smooth at $x$, then for smooth $X$,
$\nabla_X Y_1(x) = \nabla_X Y_2(x)$. -/
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

/-- **Pointwise torsion-freeness** of the Levi-Civita connection:
$\nabla_X Y - \nabla_Y X = [X, Y]$ at any point where $X, Y$ are
differentiable as bundle sections. -/
theorem covDeriv_sub_swap_eq_mlieBracket
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    (∇[X] Y) x - (∇[Y] X) x = (⟦X, Y⟧) x :=
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
    (∇[X] (Y₁ + Y₂)) x = (∇[X] Y₁) x + (∇[X] Y₂) x := by
  have h := leviCivitaConnection.isCovariantDerivativeOnUniv.add (σ := Y₁) (σ' := Y₂)
    (x := x) hY₁ hY₂
  show (leviCivitaConnection.toFun (Y₁ + Y₂) x) (X x)
    = (leviCivitaConnection.toFun Y₁ x) (X x) + (leviCivitaConnection.toFun Y₂ x) (X x)
  rw [h]
  rfl

/-- **Locality of `covDeriv` in the differentiated field**: if
$Y_1 =ᶠ[𝓝 x] Y_2$ and both are smooth at $x$, then
$\nabla_X Y_1(x) = \nabla_X Y_2(x)$.

Direct application of `IsCovariantDerivativeOn.congr_of_eventuallyEq` to the
Levi-Civita connection. Smoothness of the direction `X` is not required:
the section-level connection `leviCivitaConnection.toFun Y x` is a CLM in
the direction slot, so the value at `X x` depends only on `Y` near `x`. -/
theorem covDeriv_congr_eventuallyEq_field
    (X Y₁ Y₂ : Π x : M, TangentSpace I x) (x : M)
    (hY₁ : TangentSmoothAt Y₁ x) (hY₂ : TangentSmoothAt Y₂ x)
    (h : ∀ᶠ y in 𝓝 x, Y₁ y = Y₂ y) :
    (∇[X] Y₁) x = (∇[X] Y₂) x := by
  show (leviCivitaConnection.toFun Y₁ x) (X x)
      = (leviCivitaConnection.toFun Y₂ x) (X x)
  rw [leviCivitaConnection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hY₁ hY₂ Filter.univ_mem h]

/-- **`covDeriv` of a constant scalar multiple in the differentiated field**:
$\nabla_X (a \cdot Y)(x) = a \cdot \nabla_X Y(x)$ for $a : \mathbb{R}$.

Direct from `IsCovariantDerivativeOn.smul_const`. -/
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

/-- **Subtractivity of `covDeriv` in the differentiated field**:
$\nabla_X (Y_1 - Y_2)(x) = \nabla_X Y_1(x) - \nabla_X Y_2(x)$.

Derived from additivity + `smul_const a := -1`. -/
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

/-- **Leibniz rule (`C^∞`-linearity in differentiated section): the connection
acts as a derivation in the scalar factor of `g • Y`**:
$$\nabla_X (g \cdot Y)(x) = g(x) \cdot \nabla_X Y(x) + (\mathrm{d}g \cdot X)(x) \cdot Y(x).$$

Directly lifted from Mathlib's `IsCovariantDerivativeOn.leibniz` applied to
`leviCivitaConnection.isCovariantDerivativeOnUniv`, then projected onto the
direction `X(x)`. The `extDerivFun g x v = mfderiv g x v` reduction is
definitional via `NormedSpace.fromTangentSpace` (the identity bridge on the
scalar tangent space `TangentSpace 𝓘(ℝ, ℝ) (g x) ≃L ℝ`). -/
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

/-- The **Riemann curvature tensor**:
$R(X, Y)Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.

Connection-level definition: only `covDeriv` (Levi-Civita) and `mlieBracket`
appear. Metric-dependent properties (full antisymmetry, Ricci as trace,
sectional curvature) belong in `Riemannian.Curvature`.

**Ground truth**: do Carmo 1992 §4 Definition 2.1. -/
noncomputable def riemannCurvature
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  covDeriv X (covDeriv Y Z) x - covDeriv Y (covDeriv X Z) x
    - covDeriv (mlieBracket I X Y) Z x

/-- The Riemann curvature `Riem(X, Y) Z` as a section. Pointwise:
`(Riem(X, Y) Z)(x) = R(X, Y) Z(x) = riemannCurvature X Y Z x`. -/
scoped[Riemannian] notation:max "Riem(" X ", " Y ") " Z:max =>
  riemannCurvature X Y Z

/-! ### `riem_simp` lemmas

Two rewrites that drive the `riem_simp` simp set, populated for the
Riemann curvature operator built from the framework's `covDeriv`. Together
with `abel` they discharge the algebraic identities of `riemannCurvature`
without exposing the underlying connection plumbing. -/

/-- **Definitional unfold** of `riemannCurvature` to its
$\nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$ form.
Pure rewrite — no smoothness hypotheses.

LHS uses `riemannCurvature` literal: this lemma lives in Bianchi, where
the post-Bianchi `Riem(X, Y) Z` notation (in `Util/Notation/Curvature`)
is not yet declared. RHS uses `covDeriv X Y` and `VectorField.mlieBracket I X Y` (pre-Bianchi tier,
imported from `Util/Notation/Connection`). -/
@[riem_simp]
theorem riemannCurvature_def
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x
      = covDeriv X (covDeriv Y Z) x - covDeriv Y (covDeriv X Z) x
        - covDeriv (VectorField.mlieBracket I X Y) Z x := rfl

/-- **Lie-bracket antisymmetry pulled through the connection's direction
argument**: $\nabla_{[Y,X]} Z = -\nabla_{[X,Y]} Z$ pointwise. Combines
`VectorField.mlieBracket_swap_apply` with the ℝ-linearity of
`leviCivitaConnection.toFun Z x` (a CLM, so it commutes with negation).
Pure rewrite — no smoothness hypotheses.

Used as an explicit `rw` step (not in `riem_simp`): the rewrite is
symmetric in `X ↔ Y`, so adding it to a simp set causes loop. -/
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

/-! ## from `Connection.lean` (smoothness section) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- $\nabla_{\,\mathrm{const}\,v}\, Y$ is smooth at every $x$ for any
`SmoothVectorField Y` and any chart-frame constant direction $v$. -/
theorem covDeriv_const_smoothVF_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => covDeriv (fun _ : M => v) Y.toFun y) x :=
  Riemannian.leviCivitaConnection_smoothAt_const_dir Y v x

/-- $\nabla_X Y$ is smooth at every $x$ for any smooth vector fields
`X, Y : SmoothVectorField I M`. Smooth-VF-direction strengthening of
`covDeriv_const_smoothVF_smoothAt`; primary infrastructure consumer is
the Bochner–Weitzenböck heart-of-Bochner chain
(`Riemannian.Operators.Bochner`). -/
theorem covDeriv_smoothVF_smoothAt
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => covDeriv X.toFun Y.toFun y) x :=
  Riemannian.leviCivitaConnection_smoothAt_smoothVF_dir X Y x

end Riemannian
