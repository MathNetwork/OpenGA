import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Riemannian.Metric.Basic
import Riemannian.Metric.Smooth

/-!
# Koszul functional + algebraic identities

The Koszul functional $K(X, Y; Z) : M \to \mathbb{R}$ encodes the
Levi-Civita connection: $\nabla_X Y$ is the unique vector with
$\langle \nabla_X Y, Z \rangle = \tfrac12 K(X, Y; Z)$ for all smooth $Z$.

This file defines `koszulFunctional` and proves the foundational
algebraic identities (anti-symmetry, metric compatibility,
$C^\infty(M)$-linearity in each argument, locality in $Z$). The Riesz
extraction → Levi-Civita construction lives in
`Riemannian/Connection/LeviCivita.lean`.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (Levi-Civita theorem,
existence + uniqueness via the Koszul formula).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold
open OpenGALib

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianMetric I M]

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
noncomputable def directionalDeriv
    (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f x v

/-- The **Koszul functional** $K(X, Y; Z) : M \to \mathbb{R}$ as defined
above. Implementation uses the helper `directionalDeriv` to keep each
$X\langle Y, Z\rangle$ term typed as `ℝ` (avoiding the `TangentSpace 𝓘(ℝ,ℝ) (f x)`
basepoint mismatch under `HAdd` synthesis). The framework-owned
`metricInner` provides the inner product on tangent vectors. -/
noncomputable def koszulFunctional
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x)
  + directionalDeriv (fun y => metricInner y (Z y) (X y)) x (Y x)
  - directionalDeriv (fun y => metricInner y (X y) (Y y)) x (Z x)
  + metricInner x (mlieBracket I X Y x) (Z x)
  - metricInner x (mlieBracket I Y Z x) (X x)
  - metricInner x (mlieBracket I X Z x) (Y x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
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
theorem koszul_antisymm
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

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
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
theorem koszul_metric_compat_sum
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
  [RiemannianMetric I M] in
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
  [RiemannianMetric I M] in
/-- **Helper**: linearity of `directionalDeriv` in the tangent vector argument:
$X_{a \cdot v}(f) = a \cdot X_v(f)$.

Wraps `ContinuousLinearMap.map_smul` for `mfderiv` viewed as a linear map. -/
private lemma directionalDeriv_smul_arg
    (g : M → ℝ) (x : M) (a : ℝ) (v : TangentSpace I x) :
    directionalDeriv g x (a • v) = a * directionalDeriv g x v := by
  unfold directionalDeriv
  exact (mfderiv I 𝓘(ℝ, ℝ) g x).map_smul a v

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianMetric I M] in
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
  [RiemannianMetric I M] in
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
theorem koszul_smul_right
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
theorem koszul_add_right
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
theorem koszul_add_left
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
theorem koszul_add_middle
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
theorem koszul_smul_left
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
theorem koszul_smul_middle
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

end Riemannian
