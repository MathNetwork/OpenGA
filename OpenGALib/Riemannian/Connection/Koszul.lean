import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import OpenGALib.Riemannian.Manifold.SmoothManifold
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.Util.Metric.MetricInnerSmoothness
/-!
# Koszul functional and its algebraic identities

The Koszul functional $K(X, Y; Z) : M \to \mathbb{R}$ encodes the
Levi-Civita connection: $\nabla_X Y$ is the unique tangent vector with
$\langle \nabla_X Y, Z \rangle = \tfrac12 K(X, Y; Z)$ for all $Z$.

This module contains the **paper-side math base** of the Koszul story:
* the functional definition
* eight algebraic identities (anti-symmetry, metric-compatibility sum,
  $C^\infty(M)$-linearity in $Z$, additivity in all three slots, scalar
  multiplication in all three slots, Y-axis Leibniz)
* locality in $Z$ (`koszulFunctional_local`)
* tensoriality in $Z$ packaged as `TensorialAt` (`koszulFunctional_tensorialAt`)

`Connection.lean` (anchor) imports this file and feeds the
algebraic identities into Riesz extraction → `koszulCovDeriv` →
`leviCivitaConnection`. The Engineering-tax helpers
(`directionalDeriv` wrapper + its 4 Leibniz lemmas) live alongside the
Math content here because the 8 identities are stated in terms of them.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6.
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace Riemannian

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

/-- **Math.** Directional derivative of a scalar function `f : M → ℝ` at
`x` in direction `v : TangentSpace I x`. Thin wrapper around `mfderiv`
typed to `ℝ` to avoid `TangentSpace 𝓘(ℝ, ℝ) (f x)` basepoint mismatches
when composing Koszul-functional terms. -/
noncomputable def directionalDeriv
    (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f x v

/-- **Math.** The **Koszul functional** $K(X, Y; Z) : M \to \mathbb{R}$:
$$K(X, Y; Z)(x) \;=\; X\langle Y, Z\rangle\,(x) + Y\langle Z, X\rangle\,(x)
  - Z\langle X, Y\rangle\,(x) + \langle [X, Y], Z\rangle\,(x)
  - \langle [Y, Z], X\rangle\,(x) - \langle [X, Z], Y\rangle\,(x).$$

The Levi-Civita connection $\nabla_X Y$ is determined by Riesz
representation of $Z \mapsto \tfrac12 K(X, Y; Z)(x)$ via the inner
product on $T_xM$. Here $X\langle Y, Z\rangle$ denotes the directional
derivative of $y \mapsto \langle Y(y), Z(y)\rangle$ in direction
$X(x)$ at $x$.

**Ground truth**: do Carmo 1992 §2 (Koszul formula in the proof of
Theorem 3.6). -/
noncomputable def koszulFunctional
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) : ℝ :=
  directionalDeriv (fun y => g.metricInner y (Y y) (Z y)) x (X x)
  + directionalDeriv (fun y => g.metricInner y (Z y) (X y)) x (Y x)
  - directionalDeriv (fun y => g.metricInner y (X y) (Y y)) x (Z x)
  + g.metricInner x (mlieBracket I X Y x) (Z x)
  - g.metricInner x (mlieBracket I Y Z x) (X x)
  - g.metricInner x (mlieBracket I X Z x) (Y x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul antisymmetry identity**:
$$K(X, Y; Z)(x) - K(Y, X; Z)(x) \;=\; 2\,\langle [X, Y], Z\rangle(x).$$

Foundation of the torsion-free property (LC1): under Riesz, $\nabla_X Y$
satisfies $\langle \nabla_X Y, Z\rangle = \tfrac12 K(X, Y; Z)$, so
$\langle \nabla_X Y - \nabla_Y X, Z\rangle = \langle [X, Y], Z\rangle$
holds for all $Z$, hence $\nabla_X Y - \nabla_Y X = [X, Y]$.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 proof. -/
theorem koszul_antisymm
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) :
    koszulFunctional g X Y Z x - koszulFunctional g Y X Z x
      = 2 * g.metricInner x (mlieBracket I X Y x) (Z x) := by
  unfold koszulFunctional
  -- Inner symmetry as function equalities (so mfderiv values match pairwise).
  have hZY_YZ :
      (fun y : M => g.metricInner y (Z y) (Y y))
        = fun y => g.metricInner y (Y y) (Z y) := by
    funext y; exact g.metricInner_comm y _ _
  have hXZ_ZX :
      (fun y : M => g.metricInner y (X y) (Z y))
        = fun y => g.metricInner y (Z y) (X y) := by
    funext y; exact g.metricInner_comm y _ _
  have hYX_XY :
      (fun y : M => g.metricInner y (Y y) (X y))
        = fun y => g.metricInner y (X y) (Y y) := by
    funext y; exact g.metricInner_comm y _ _
  rw [hZY_YZ, hXZ_ZX, hYX_XY]
  -- Lie-bracket swap on the (Y, X) bracket.
  rw [show mlieBracket I Y X x = -mlieBracket I X Y x from mlieBracket_swap_apply]
  rw [g.metricInner_neg_left]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul metric-compatibility sum identity**:
$$K(X, Y; Z)(x) + K(X, Z; Y)(x) \;=\; 2\,X\langle Y, Z\rangle(x).$$

Foundation of metric-compatibility (LC2): under Riesz,
$\langle \nabla_X Y, Z\rangle + \langle Y, \nabla_X Z\rangle =
X\langle Y, Z\rangle$, i.e., $\nabla_X\langle Y,Z\rangle =
\langle \nabla_X Y,Z\rangle + \langle Y,\nabla_X Z\rangle$.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 proof. -/
theorem koszul_metric_compat_sum
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) :
    koszulFunctional g X Y Z x + koszulFunctional g X Z Y x
      = 2 * directionalDeriv (fun y => g.metricInner y (Y y) (Z y)) x (X x) := by
  unfold koszulFunctional
  -- Inner symmetry as function equalities.
  have hZY_YZ :
      (fun y : M => g.metricInner y (Z y) (Y y))
        = fun y => g.metricInner y (Y y) (Z y) := by
    funext y; exact g.metricInner_comm y _ _
  have hYX_XY :
      (fun y : M => g.metricInner y (Y y) (X y))
        = fun y => g.metricInner y (X y) (Y y) := by
    funext y; exact g.metricInner_comm y _ _
  have hXZ_ZX :
      (fun y : M => g.metricInner y (X y) (Z y))
        = fun y => g.metricInner y (Z y) (X y) := by
    funext y; exact g.metricInner_comm y _ _
  rw [hZY_YZ, hYX_XY, hXZ_ZX]
  -- Lie-bracket swap on the (Z, Y) bracket inside K(X, Z; Y).
  rw [show mlieBracket I Z Y x = -mlieBracket I Y Z x from mlieBracket_swap_apply]
  rw [g.metricInner_neg_left]
  ring
/-! ## Koszul $C^\infty(M)$-linearity in $Z$

The Koszul functional $K(X, Y; Z)(x)$, viewed as a map of $Z$, is
$C^\infty(M)$-linear:
$$K(X, Y; f \cdot Z)(x) = f(x) \cdot K(X, Y; Z)(x).$$

This is the key tensorial property enabling Riesz extraction: a
$C^\infty(M)$-linear functional on $\mathfrak{X}(M)$ descends to a
fibrewise linear functional on $T_xM$ and is represented by a unique
vector field via the Riemannian metric. The $X(f) / Y(f)$ pairwise
cancellation by inner-product symmetry is why Levi-Civita is a tensor
in $Z$ but not in $X$.
-/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [hm : HasMetric I M] in
/-- **Eng.** Leibniz product rule for `directionalDeriv` on $\mathbb{R}$-valued
functions: $X(f \cdot g)(x) = f(x) \cdot X(g)(x) + g(x) \cdot X(f)(x)$.
Wraps Mathlib's `HasMFDerivAt.mul` for the framework wrapper. -/
lemma directionalDeriv_mul
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
/-- **Eng.** Linearity of `directionalDeriv` in the tangent vector argument:
$X_{a \cdot v}(f) = a \cdot X_v(f)$. Wraps `ContinuousLinearMap.map_smul`. -/
lemma directionalDeriv_smul_arg
    (g : M → ℝ) (x : M) (a : ℝ) (v : TangentSpace I x) :
    directionalDeriv g x (a • v) = a * directionalDeriv g x v := by
  unfold directionalDeriv
  exact (mfderiv I 𝓘(ℝ, ℝ) g x).map_smul a v

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [hm : HasMetric I M] in
/-- **Eng.** Additivity of `directionalDeriv` in the function argument:
$X(f + g)(x) = X(f)(x) + X(g)(x)$. Wraps `mfderiv_add`. -/
lemma directionalDeriv_add_fun
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
/-- **Eng.** Additivity of `directionalDeriv` in the tangent vector argument:
$X_{v_1 + v_2}(f) = X_{v_1}(f) + X_{v_2}(f)$. Wraps `map_add`. -/
lemma directionalDeriv_add_arg
    (f : M → ℝ) (x : M) (v₁ v₂ : TangentSpace I x) :
    directionalDeriv f x (v₁ + v₂)
      = directionalDeriv f x v₁ + directionalDeriv f x v₂ := by
  unfold directionalDeriv
  exact (mfderiv I 𝓘(ℝ, ℝ) f x).map_add v₁ v₂

omit [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul $C^\infty(M)$-linearity in $Z$**:
$$K(X, Y; f \cdot Z)(x) = f(x) \cdot K(X, Y; Z)(x).$$

Foundation of Riesz extraction: $\tfrac12 K(X, Y; \cdot)(x)$ is a
bounded linear functional on $T_xM$, hence represented by a unique
tangent vector $\nabla_X Y(x)$ via the inner product.

The scalar smoothness hypotheses on `⟨Y,Z⟩` and `⟨Z,X⟩` are needed for
the product rule on `f * inner_func`; they are derivable from vector-field
smoothness of `Y, Z, X` together with smoothness of the metric.

**Ground truth**: do Carmo 1992 *Riemannian Geometry*, §2 Theorem 3.6
existence proof, Step 2 (cancellation calculation). -/
theorem koszul_smul_right
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hYZ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y y) (Z y)) x)
    (hZX : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Z y) (X y)) x)
    (hZ : TangentSmoothAt Z x) :
    koszulFunctional g X Y (fun y => f y • Z y) x
      = f x * koszulFunctional g X Y Z x := by
  -- Step 1: factor `f` out of the inner products `⟨Y, fZ⟩` and `⟨fZ, X⟩`
  -- pointwise (these are the function-level rewrites that let the product rule fire).
  have h_inner_YfZ : (fun y : M => g.metricInner y (Y y) (f y • Z y))
                   = fun y => f y * g.metricInner y (Y y) (Z y) := by
    funext y; exact g.metricInner_smul_right y (f y) (Y y) (Z y)
  have h_inner_fZX : (fun y : M => g.metricInner y (f y • Z y) (X y))
                   = fun y => f y * g.metricInner y (Z y) (X y) := by
    funext y; exact g.metricInner_smul_left y (f y) (Z y) (X y)
  -- Step 2: convert pointwise smul back to Pi smul for `mlieBracket_smul_right`.
  have hPi : (fun y : M => f y • Z y) = (f • Z : VectorFieldSection I M) := rfl
  unfold koszulFunctional
  rw [h_inner_YfZ, h_inner_fZX]
  -- Step 3: apply Leibniz product rule to T1, T2 (terms with `f * inner_func`).
  rw [directionalDeriv_mul f (fun y => g.metricInner y (Y y) (Z y)) x (X x) hf hYZ]
  rw [directionalDeriv_mul f (fun y => g.metricInner y (Z y) (X y)) x (Y x) hf hZX]
  -- Step 4: T3 — pull `f x` out of the action vector via mfderiv linearity.
  -- (Beta-reduction `(fun y => f y • Z y) x = f x • Z x` is automatic.)
  rw [directionalDeriv_smul_arg (fun y => g.metricInner y (X y) (Y y)) x (f x) (Z x)]
  -- Step 5: T4 — pull `f x` out of `g.metricInner _ (f x • Z x)`.
  rw [g.metricInner_smul_right x (f x) (mlieBracket I X Y x) (Z x)]
  -- Step 6: T5, T6 — Lie bracket Leibniz; convert pointwise smul to Pi smul first.
  rw [hPi]
  rw [mlieBracket_smul_right (I := I) (V := Y) (W := Z) hf hZ]
  rw [mlieBracket_smul_right (I := I) (V := X) (W := Z) hf hZ]
  -- Step 7: distribute g.metricInner over the Leibniz sum + pull scalars out.
  -- After mlieBracket_smul_right: [V, f•Z] x = (df V) • Z x + f x • [V, Z] x
  -- where (df V) = fromTangentSpace (f x) (mfderiv f x (V x)) = directionalDeriv f x (V x)
  -- (since fromTangentSpace is the identity equiv on ℝ).
  simp only [g.metricInner_add_left, g.metricInner_smul_left]
  -- Step 8: align ⟨Z, Y⟩ = ⟨Y, Z⟩ for X(f) cancellation.
  have hZY : g.metricInner x (Z x) (Y x) = g.metricInner x (Y x) (Z x) := g.metricInner_comm x _ _
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

omit [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul Z-additivity**: $K(X, Y; Z_1 + Z_2) = K(X, Y; Z_1) + K(X, Y; Z_2)$.

Each Koszul term is linear in $Z$ (via `g.metricInner_add_right`/`left`,
`mfderiv_add`, `mlieBracket_add_right`). -/
theorem koszul_add_right
    (g : RiemannianMetric I M)
    (X Y Z₁ Z₂ : VectorFieldSection I M) (x : M)
    (h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y y) (Z₁ y)) x)
    (h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y y) (Z₂ y)) x)
    (h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Z₁ y) (X y)) x)
    (h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Z₂ y) (X y)) x)
    (h_Z₁ : TangentSmoothAt Z₁ x)
    (h_Z₂ : TangentSmoothAt Z₂ x) :
    koszulFunctional g X Y (Z₁ + Z₂) x
      = koszulFunctional g X Y Z₁ x + koszulFunctional g X Y Z₂ x := by
  unfold koszulFunctional
  -- Step 1: split inner products with Z₁+Z₂ argument at function level.
  have h_YZ : (fun y : M => g.metricInner y (Y y) ((Z₁ + Z₂) y))
      = (fun y => g.metricInner y (Y y) (Z₁ y) + g.metricInner y (Y y) (Z₂ y)) := by
    funext y; rw [Pi.add_apply, g.metricInner_add_right]
  have h_ZX : (fun y : M => g.metricInner y ((Z₁ + Z₂) y) (X y))
      = (fun y => g.metricInner y (Z₁ y) (X y) + g.metricInner y (Z₂ y) (X y)) := by
    funext y; rw [Pi.add_apply, g.metricInner_add_left]
  rw [h_YZ, h_ZX]
  -- Step 2: split directionalDeriv over function addition (T1, T2).
  rw [directionalDeriv_add_fun (fun y => g.metricInner y (Y y) (Z₁ y))
        (fun y => g.metricInner y (Y y) (Z₂ y)) x (X x) h_YZ₁ h_YZ₂]
  rw [directionalDeriv_add_fun (fun y => g.metricInner y (Z₁ y) (X y))
        (fun y => g.metricInner y (Z₂ y) (X y)) x (Y x) h_Z₁X h_Z₂X]
  -- Step 3: split directionalDeriv on the action vector at point (T3).
  rw [show ((Z₁ + Z₂) x : TangentSpace I x) = Z₁ x + Z₂ x from rfl]
  rw [directionalDeriv_add_arg]
  -- Step 4: split inner product at point (T4).
  rw [g.metricInner_add_right]
  -- Step 5: split mlieBracket on right argument (T5, T6).
  rw [mlieBracket_add_right (V := Y) h_Z₁ h_Z₂]
  rw [mlieBracket_add_right (V := X) h_Z₁ h_Z₂]
  rw [g.metricInner_add_left, g.metricInner_add_left]
  ring

omit [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul X-additivity**: $K(X_1 + X_2, Y; Z) = K(X_1, Y; Z) + K(X_2, Y; Z)$. -/
theorem koszul_add_left
    (g : RiemannianMetric I M)
    (X₁ X₂ Y Z : VectorFieldSection I M) (x : M)
    (h_ZX₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Z y) (X₁ y)) x)
    (h_ZX₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Z y) (X₂ y)) x)
    (h_X₁Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (X₁ y) (Y y)) x)
    (h_X₂Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (X₂ y) (Y y)) x)
    (h_X₁ : TangentSmoothAt X₁ x)
    (h_X₂ : TangentSmoothAt X₂ x) :
    koszulFunctional g (X₁ + X₂) Y Z x
      = koszulFunctional g X₁ Y Z x + koszulFunctional g X₂ Y Z x := by
  unfold koszulFunctional
  have h_ZX : (fun y : M => g.metricInner y (Z y) ((X₁ + X₂) y))
      = (fun y => g.metricInner y (Z y) (X₁ y) + g.metricInner y (Z y) (X₂ y)) := by
    funext y; rw [Pi.add_apply, g.metricInner_add_right]
  have h_XY : (fun y : M => g.metricInner y ((X₁ + X₂) y) (Y y))
      = (fun y => g.metricInner y (X₁ y) (Y y) + g.metricInner y (X₂ y) (Y y)) := by
    funext y; rw [Pi.add_apply, g.metricInner_add_left]
  rw [h_ZX, h_XY]
  -- T1: action vector (X₁+X₂) x at point.
  rw [show ((X₁ + X₂) x : TangentSpace I x) = X₁ x + X₂ x from rfl]
  rw [directionalDeriv_add_arg]
  -- T2: function addition.
  rw [directionalDeriv_add_fun (fun y => g.metricInner y (Z y) (X₁ y))
        (fun y => g.metricInner y (Z y) (X₂ y)) x (Y x) h_ZX₁ h_ZX₂]
  -- T3: function addition.
  rw [directionalDeriv_add_fun (fun y => g.metricInner y (X₁ y) (Y y))
        (fun y => g.metricInner y (X₂ y) (Y y)) x (Z x) h_X₁Y h_X₂Y]
  -- T4: mlieBracket on left argument (V axis).
  rw [mlieBracket_add_left (W := Y) h_X₁ h_X₂]
  rw [g.metricInner_add_left]
  -- T5: action vector (X₁+X₂) x at point.
  rw [g.metricInner_add_right]
  -- T6: mlieBracket on left argument.
  rw [mlieBracket_add_left (W := Z) h_X₁ h_X₂]
  rw [g.metricInner_add_left]
  ring

omit [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul Y-additivity**: $K(X, Y_1 + Y_2; Z) = K(X, Y_1; Z) + K(X, Y_2; Z)$. -/
theorem koszul_add_middle
    (g : RiemannianMetric I M)
    (X Y₁ Y₂ Z : VectorFieldSection I M) (x : M)
    (h_Y₁Z : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y₁ y) (Z y)) x)
    (h_Y₂Z : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y₂ y) (Z y)) x)
    (h_XY₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (X y) (Y₁ y)) x)
    (h_XY₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (X y) (Y₂ y)) x)
    (h_Y₁ : TangentSmoothAt Y₁ x)
    (h_Y₂ : TangentSmoothAt Y₂ x) :
    koszulFunctional g X (Y₁ + Y₂) Z x
      = koszulFunctional g X Y₁ Z x + koszulFunctional g X Y₂ Z x := by
  unfold koszulFunctional
  have h_YZ : (fun y : M => g.metricInner y ((Y₁ + Y₂) y) (Z y))
      = (fun y => g.metricInner y (Y₁ y) (Z y) + g.metricInner y (Y₂ y) (Z y)) := by
    funext y; rw [Pi.add_apply, g.metricInner_add_left]
  have h_XY : (fun y : M => g.metricInner y (X y) ((Y₁ + Y₂) y))
      = (fun y => g.metricInner y (X y) (Y₁ y) + g.metricInner y (X y) (Y₂ y)) := by
    funext y; rw [Pi.add_apply, g.metricInner_add_right]
  rw [h_YZ, h_XY]
  -- T1: function addition.
  rw [directionalDeriv_add_fun (fun y => g.metricInner y (Y₁ y) (Z y))
        (fun y => g.metricInner y (Y₂ y) (Z y)) x (X x) h_Y₁Z h_Y₂Z]
  -- T2: action vector (Y₁+Y₂) x at point.
  rw [show ((Y₁ + Y₂) x : TangentSpace I x) = Y₁ x + Y₂ x from rfl]
  rw [directionalDeriv_add_arg]
  -- T3: function addition.
  rw [directionalDeriv_add_fun (fun y => g.metricInner y (X y) (Y₁ y))
        (fun y => g.metricInner y (X y) (Y₂ y)) x (Z x) h_XY₁ h_XY₂]
  -- T4: mlieBracket on right argument (Y axis).
  rw [mlieBracket_add_right (V := X) h_Y₁ h_Y₂]
  rw [g.metricInner_add_left]
  -- T5: mlieBracket on left argument (Y axis).
  rw [mlieBracket_add_left (W := Z) h_Y₁ h_Y₂]
  rw [g.metricInner_add_left]
  -- T6: action vector at point.
  rw [g.metricInner_add_right]
  ring

omit [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul X-axis $C^\infty(M)$-linearity**:
$K(f \cdot X, Y; Z)(x) = f(x) \cdot K(X, Y; Z)(x)$.

Mirror of `koszul_smul_right` on the X axis. Same algebraic
structure: $Y(f)$ terms cancel via $\langle Z, X\rangle - \langle X, Z\rangle = 0$;
$Z(f)$ terms cancel via $\langle X, Y\rangle - \langle Y, X\rangle = 0$
(both by inner symmetry).

**Smoothness hypotheses**: `hf`, `h_ZX` (for T2 product rule), `h_XY` (for T3
product rule), `h_X` (for T4, T6 mlieBracket Leibniz). -/
theorem koszul_smul_left
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Z y) (X y)) x)
    (h_XY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (X y) (Y y)) x)
    (h_X : TangentSmoothAt X x) :
    koszulFunctional g (fun y => f y • X y) Y Z x
      = f x * koszulFunctional g X Y Z x := by
  -- Step 1: factor `f` out of the inner products with `f • X` argument.
  have h_inner_ZfX : (fun y : M => g.metricInner y (Z y) (f y • X y))
                   = fun y => f y * g.metricInner y (Z y) (X y) := by
    funext y; exact g.metricInner_smul_right y (f y) (Z y) (X y)
  have h_inner_fXY : (fun y : M => g.metricInner y (f y • X y) (Y y))
                   = fun y => f y * g.metricInner y (X y) (Y y) := by
    funext y; exact g.metricInner_smul_left y (f y) (X y) (Y y)
  have hPi : (fun y : M => f y • X y) = (f • X : VectorFieldSection I M) := rfl
  unfold koszulFunctional
  rw [h_inner_ZfX, h_inner_fXY]
  -- Step 2: T1 — pull `f x` out of the action vector.
  rw [directionalDeriv_smul_arg (fun y => g.metricInner y (Y y) (Z y)) x (f x) (X x)]
  -- Step 3: T2, T3 — apply Leibniz product rule.
  rw [directionalDeriv_mul f (fun y => g.metricInner y (Z y) (X y)) x (Y x) hf h_ZX]
  rw [directionalDeriv_mul f (fun y => g.metricInner y (X y) (Y y)) x (Z x) hf h_XY]
  -- Step 4: T5 — pull `f x` out of `g.metricInner _ (f x • X x)`.
  rw [g.metricInner_smul_right x (f x) (mlieBracket I Y Z x) (X x)]
  -- Step 5: T4, T6 — Lie bracket Leibniz on left arg.
  rw [hPi]
  rw [mlieBracket_smul_left (I := I) (W := Y) hf h_X]
  rw [mlieBracket_smul_left (I := I) (W := Z) hf h_X]
  -- Step 6: distribute g.metricInner over the Leibniz sum + pull scalars out.
  simp only [g.metricInner_add_left, g.metricInner_smul_left]
  -- Step 7: align inner symmetry for cancellation.
  have hZX : g.metricInner x (X x) (Z x) = g.metricInner x (Z x) (X x) :=
    g.metricInner_comm x (X x) (Z x)
  have hXY : g.metricInner x (X x) (Y x) = g.metricInner x (Y x) (X x) :=
    g.metricInner_comm x (X x) (Y x)
  rw [hZX, hXY]
  -- Step 8: unfold so fromTangentSpace identity rfl-aligns the X(f)/Y(f)/Z(f) terms.
  unfold directionalDeriv
  have h_fromTS_Y : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x) := rfl
  have h_fromTS_Z : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Z x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x) := rfl
  rw [h_fromTS_Y, h_fromTS_Z]
  ring

omit [FiniteDimensional ℝ E] hm in
/-- **Math.** **Koszul Y-axis Leibniz**:
$K(X, f \cdot Y; Z)(x) = f(x) \cdot K(X, Y; Z)(x) + 2 \cdot X(f)(x) \cdot \langle Y, Z\rangle(x)$.

Different from `koszul_smul_right`/`left`: $X(f)$ terms do NOT cancel — they
double via T1 (Leibniz on $X\langle f Y, Z\rangle = X(f)\langle Y, Z\rangle + f X\langle Y, Z\rangle$)
and T4 (Lie bracket Leibniz $[X, fY] = X(f) Y + f [X, Y]$). The $Z(f)$ terms
still cancel by inner symmetry.

This is the connection-Leibniz pattern that distinguishes Y-axis from X/Z axes:
$\nabla_X(fY) = X(f) Y + f \nabla_X Y$ (vs C∞-linear in X, Z).

**Smoothness hypotheses**: `hf`, `h_YZ`, `h_ZX`, `h_XY`, `h_Y`. -/
theorem koszul_smul_middle
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (Y y) (Z y)) x)
    (h_XY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g.metricInner y (X y) (Y y)) x)
    (h_Y : TangentSmoothAt Y x) :
    koszulFunctional g X (fun y => f y • Y y) Z x
      = f x * koszulFunctional g X Y Z x
        + 2 * directionalDeriv f x (X x) * g.metricInner x (Y x) (Z x) := by
  -- Step 1: factor `f` out of the inner products with `f • Y` argument.
  have h_inner_fYZ : (fun y : M => g.metricInner y (f y • Y y) (Z y))
                   = fun y => f y * g.metricInner y (Y y) (Z y) := by
    funext y; exact g.metricInner_smul_left y (f y) (Y y) (Z y)
  have h_inner_XfY : (fun y : M => g.metricInner y (X y) (f y • Y y))
                   = fun y => f y * g.metricInner y (X y) (Y y) := by
    funext y; exact g.metricInner_smul_right y (f y) (X y) (Y y)
  have hPi : (fun y : M => f y • Y y) = (f • Y : VectorFieldSection I M) := rfl
  unfold koszulFunctional
  rw [h_inner_fYZ, h_inner_XfY]
  -- Step 2: T1, T3 — apply Leibniz product rule.
  rw [directionalDeriv_mul f (fun y => g.metricInner y (Y y) (Z y)) x (X x) hf h_YZ]
  rw [directionalDeriv_mul f (fun y => g.metricInner y (X y) (Y y)) x (Z x) hf h_XY]
  -- Step 3: T2 — pull `f x` out of action vector.
  rw [directionalDeriv_smul_arg (fun y => g.metricInner y (Z y) (X y)) x (f x) (Y x)]
  -- Step 4: T6 — pull `f x` out of `g.metricInner _ (f x • Y x)`.
  rw [g.metricInner_smul_right x (f x) (mlieBracket I X Z x) (Y x)]
  -- Step 5: T4 — Lie bracket Leibniz right; T5 — Lie bracket Leibniz left.
  rw [hPi]
  rw [mlieBracket_smul_right (I := I) (V := X) (W := Y) hf h_Y]
  rw [mlieBracket_smul_left (I := I) (W := Z) hf h_Y]
  -- Step 6: distribute g.metricInner over the Leibniz sum + pull scalars out.
  simp only [g.metricInner_add_left, g.metricInner_smul_left]
  -- Step 7: align inner symmetry — the Z(f) terms need ⟨Y, X⟩ = ⟨X, Y⟩.
  have hYX : g.metricInner x (Y x) (X x) = g.metricInner x (X x) (Y x) :=
    g.metricInner_comm x (Y x) (X x)
  rw [hYX]
  -- Step 8: unfold so fromTangentSpace identity rfl-aligns the X(f)/Z(f) terms.
  unfold directionalDeriv
  have h_fromTS_X : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (X x) := rfl
  have h_fromTS_Z : NormedSpace.fromTangentSpace (f x)
      ((mfderiv I 𝓘(ℝ, ℝ) f x) (Z x)) = (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x) := rfl
  rw [h_fromTS_X, h_fromTS_Z]
  ring

/-! ## Locality and tensoriality of the Koszul functional

These two properties feed Riesz extraction: locality gives
extension-independence of the functional, tensoriality packages it as
`TensorialAt` for `mkHom`.
-/

omit [CompleteSpace E] [FiniteDimensional ℝ E] hm
  in
/-- **Math.** **Locality of the Koszul functional in $Z$**: if $Z_1, Z_2$
agree on a neighborhood of $x$, then $K(X, Y; Z_1)(x) = K(X, Y; Z_2)(x)$.

Foundation for extension-independence: combined with bump decomposition,
gives well-definedness of the linear functional in
`koszulLinearFunctional_exists`. -/
theorem koszulFunctional_local
    (g : RiemannianMetric I M)
    (X Y Z₁ Z₂ : VectorFieldSection I M) (x : M)
    (h : Z₁ =ᶠ[nhds x] Z₂) :
    koszulFunctional g X Y Z₁ x = koszulFunctional g X Y Z₂ x := by
  have hZx : Z₁ x = Z₂ x := h.self_of_nhds
  unfold koszulFunctional directionalDeriv
  have hT1 : (fun y => g.metricInner y (Y y) (Z₁ y))
      =ᶠ[nhds x] fun y => g.metricInner y (Y y) (Z₂ y) := by
    filter_upwards [h] with y hy; rw [hy]
  have hT2 : (fun y => g.metricInner y (Z₁ y) (X y))
      =ᶠ[nhds x] fun y => g.metricInner y (Z₂ y) (X y) := by
    filter_upwards [h] with y hy; rw [hy]
  have hT5 : mlieBracket I Y Z₁ x = mlieBracket I Y Z₂ x :=
    (Filter.EventuallyEq.refl (nhds x) Y).mlieBracket_vectorField_eq h
  have hT6 : mlieBracket I X Z₁ x = mlieBracket I X Z₂ x :=
    (Filter.EventuallyEq.refl (nhds x) X).mlieBracket_vectorField_eq h
  rw [hT1.mfderiv_eq, hT2.mfderiv_eq, hZx, hT5, hT6]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] hm
  in
/-- **Mixed.** Tensoriality at $x$ of the half-Koszul functional in the
third argument. Math: $Z \mapsto \tfrac12 K(X, Y; Z)(x)$ respects
$C^\infty(M)$-scalar multiplication and addition. Eng: packaged as
`TensorialAt` so `TensorialAt.mkHom` can extract the bounded linear
functional; scalar smoothness side-hypotheses are derived from the
bundle-section smoothness of $X, Y, Z$. -/
theorem koszulFunctional_tensorialAt
    [FiniteDimensional ℝ E]
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (X Y : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    TensorialAt I E (fun Z : (VectorFieldSection I M) =>
      (1/2 : ℝ) * koszulFunctional g X Y Z x) x where
  smul := by
    intro f σ hf hσ
    have hYZ := g.metricInner_mdifferentiableAt hY hσ
    have hZX := g.metricInner_mdifferentiableAt hσ hX
    have heq : (f • σ : VectorFieldSection I M) = fun y => f y • σ y := rfl
    show (1/2 : ℝ) * koszulFunctional g X Y (f • σ) x
        = f x • ((1/2 : ℝ) * koszulFunctional g X Y σ x)
    rw [heq, koszul_smul_right g X Y σ f x hf hYZ hZX hσ]
    show (1/2 : ℝ) * (f x * koszulFunctional g X Y σ x)
        = f x * ((1/2 : ℝ) * koszulFunctional g X Y σ x)
    ring
  add := by
    intro σ σ' hσ hσ'
    have h_YZ₁ := g.metricInner_mdifferentiableAt hY hσ
    have h_YZ₂ := g.metricInner_mdifferentiableAt hY hσ'
    have h_Z₁X := g.metricInner_mdifferentiableAt hσ hX
    have h_Z₂X := g.metricInner_mdifferentiableAt hσ' hX
    show (1/2 : ℝ) * koszulFunctional g X Y (σ + σ') x
        = (1/2 : ℝ) * koszulFunctional g X Y σ x
        + (1/2 : ℝ) * koszulFunctional g X Y σ' x
    rw [koszul_add_right g X Y σ σ' x h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X hσ hσ']
    ring

end Riemannian
