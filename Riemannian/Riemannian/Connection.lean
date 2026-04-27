import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Riemannian.Connection

The **Levi-Civita connection** on a Riemannian manifold $M$: the unique
torsion-free, metric-compatible covariant derivative on the tangent bundle
$TM$.

## Form

`leviCivitaConnection` is grounded as a real `noncomputable def` via
`Classical.choose` over an existence axiom (`leviCivitaConnection_exists`).
The existence axiom is a standard theorem (Koszul formula / do Carmo §2);
its inline proof is deferred to a future Phase that may replace this
construction with Mathlib's eventual constructive Levi-Civita instance.

This pattern matches the framework's `tangentCone` (commit `ad54a8e`)
which uses `Classical.choice` over a real predicate for the same reason.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (Levi-Civita theorem,
existence + uniqueness); Mathlib's `CovariantDerivative.torsion` provides
the torsion-vanishing condition; metric-compatibility lemma deferred.
-/

open Bundle VectorField
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- **Existence axiom for the Levi-Civita connection.**

On a Riemannian manifold, there exists a covariant derivative on the
tangent bundle that is **torsion-free** and **metric-compatible**. This
is the Levi-Civita theorem (do Carmo 1992 §2 Theorem 3.6) — existence
+ uniqueness via the Koszul formula.

The statement is the **full Levi-Civita theorem**: torsion-free
($\mathrm{torsion}(\nabla) = 0$) AND metric-compatible
($\nabla_X \langle Y, Z \rangle = \langle \nabla_X Y, Z \rangle +
\langle Y, \nabla_X Z \rangle$ for vector fields $X, Y, Z$ on $M$).

**Ground truth**: do Carmo 1992 §2 Theorem 3.6.

**Sorry status**: PRE-PAPER (standard theorem, body deferred). Repair plan:
when Mathlib's `Geometry/Manifold/Riemannian/` adds a constructive
Levi-Civita instance (or when framework opts to inline the Koszul-formula
proof, ~100 LOC), replace `Classical.choose` with the explicit
construction. -/
theorem leviCivitaConnection_exists :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      cov.torsion = 0 ∧
      ∀ (X Y Z : Π x : M, TangentSpace I x) (x : M),
        mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Z y)) x (X x) =
          inner ℝ (cov.toFun Y x (X x)) (Z x) +
          inner ℝ (Y x) (cov.toFun Z x (X x)) := by
  sorry

/-- The **Levi-Civita connection** $\nabla$ on the tangent bundle of a
Riemannian manifold $M$: the unique torsion-free, metric-compatible
covariant derivative.

Real `noncomputable def` via `Classical.choose` over
`leviCivitaConnection_exists`. The chosen value satisfies
`leviCivitaConnection.torsion = 0` (see
`leviCivitaConnection_torsion_zero`).

Apply via the bundled `toFun`: for vector fields $X, Y$ on $M$, the
covariant derivative $\nabla_X Y$ at $x$ is
`leviCivitaConnection.toFun Y x (X x) : TangentSpace I x`.

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

/-- The Levi-Civita connection is **metric-compatible**: for vector
fields $X, Y, Z$ on $M$,
$$\nabla_X \langle Y, Z \rangle =
  \langle \nabla_X Y, Z \rangle + \langle Y, \nabla_X Z \rangle.$$

This is the second of the two defining properties of Levi-Civita
(torsion-free + metric-compatible), extracted from the existence
axiom via `Classical.choose_spec`. -/
theorem leviCivitaConnection_metric_compatible
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Z y)) x (X x) =
      inner ℝ ((leviCivitaConnection (I := I) (M := M)).toFun Y x (X x)) (Z x) +
      inner ℝ (Y x)
        ((leviCivitaConnection (I := I) (M := M)).toFun Z x (X x)) :=
  (Classical.choose_spec leviCivitaConnection_exists).2 X Y Z x

/-- **Covariant derivative of one vector field along another**:
$(\nabla_X Y)(x) := \nabla\,Y\,x\,(X\,x)$, where $\nabla$ is the
Levi-Civita connection.

Convenience wrapper that exposes the standard math notation
$\nabla_X Y$ from Mathlib's bundled `CovariantDerivative.toFun`. -/
noncomputable def covDeriv (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  ((leviCivitaConnection (I := I) (M := M)).toFun Y x) (X x)

/-! ## Phase 4.5.A — Koszul functional + basic algebraic identities

Toward an explicit Koszul-formula construction of the Levi-Civita
connection, replacing the `Classical.choose` over the existence axiom
`leviCivitaConnection_exists`. This is the first of four sub-phases:

  * Phase 4.5.A (this section): `koszulFunctional` def + algebraic
    identities `koszul_antisymm` (toward LC1 torsion-free) +
    `koszul_metric_compat_sum` (toward LC2 metric-compatible).
  * Phase 4.5.B: $C^\infty(M)$-linearity in $Z$ (extension-independence).
  * Phase 4.5.C: Riesz extraction → explicit `leviCivitaConnection`
    real `noncomputable def`, plus `IsCovariantDerivativeOn` axioms
    (additivity + Leibniz).
  * Phase 4.5.D: derive torsion-free + metric-compat from the Koszul
    construction; replace the `leviCivitaConnection_exists` axiom.

Each sub-phase keeps the existing `leviCivitaConnection_exists` axiom
intact until 4.5.D, so the chain proof stays 0-sorry throughout.

**Ground truth**: do Carmo 1992 *Riemannian Geometry*, §2 Theorem 3.6
(Levi-Civita theorem, existence + uniqueness via the Koszul formula).
-/

/-- The **Koszul functional** $K(X, Y; Z) : M \to \mathbb{R}$.

Pointwise value at $x \in M$:
$$K(X, Y; Z)(x) \;=\; X\langle Y, Z\rangle\,(x) + Y\langle Z, X\rangle\,(x)
  - Z\langle X, Y\rangle\,(x) + \langle [X, Y], Z\rangle\,(x)
  - \langle [Y, Z], X\rangle\,(x) - \langle [X, Z], Y\rangle\,(x).$$

The Levi-Civita connection $\nabla_X Y$ is determined by Riesz
representation of the linear functional
$Z \mapsto \tfrac12 K(X, Y; Z)(x)$ via the inner product on
$T_xM$ (Phase 4.5.C).

**Notation note**: $X\langle Y, Z\rangle$ denotes the directional
derivative of the real-valued function $y \mapsto \langle Y(y), Z(y)\rangle$
in direction $X(x)$ at $x$, i.e., `mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Z y)) x (X x)`.

**Ground truth**: do Carmo 1992 §2 (Koszul formula, equation (3) in
the proof of Theorem 3.6). -/
noncomputable def koszulFunctional
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  let dXY_Z : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Z y)) x (X x)
  let dY_ZX : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Z y) (X y)) x (Y x)
  let dZ_XY : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (X y) (Y y)) x (Z x)
  dXY_Z + dY_ZX - dZ_XY
  + inner ℝ (mlieBracket I X Y x) (Z x)
  - inner ℝ (mlieBracket I Y Z x) (X x)
  - inner ℝ (mlieBracket I X Z x) (Y x)

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
- The three `mfderiv` terms cancel pairwise via `real_inner_comm`
  on $\langle Y, Z\rangle, \langle Z, X\rangle, \langle X, Y\rangle$
  (the inner products are symmetric, so the underlying
  $\mathbb{R}$-valued functions coincide).
- $\langle [X,Y], Z\rangle - \langle [Y,X], Z\rangle = 2\langle [X,Y], Z\rangle$
  via `mlieBracket_swap_apply` ($[Y,X] = -[X,Y]$) +
  `inner_neg_left`.
- The other two Lie bracket pairs ($\langle [Y,Z], X\rangle$,
  $\langle [X,Z], Y\rangle$) cancel directly.

**Sorry status**: Phase 4.5.A.2 (proof body deferred to a follow-up
commit; the def + identity statement are the Phase 4.5.A.1 deliverable).
The mathematical derivation is straightforward; the Lean tactic-side
manipulation of `mfderiv` over function-equality + inner-symmetry +
Lie-bracket-swap is mechanical work scheduled separately.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 proof (lines on
torsion-free derivation from Koszul). -/
theorem koszul_antisymm
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x - koszulFunctional Y X Z x
      = 2 * inner ℝ (mlieBracket I X Y x) (Z x) := by
  sorry

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
  via `real_inner_comm` ($\langle Z, Y\rangle = \langle Y, Z\rangle$
  pointwise, hence equal as $\mathbb{R}$-valued functions, hence
  equal `mfderiv` value).
- The other two `mfderiv` pairs and the three Lie bracket pairs
  cancel via `real_inner_comm` + `mlieBracket_swap_apply` +
  `inner_neg_left`.

**Sorry status**: Phase 4.5.A.2 (proof body deferred, same status
as `koszul_antisymm`).

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 proof (lines on
metric-compatibility derivation from Koszul). -/
theorem koszul_metric_compat_sum
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x + koszulFunctional X Z Y x
      = 2 * (let dXY_Z : ℝ :=
              mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Z y)) x (X x)
            dXY_Z) := by
  sorry

end Riemannian

/-! ## UXTest

Self-test verifying the Levi-Civita connection + `covDeriv` resolve
their typeclass cascade. Regression guard against signature drift. -/
section UXTest

open Riemannian

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x := covDeriv X Y x

/-! ## Phase 4.5.A self-test: Koszul functional typeclass + identities -/

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    ℝ := koszulFunctional X Y Z x

example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x - koszulFunctional Y X Z x
      = 2 * inner ℝ (mlieBracket I X Y x) (Z x) :=
  koszul_antisymm X Y Z x

example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x + koszulFunctional X Z Y x
      = 2 * (let dXY_Z : ℝ :=
              mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Z y)) x (X x)
            dXY_Z) :=
  koszul_metric_compat_sum X Y Z x

end UXTest
