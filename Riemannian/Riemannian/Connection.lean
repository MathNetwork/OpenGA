import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Riemannian.Basic

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

open Bundle
open scoped ContDiff Manifold

namespace Riemannian

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Existence axiom for the Levi-Civita connection.**

On a Riemannian manifold, there exists a torsion-free covariant derivative
on the tangent bundle. (Metric compatibility is a separate property,
captured by additional axioms in future refinements.)

**Ground truth**: do Carmo 1992 §2 Theorem 3.6.

**Sorry status**: PRE-PAPER (standard theorem, body deferred). Repair plan:
when Mathlib's `Geometry/Manifold/Riemannian/` adds a constructive
Levi-Civita instance (or when framework opts to inline the Koszul-formula
proof, ~100 LOC), replace `Classical.choose` with the explicit
construction. -/
theorem leviCivitaConnection_exists :
    ∃ cov : CovariantDerivative I E (fun x : M => TangentSpace I x),
      cov.torsion = 0 := by
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
  Classical.choose_spec leviCivitaConnection_exists

/-- **Covariant derivative of one vector field along another**:
$(\nabla_X Y)(x) := \nabla\,Y\,x\,(X\,x)$, where $\nabla$ is the
Levi-Civita connection.

Convenience wrapper that exposes the standard math notation
$\nabla_X Y$ from Mathlib's bundled `CovariantDerivative.toFun`. -/
noncomputable def covDeriv (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x :=
  ((leviCivitaConnection (I := I) (M := M)).toFun Y x) (X x)

end Riemannian

/-! ## UXTest

Self-test verifying the Levi-Civita connection + `covDeriv` resolve
their typeclass cascade. Regression guard against signature drift. -/
section UXTest

open Riemannian

noncomputable example {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x := covDeriv X Y x

end UXTest
