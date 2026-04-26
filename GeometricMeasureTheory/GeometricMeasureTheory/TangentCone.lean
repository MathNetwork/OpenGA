import GeometricMeasureTheory.Varifold

/-!
# GeometricMeasureTheory.TangentCone

Tangent cone of a varifold: the blow-up limit of $V$ under rescaling
at a point $Z$.

This file provides only the GMT primitive `tangentCone`. The
junction-cone configuration (a stationary cone supported on $N \ge 3$
half-hyperplanes meeting along a common edge), which is the configuration
excluded by the Wickramasekera $\alpha$-structural hypothesis, lives in
the regularity-theory package (`Regularity.AlphaStructural`) since it
is a regularity-theory-specific concept rather than a general GMT
primitive.
-/

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- The **tangent cone** of $V$ at $Z$: the blow-up limit of $V$ under
rescaling at $Z$, a stationary integral cone in the tangent space.

**Ground truth**: Simon 1983 §42 (varifold tangents, blow-up procedure
for stationary integral varifolds); Allard 1972 §3.4–§3.6.

**Why opaque** (Layer B Item 3 retreat):

A paper-faithful definition requires the rescaling map
$\eta_{Z, r}(x) := (x - Z) / r$ and the push-forward measure
$\eta_{Z, r \#} V$, then the weak limit as $r \to 0^+$. Three options
explored:

  * **(A) Full geometric blow-up**: requires affine/vector-space
    structure on $M$ (e.g., `[NormedAddCommGroup M]`), which would
    cascade through ~27 framework files and conflicts with $M$ being a
    Riemannian manifold rather than a normed space at the typeclass
    level.
  * **(B/C) `Classical.choice` over `IsTangentConeAt` predicate**:
    introduce sub-primitive `opaque IsTangentConeAt : Varifold M → M →
    Varifold M → Prop` and pick any cone via choice. Net opaque count
    unchanged (1 → 1); semantics degenerate to the zero varifold
    via `instNonempty` since existence proof itself is paper-
    mathematical (Simon §42).
  * **(D) Mathlib normed-space form**: same blocker as (A).

The chain only uses `tangentCone V Z` as black-box input; the computed
value is never inspected by chain proofs. Retreat preserves structural
information without losing chain-checked correctness.

**Used by**: `Regularity.HasJunction` def
(`Regularity/AlphaStructural.lean`). -/
noncomputable opaque tangentCone : Varifold M → M → Varifold M

end Varifold

end GeometricMeasureTheory
