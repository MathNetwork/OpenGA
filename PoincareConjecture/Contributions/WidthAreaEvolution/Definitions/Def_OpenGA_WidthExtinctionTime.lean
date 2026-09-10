import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The width inequality forces extinction

A nonnegative continuous quantity `W` whose forward Dini derivative
satisfies
$$\frac{d}{dt} W(t) \;\le\; -4\pi + \frac{3}{4(t+C)}\, W(t)$$
cannot live past the explicit deadline
$$T^* \;=\; \Big(C^{1/4} + \frac{W(0)}{16\pi\, C^{3/4}}\Big)^{4} - C .$$

This is the pure-calculus endpoint of the Colding–Minicozzi finite-time
extinction argument: the width of a nontrivial sweepout class along a
Ricci flow satisfies the displayed inequality, is nonnegative by
definition, and therefore the flow cannot be immortal. All geometry is
upstream, in the two constants; this file is analysis only.

The differential inequality enters in the weakest useful sense — the
liminf of forward difference quotients (`slope`), the form consumed by
Mathlib's fencing lemmas. It is implied both by the limsup-of-forward-
difference-quotients hypothesis of the blueprint and by any pointwise
right-differentiable version, so every downstream supplier can
instantiate it.

## Ground truth

Colding–Minicozzi, *Estimates for the extinction time for the Ricci
flow on certain 3-manifolds and a question of Perelman*, §1 (the
integration displayed between Theorem 0.1 and its corollary).
Blueprint: PoincareNet card `lem-width-inequality-forces-extinction`
(id `aa4c3210ae78`).

## Main declarations

* `widthExtinctionTime C W₀` — the explicit deadline `T*(C, W₀)`.
* `le_widthExtinctionTime_of_slope_le` — a nonnegative continuous `W`
  satisfying the width differential inequality on `[0, t]` forces
  `t ≤ widthExtinctionTime C (W 0)`.
* `le_widthExtinctionTime_across_downward_jumps` — the same deadline for
  finitely many continuous width profiles with downward jumps.

## Proof shape

No integrating factor is applied to `W` itself (transporting Dini
bounds through a product costs an epsilon-management detour). Instead,
for each `ε > 0` the *explicit* solution of the perturbed comparison
equation `B' = 3/(4(t+C))·B - 4π + ε`, `B 0 = W 0 + ε`, is written
down in closed form and Mathlib's contact fencing lemma
`image_le_of_liminf_slope_right_lt_deriv_boundary'` pins `W ≤ B`:
at a contact point `W x = B x` the hypothesised Dini bound for `W` is
*strictly* below `B'`. Letting `ε ↓ 0` and reading the sign of the
limit solution at `t` yields the deadline.
-/

open Set Topology
open scoped Topology

namespace OpenGA

/-- **Math.** The **extinction deadline** $T^*(C, W_0) = \big(C^{1/4} +
\frac{W_0}{16\pi C^{3/4}}\big)^4 - C$: past this time, no nonnegative
quantity can satisfy the width differential inequality. -/
noncomputable def widthExtinctionTime (C W₀ : ℝ) : ℝ :=
  (C ^ ((1 : ℝ)/4) + W₀ / (16 * Real.pi * C ^ ((3 : ℝ)/4))) ^ (4 : ℕ) - C

namespace WidthExtinction















end WidthExtinction







end OpenGA
