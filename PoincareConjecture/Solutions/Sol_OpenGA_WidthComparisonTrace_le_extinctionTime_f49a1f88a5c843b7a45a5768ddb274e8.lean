import Definitions.Def_OpenGA_WidthComparisonTrace
import Definitions.Def_OpenGA_WidthExtinctionTime
import Theorems.Thm_OpenGA_scalar_lower_bound_across_upward_jumps
import Theorems.Thm_OpenGA_eventually_width_slope_lt_of_comparison
import Theorems.Thm_OpenGA_le_width_deadline_across_downward_jumps

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



namespace WidthExtinction















end WidthExtinction




open WidthExtinction in
/-- **Math.** The Colding-Minicozzi width deadline survives finitely many
surgery times at which the width can only decrease. This is an analytic
statement; its hypotheses must be supplied by a geometric construction. -/
theorem le_widthExtinctionTime_across_downward_jumps
    {C W₀ : ℝ} (hC : 0 < C)
    (n : ℕ) (hn : 0 < n) (times : ℕ → ℝ) (widths : ℕ → ℝ → ℝ)
    (hzero : times 0 = 0)
    (htimes : ∀ i < n, times i < times (i + 1))
    (hcont : ∀ i < n, ContinuousOn (widths i) (Icc (times i) (times (i + 1))))
    (hinitial : widths 0 (times 0) ≤ W₀)
    (hfinal : 0 ≤ widths (n - 1) (times n))
    (hslope : ∀ i < n, ∀ x ∈ Ico (times i) (times (i + 1)), ∀ r : ℝ,
      -(4 * Real.pi) + 3 / (4 * (x + C)) * widths i x < r →
        ∃ᶠ z in 𝓝[>] x, slope (widths i) x z < r)
    (hjumps : ∀ i, i + 1 < n →
      widths (i + 1) (times (i + 1)) ≤ widths i (times (i + 1))) :
    times n ≤ widthExtinctionTime C W₀ := by
  exact OpenGA.le_width_deadline_across_downward_jumps hC n hn times widths hzero htimes hcont hinitial hfinal hslope hjumps


end OpenGA

/-!
# The lifetime bound for scalar and width comparison traces

This packages the existing scalar lower bound, area-energy width comparison,
and finite-jump deadline into one reusable theorem. No geometric existence
claim is made: the trace is an explicit input.
-/

namespace OpenGA

open Set Filter
open scoped Topology

/-- **Math.** A normalized finite scalar/width comparison trace cannot
extend beyond the Colding-Minicozzi deadline. -/
theorem _root_.solution {W T : ℝ} (F : WidthComparisonTrace W T) :
    T ≤ widthExtinctionTime (1 / 4) W := by
  have hscalar := scalar_lower_bound_across_upward_jumps
    F.count F.count_pos F.times F.scalar F.first_time F.times_strict
    F.scalar_cont F.scalar_initial F.scalar_slope F.scalar_jump
  have hslope : ∀ i < F.count, ∀ x ∈ Ico (F.times i) (F.times (i + 1)), ∀ q : ℝ,
      -(4 * Real.pi) + 3 / (4 * (x + (1 / 4 : ℝ))) * F.width i x < q →
        ∃ᶠ s in 𝓝[>] x, slope (F.width i) x s < q := by
    intro i hi x hx q hq
    obtain ⟨data⟩ := F.comparison i hi x hx
    apply (eventually_width_slope_lt_of_comparison data q ?_).frequently
    have hs := hscalar i hi x (Ico_subset_Icc_self hx)
    have hw := F.width_nonneg i hi x (Ico_subset_Icc_self hx)
    have hm := mul_le_mul_of_nonneg_right hs hw
    have hid : (-(6 : ℝ) / (1 + 4 * x)) * F.width i x / 2 =
        -(3 / (4 * (x + (1 / 4 : ℝ))) * F.width i x) := by
      have hden : 1 + 4 * x = 4 * (x + (1 / 4 : ℝ)) := by ring
      rw [hden]
      ring
    nlinarith
  have hlast : F.count - 1 + 1 = F.count := by have := F.count_pos; omega
  have hfinal : 0 ≤ F.width (F.count - 1) (F.times F.count) := by
    apply F.width_nonneg (F.count - 1) (by have := F.count_pos; omega)
    constructor
    · simpa [hlast] using (F.times_strict (F.count - 1) (by have := F.count_pos; omega)).le
    · simp [hlast]
  have hbound := le_widthExtinctionTime_across_downward_jumps
    (C := (1 / 4 : ℝ)) (W₀ := W) (by norm_num)
    F.count F.count_pos F.times F.width F.first_time F.times_strict
    F.width_cont F.width_initial hfinal hslope F.width_jump
  simpa only [F.last_time] using hbound

end OpenGA
