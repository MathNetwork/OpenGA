import Definitions.Def_OpenGA_RadialSurgeryVolumeBudget
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Ricci flow with `(r, δ)`-cutoff: the continuation interface

Kleiner-Lott, Section 77 (Proposition 77.2, p. 146, and the discussion of its
existence consequence on p. 147), https://arxiv.org/pdf/math/0605667v5#page=146.

Proposition 77.2 implies that one can choose positive nonincreasing functions
`r, δ : [0, ∞) → (0, ∞)` such that the Ricci flow with `(r, δ)`-cutoff starting
from any normalized initial condition is defined for all time, where "defined
for all time" allows the manifold to become extinct, i.e. allows empty time
slices.

Kleiner-Lott describe the passage from the inductive statement to all-time
existence as follows (p. 147): given `r` and `δ`, a normalized initial condition
has a maximal time interval on which the flow with cutoff is defined; this
interval can be finite only if it is of the form `[0, T)`, the flow extends to
`[0, T]`, and the canonical neighbourhood assumption fails at `T`. The
`r`-canonical neighbourhood assumption lets one run the flow forward to the next
singular time and perform surgery there, while volume considerations rule out an
accumulation of surgery times.

This file records that interface. A `CutoffSurgeryProcess` carries the
predicate `DefinedUpTo T`, read as "the Ricci flow with `(r, δ)`-cutoff started
from the given normalized initial condition is defined on the whole time
interval `[0, T]`", together with

* the two continuation mechanisms quoted above, as the fields `extend_forward`
  and `extend_limit`, and
* the radial volume-loss budget of `OpenGA.RadialSurgeryVolumeBudget` whose
  event set is the set of surgery times, which is what makes the finiteness
  hypothesis of `extend_limit` available.

The metric surgery construction itself, and the derivation of these records from
a normalized closed oriented Riemannian three-manifold, are geometric tasks that
this interface does not perform.
-/

set_option autoImplicit false

open Set

namespace OpenGA

/-- **Math.** The surgery parameters of Kleiner-Lott, Proposition 77.2: positive
nonincreasing functions `r, δ` on `[0, ∞)`. -/
structure CutoffParameters where
  /-- The canonical neighbourhood scale `r`. -/
  r : ℝ → ℝ
  /-- The surgery parameter `δ`. -/
  delta : ℝ → ℝ
  r_pos : ∀ t : ℝ, 0 ≤ t → 0 < r t
  delta_pos : ∀ t : ℝ, 0 ≤ t → 0 < delta t
  r_antitoneOn : AntitoneOn r (Ici 0)
  delta_antitoneOn : AntitoneOn delta (Ici 0)

/-- **Math.** A Ricci flow with `(r, δ)`-cutoff started from a fixed normalized
initial condition, recorded through its continuation behaviour.

`DefinedUpTo T` means that the flow with cutoff is defined on the whole time
interval `[0, T]`; time slices are allowed to be empty. The two continuation
fields are the mechanisms of Kleiner-Lott, p. 147: the canonical neighbourhood
assumption runs the flow forward past every time already reached and performs
surgery at the next singular time (`extend_forward`), and a time reached only as
a limit is itself attained once only finitely many surgeries occur up to it
(`extend_limit`). The volume-loss budget `budget`, whose events are exactly the
surgery times, is the source of that finiteness. -/
structure CutoffSurgeryProcess where
  /-- The surgery parameters `r` and `δ` of the process. -/
  params : CutoffParameters
  /-- `DefinedUpTo T`: the flow with cutoff is defined on all of `[0, T]`. -/
  DefinedUpTo : ℝ → Prop
  /-- The initial condition itself is a time slice of the flow. -/
  definedUpTo_zero : DefinedUpTo 0
  /-- A flow defined on `[0, T]` is defined on every `[0, S]` with `S ≤ T`. -/
  definedUpTo_mono : ∀ ⦃S T : ℝ⦄, 0 ≤ S → S ≤ T → DefinedUpTo T → DefinedUpTo S
  /-- The surgery times of the process. -/
  surgeryTimes : Set ℝ
  /-- The radial comparison data and volume-loss budget controlling the surgeries. -/
  budget : RadialSurgeryVolumeBudget
  /-- The events of the budget are the surgery times. -/
  budget_events : budget.events = surgeryTimes
  /-- Canonical neighbourhoods: the flow runs forward past any time it reaches,
  a surgery being performed at the next singular time. -/
  extend_forward : ∀ T : ℝ, 0 ≤ T → DefinedUpTo T → ∃ T' : ℝ, T < T' ∧ DefinedUpTo T'
  /-- No accumulation of surgeries: if the flow is defined on `[0, T)` and only
  finitely many surgeries occur up to time `T`, it is defined on `[0, T]`. -/
  extend_limit : ∀ T : ℝ, 0 < T → (∀ S : ℝ, 0 ≤ S → S < T → DefinedUpTo S) →
    (surgeryTimes ∩ Iic T).Finite → DefinedUpTo T

end OpenGA
