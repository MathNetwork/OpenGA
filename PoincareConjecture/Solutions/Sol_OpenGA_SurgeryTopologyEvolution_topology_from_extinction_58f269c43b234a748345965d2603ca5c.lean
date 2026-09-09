import Definitions.Def_OpenGA_SurgeryTopologyEvolution

/-!
# The topological endpoint of finite surgery

Kleiner-Lott, Lemma 73.4 (p. 140), reconstructs the topology before a surgery
by connected sums and restoration of specified discarded components. Lemma
81.2 (p. 160) iterates this description backwards from an empty slice.
Source: https://arxiv.org/pdf/math/0605667v5

This file proves that finite iteration explicitly. A `SurgeryReconstruction`
records the topological consequence of an operation, not its metric surgery
construction. Obtaining these records from a Kleiner-Lott flow remains a
geometric task.

For the topological conclusion we retain a weaker class than round spherical
space forms: closed three-manifolds covered by the standard three-sphere.
Every round spherical space form has such a covering. This weakening is
sufficient for the simply connected endgame and does not assert that every
sphere-covered manifold carries a round quotient metric.
-/

namespace OpenGA

universe u




attribute [instance] ClosedThreeManifold.topology ClosedThreeManifold.hausdorff
  ClosedThreeManifold.charts ClosedThreeManifold.compact ClosedThreeManifold.connected

namespace ClosedThreeManifold











end ClosedThreeManifold



namespace ConnectedSumClosure

variable {P Q : ClosedThreeManifold.{u} → Prop} {M : ClosedThreeManifold.{u}}

/-- **Math.** Substitute finite connected-sum expressions for their leaves. -/
theorem bind (h : ConnectedSumClosure P M)
    (hPQ : ∀ N, P N → ConnectedSumClosure Q N) : ConnectedSumClosure Q M := by
  induction h with
  | factor h => exact hPQ _ h
  | homeomorph _ e ih => exact .homeomorph ih e
  | sum _ _ h ihM ihN => exact .sum ihM ihN h

end ConnectedSumClosure





namespace FiniteSurgeryHistory

/-- **Math.** Recover every earlier component from the later components and
the standard factors by finitely many connected sums. -/
theorem reconstruct {before after : List ClosedThreeManifold.{u}}
    (h : FiniteSurgeryHistory before after) : SurgeryReconstruction before after := by
  induction h with
  | refl slice =>
    intro M hM
    exact .factor (Or.inl hM)
  | step hstep _ ih =>
    intro M hM
    apply (hstep M hM).bind
    intro N hN
    rcases hN with hN | hN
    · exact ih N hN
    · exact .factor (Or.inr hN)

/-- **Math.** A finite surgery history ending with no components leaves only
standard factors in the initial connected-sum decomposition. This is the
finite-induction part of Kleiner-Lott Lemma 81.2. -/
theorem topology_from_empty {before : List ClosedThreeManifold.{u}}
    (h : FiniteSurgeryHistory before []) {M : ClosedThreeManifold.{u}} (hM : M ∈ before) :
    ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M := by
  apply (h.reconstruct M hM).bind
  intro N hN
  rcases hN with hN | hN
  · simp at hN
  · exact .factor hN

end FiniteSurgeryHistory



namespace SurgeryTopologyEvolution

variable {M : ClosedThreeManifold.{u}}





end SurgeryTopologyEvolution

end OpenGA

/-!
# The topological endpoint of finite surgery

Kleiner-Lott, Lemma 73.4 (p. 140), reconstructs the topology before a surgery
by connected sums and restoration of specified discarded components. Lemma
81.2 (p. 160) iterates this description backwards from an empty slice.
Source: https://arxiv.org/pdf/math/0605667v5

This file proves that finite iteration explicitly. A `SurgeryReconstruction`
records the topological consequence of an operation, not its metric surgery
construction. Obtaining these records from a Kleiner-Lott flow remains a
geometric task.

For the topological conclusion we retain a weaker class than round spherical
space forms: closed three-manifolds covered by the standard three-sphere.
Every round spherical space form has such a covering. This weakening is
sufficient for the simply connected endgame and does not assert that every
sphere-covered manifold carries a round quotient metric.
-/

namespace OpenGA

universe u




attribute [instance] ClosedThreeManifold.topology ClosedThreeManifold.hausdorff
  ClosedThreeManifold.charts ClosedThreeManifold.compact ClosedThreeManifold.connected

namespace ClosedThreeManifold











end ClosedThreeManifold



namespace ConnectedSumClosure

variable {P Q : ClosedThreeManifold.{u} → Prop} {M : ClosedThreeManifold.{u}}



end ConnectedSumClosure





namespace FiniteSurgeryHistory





end FiniteSurgeryHistory



namespace SurgeryTopologyEvolution

variable {M : ClosedThreeManifold.{u}}



/-- **Math.** Finite extinction plus the recorded surgery topology yields
a finite connected sum of standard factors. -/
theorem _root_.solution (E : SurgeryTopologyEvolution M) (h : E.FiniteExtinction) :
    ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M := by
  obtain ⟨T, hT, hempty⟩ := h
  have hh := E.history T hT.le
  rw [E.initial, hempty T le_rfl] at hh
  exact hh.topology_from_empty (by simp)

end SurgeryTopologyEvolution

end OpenGA
