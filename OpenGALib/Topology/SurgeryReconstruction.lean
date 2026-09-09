import OpenGALib.Topology.ConnectedSum
import OpenGALib.Topology.SphereCovering

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

/-- A nonempty, connected, compact Hausdorff topological three-manifold
without boundary. The topology and atlas are part of the data. -/
structure ClosedThreeManifold where
  Carrier : Type u
  topology : TopologicalSpace Carrier
  hausdorff : @T2Space Carrier topology
  charts : @ChartedSpace EuclideanThree _ Carrier topology
  compact : @CompactSpace Carrier topology
  connected : @ConnectedSpace Carrier topology

instance : CoeSort ClosedThreeManifold.{u} (Type u) := ⟨ClosedThreeManifold.Carrier⟩
attribute [instance] ClosedThreeManifold.topology ClosedThreeManifold.hausdorff
  ClosedThreeManifold.charts ClosedThreeManifold.compact ClosedThreeManifold.connected

namespace ClosedThreeManifold

instance (M : ClosedThreeManifold) : LocallyPathConnectedSpace M :=
  ChartedSpace.locallyPathConnectedSpace EuclideanThree M

/-- A topological consequence of being a round spherical space form. -/
def IsSphereCovered (M : ClosedThreeManifold) : Prop :=
  ∃ p : SphereThree → M, IsCoveringMap p ∧ Function.Surjective p

/-- The orientable sphere-bundle factor occurring in the surgery endgame. -/
def IsSphereHandle (M : ClosedThreeManifold) : Prop :=
  Nonempty (M ≃ₜ (SphereOne × SphereTwo))

/-- The allowed terminal factors, with spherical space forms weakened to
the covering property needed for the topological conclusion. -/
def IsStandardFactor (M : ClosedThreeManifold) : Prop :=
  M.IsSphereCovered ∨ M.IsSphereHandle

/-- **Math.** A simply connected sphere-covered factor is a three-sphere.
This reuses the previously curated covering-space theorem. -/
theorem nonempty_homeomorph_sphere_of_isSphereCovered (M : ClosedThreeManifold)
    [SimplyConnectedSpace M] (h : M.IsSphereCovered) : Nonempty (M ≃ₜ SphereThree) := by
  obtain ⟨p, hp, _⟩ := h
  apply nonempty_homeomorph_sphere_of_isCoveringMap (X := M) (p := p) _ (by norm_num) hp
  apply Module.one_lt_rank_of_one_lt_finrank
  simp

end ClosedThreeManifold

/-- Finite, nonempty connected-sum expressions in factors satisfying `P`.
The operation is the actual quotient construction in `IsConnectedSum`.
There is deliberately no constructor declaring an arbitrary manifold to be
the empty connected sum. -/
inductive ConnectedSumClosure (P : ClosedThreeManifold.{u} → Prop) :
    ClosedThreeManifold.{u} → Prop
  | factor {M : ClosedThreeManifold.{u}} : P M → ConnectedSumClosure P M
  | homeomorph {M N : ClosedThreeManifold.{u}} : ConnectedSumClosure P M →
      Nonempty (N ≃ₜ M) → ConnectedSumClosure P N
  | sum {M N X : ClosedThreeManifold.{u}} : ConnectedSumClosure P M → ConnectedSumClosure P N →
      IsConnectedSum M N X → ConnectedSumClosure P X

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

/-- Topology recoverable from a later slice and the standard discarded factors. -/
def SurgeryReconstruction (before after : List ClosedThreeManifold.{u}) : Prop :=
  ∀ M ∈ before, ConnectedSumClosure (fun N => N ∈ after ∨ N.IsStandardFactor) M

/-- A finite chain of reconstruction records, in forward time order. -/
inductive FiniteSurgeryHistory :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → Prop
  | refl (slice) : FiniteSurgeryHistory slice slice
  | step {before middle after} : SurgeryReconstruction before middle →
      FiniteSurgeryHistory middle after → FiniteSurgeryHistory before after

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

/-- Time-indexed component topology with finite reconstruction on each
bounded horizon. This is extracted topological data, not a definition of
Ricci flow: no metric or Ricci equation is encoded here. -/
structure SurgeryTopologyEvolution (M : ClosedThreeManifold.{u}) where
  components : ℝ → List ClosedThreeManifold.{u}
  initial : components 0 = [M]
  initial_interval : ∃ τ : ℝ, 0 < τ ∧ ∀ t ∈ Set.Icc 0 τ, components t = [M]
  history : ∀ T, 0 ≤ T → FiniteSurgeryHistory (components 0) (components T)

namespace SurgeryTopologyEvolution

variable {M : ClosedThreeManifold.{u}}

/-- Every component is absent from some positive time onward. -/
def FiniteExtinction (E : SurgeryTopologyEvolution M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → E.components t = []

/-- **Math.** Finite extinction plus the recorded surgery topology yields
a finite connected sum of standard factors. -/
theorem topology_from_extinction (E : SurgeryTopologyEvolution M) (h : E.FiniteExtinction) :
    ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M := by
  obtain ⟨T, hT, hempty⟩ := h
  have hh := E.history T hT.le
  rw [E.initial, hempty T le_rfl] at hh
  exact hh.topology_from_empty (by simp)

end SurgeryTopologyEvolution

end OpenGA
