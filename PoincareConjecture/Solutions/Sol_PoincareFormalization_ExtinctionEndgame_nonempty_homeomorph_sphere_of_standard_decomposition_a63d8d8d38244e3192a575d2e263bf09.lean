import Definitions.Def_OpenGA_SurgeryTopologyEvolution
import Theorems.Thm_PoincareFormalization_ExtinctionEndgame_simply_connected_factors_of_connected_sum
import Theorems.Thm_PoincareFormalization_ExtinctionEndgame_not_simply_connected_sphere_handle
import Theorems.Thm_PoincareFormalization_ExtinctionEndgame_nonempty_homeomorph_sphere_of_connected_sum_spheres
import Theorems.Thm_PoincareFormalization_covering_is_homeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connected coverings of simply connected spaces

A covering map from a connected space onto a simply connected, locally path connected space
is a homeomorphism. Surjectivity need not be assumed: lift the identity on the base through a
point of the nonempty total space. Uniqueness of lifts makes this section a two-sided inverse.

The statement and lifting argument were contributed by `salim` to the Prove2Me Poincare mission:
theorem `192cef90-169f-4470-b074-8392596cb487`, accepted submission
`bbe6fec0-1a12-4eba-bb85-2c00ebf62342` (2026-09-08). This version exposes `IsHomeomorph`, so callers
can use Mathlib's existing bijectivity and bundled-homeomorphism interfaces.
Source: https://prove2.me/api/v1/submissions/bbe6fec0-1a12-4eba-bb85-2c00ebf62342/solution

Mathematical reference: Hatcher, *Algebraic Topology*, Section 1.3, Propositions 1.33 and 1.34.
-/

/-- **Math.** A covering map from a connected space to a simply connected, locally path connected
space is a homeomorphism. `ConnectedSpace E` includes nonemptiness, which is needed to lift the
identity of the base. No separation, compactness, or manifold hypotheses are required. -/
theorem IsCoveringMap.isHomeomorph_of_simplyConnectedSpace
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) : IsHomeomorph p := by
  obtain ⟨e, he⟩ := PoincareFormalization.covering_is_homeomorph p hp
  rw [← he]
  exact e.isHomeomorph

/-!
# A spherical covering gives a homeomorphism

A simply connected, locally path connected space covered by a connected sphere is homeomorphic
to that sphere. The covering is an explicit hypothesis.

This extracts the conditional covering-space step of `salim`'s Prove2Me submission
`98612d40-bcb7-4333-afa7-69b60e20dfdc` (2026-09-08), and generalizes the unit 3-sphere to spheres
of nonnegative radius in real normed spaces of dimension greater than one. The original sketch
imports an unproved spherical-cover existence theorem; that import is not used here.
Source: https://prove2.me/api/v1/submissions/98612d40-bcb7-4333-afa7-69b60e20dfdc/solution
-/

namespace OpenGA

/-- **Math.** If a sphere of nonnegative radius in a real normed space of dimension greater than
one covers a simply connected, locally path connected space `X`, then `X` is homeomorphic to
that sphere. Existence of the covering map remains an explicit hypothesis. -/
theorem nonempty_homeomorph_sphere_of_isCoveringMap
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hdim : 1 < Module.rank ℝ E) {c : E} {r : ℝ} (hr : 0 ≤ r)
    {p : ↥(Metric.sphere c r) → X} (hp : IsCoveringMap p) :
    Nonempty (X ≃ₜ ↥(Metric.sphere c r)) := by
  have : ConnectedSpace ↥(Metric.sphere c r) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hdim c hr)
  exact ⟨(hp.isHomeomorph_of_simplyConnectedSpace.homeomorph p).symm⟩

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









/-- **Math.** A simply connected sphere-covered factor is a three-sphere.
This reuses the previously curated covering-space theorem. -/
theorem nonempty_homeomorph_sphere_of_isSphereCovered (M : ClosedThreeManifold)
    [SimplyConnectedSpace M] (h : M.IsSphereCovered) : Nonempty (M ≃ₜ SphereThree) := by
  obtain ⟨p, hp, _⟩ := h
  apply nonempty_homeomorph_sphere_of_isCoveringMap (X := M) (p := p) _ (by norm_num) hp
  apply Module.one_lt_rank_of_one_lt_finrank
  simp

end ClosedThreeManifold



namespace ConnectedSumClosure

variable {P Q : ClosedThreeManifold.{u} → Prop} {M : ClosedThreeManifold.{u}}



end ConnectedSumClosure





namespace FiniteSurgeryHistory





end FiniteSurgeryHistory



namespace SurgeryTopologyEvolution

variable {M : ClosedThreeManifold.{u}}





end SurgeryTopologyEvolution

end OpenGA

/-!
# From width-controlled extinction to the Poincare endgame

The analytic and finite-topology links are proved. The last theorem lists
the remaining topology lemmas as explicit hypotheses. The separate mission
workspace declares those open problems and the geometric data-construction
problem; no unproved theorem is imported into this reusable library.

References: Colding-Minicozzi, https://arxiv.org/pdf/0707.0108, Theorem 1.7
and Corollary 1.11; Kleiner-Lott, https://arxiv.org/pdf/math/0605667v5,
Section 3.2 and Lemmas 73.4 and 81.2.
-/

namespace OpenGA

universe u

namespace SurgeryTopologyEvolution

variable {M : ClosedThreeManifold.{u}}







end SurgeryTopologyEvolution

/-- **Math.** The topological endgame, conditional on three explicitly
listed connected-sum lemmas. The sphere-covered base case is already proved.
No Ricci flow, finite extinction, or Poincare theorem is assumed here. -/
theorem nonempty_homeomorph_sphere_of_standard_connectedSum
    (h_factors : ∀ M N X : ClosedThreeManifold.{u}, IsConnectedSum M N X →
      SimplyConnectedSpace X → SimplyConnectedSpace M ∧ SimplyConnectedSpace N)
    (h_handle : ∀ M : ClosedThreeManifold.{u}, M.IsSphereHandle → ¬SimplyConnectedSpace M)
    (h_sphere_sum : ∀ M N X : ClosedThreeManifold.{u}, IsConnectedSum M N X →
      Nonempty (M ≃ₜ SphereThree) → Nonempty (N ≃ₜ SphereThree) →
      Nonempty (X ≃ₜ SphereThree))
    {M : ClosedThreeManifold.{u}}
    (h : ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M)
    (hM : SimplyConnectedSpace M) : Nonempty (M ≃ₜ SphereThree) := by
  induction h with
  | factor h =>
    rcases h with h | h
    · let := hM
      exact ClosedThreeManifold.nonempty_homeomorph_sphere_of_isSphereCovered _ h
    · exact (h_handle _ h hM).elim
  | homeomorph _ e ih =>
    obtain ⟨e⟩ := e
    let := hM
    obtain ⟨f⟩ := ih e.symm.toHomotopyEquiv.simplyConnectedSpace
    exact ⟨e.trans f⟩
  | sum _ _ hsum ihM ihN =>
    obtain ⟨hM, hN⟩ := h_factors _ _ _ hsum hM
    exact h_sphere_sum _ _ _ hsum (ihM hM) (ihN hN)

end OpenGA

/-!
# The formal finite-extinction reduction of the Poincare goal

The proofs in this file have no holes of their own, but depend on the four
explicit open theorems in `OpenProblems.lean`. They are conditional proof
sketches, not proofs of the Poincare conjecture or of geometric extinction.

Dependency chain:
  geometric construction (open) -> width-controlled component evolution
  -> finite extinction -> connected-sum reconstruction
  -> simply connected endgame (three open topology lemmas) -> mission goal.

The auxiliary definitions and analytic/topological iteration theorems in
OpenGALib have no project axioms or proof holes. The distinction is checked
by `Audit.lean` and the reusable-library regression check.
-/

namespace PoincareFormalization.ExtinctionEndgame

open OpenGA

universe u



/-- **Conditional reduction.** Combine the covering-space base case with
the three open connected-sum topology lemmas. -/
theorem _root_.solution
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M]
    (h : ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M) :
    Nonempty (M ≃ₜ SphereThree) := by
  exact nonempty_homeomorph_sphere_of_standard_connectedSum
    simply_connected_factors_of_connected_sum not_simply_connected_sphere_handle
    nonempty_homeomorph_sphere_of_connected_sum_spheres h inferInstance





end PoincareFormalization.ExtinctionEndgame
