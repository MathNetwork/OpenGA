import OpenGALib.Topology.SurgeryReconstruction
import OpenGALib.Analysis.ComparisonExtinction

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

/-- A single initial width bound works for every positive horizon whose
final slice is nonempty. Supplying this property from geometric sweepouts
and surgery is an open input, not part of the definition of an evolution. -/
def HasWidthControl (E : SurgeryTopologyEvolution M) (W : ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → E.components T ≠ [] → Nonempty (WidthComparisonTrace W T)

/-- **Math.** If each nonempty slice supplies a trace with the same initial
bound, all slices beyond an explicit positive time must be empty. -/
theorem finiteExtinction_of_width_control (E : SurgeryTopologyEvolution M)
    {W : ℝ} (h : E.HasWidthControl W) : E.FiniteExtinction := by
  let T := max (widthExtinctionTime (1 / 4) W) 0 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right (widthExtinctionTime (1 / 4) W) 0]
  refine ⟨T, hT, ?_⟩
  intro t ht
  by_contra hne
  obtain ⟨F⟩ := h t (hT.trans_le ht) hne
  have hbound := F.le_extinctionTime
  have hmax := le_max_left (widthExtinctionTime (1 / 4) W) 0
  dsimp [T] at ht
  linarith

/-- **Math.** The width deadline and finite surgery reconstruction combine
to produce a genuine connected-sum decomposition of the initial manifold. -/
theorem topology_from_width_control (E : SurgeryTopologyEvolution M)
    {W : ℝ} (h : E.HasWidthControl W) :
    ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M :=
  E.topology_from_extinction (E.finiteExtinction_of_width_control h)

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
