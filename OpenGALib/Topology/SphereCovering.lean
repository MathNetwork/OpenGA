import Mathlib.Analysis.Normed.Module.Connected
import OpenGALib.Topology.CoveringSpace

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
