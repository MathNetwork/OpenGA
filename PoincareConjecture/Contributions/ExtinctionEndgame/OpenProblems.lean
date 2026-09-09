import OpenGALib.Topology.ExtinctionEndgame

/-!
# Open geometric and topological inputs to the extinction endgame

These are open problems, with explicit `sorry` bodies. They are kept in the
mission workspace, outside the reusable OpenGALib import tree. Successfully
elaborating this file does not prove any of the four problems.

The geometry problem asks for data extracted from the intended Kleiner-Lott
and Colding-Minicozzi construction. `SurgeryTopologyEvolution` is explicitly
an abstraction of its topological output, not the full metric surgery flow.
In particular, this file does not claim to formalize the Ricci equation,
cutoff conditions, or the analytic min-max construction.
-/

namespace PoincareFormalization.ExtinctionEndgame

open OpenGA

universe u

/-- **Open.** Construct one evolution and one uniform initial width bound
for a closed simply connected three-manifold. Every nonempty positive-time
slice must supply a finite comparison trace with that same bound.

The intended construction must supply a compatible smooth structure and
normalized metric, orientability, all-time controlled surgery, the finite topological
reconstruction records, nontrivial sweepouts, CM comparison estimates, and
their behavior under surgery. These are all obligations of this open node;
none are supplied by the name `SurgeryTopologyEvolution`.

References: Kleiner-Lott, Sections 3.2, 73 and 77;
Colding-Minicozzi, Theorem 1.7 and Corollary 1.11.
https://arxiv.org/pdf/math/0605667v5
https://arxiv.org/pdf/0707.0108 -/
theorem exists_width_controlled_surgery_topology (M : ClosedThreeManifold.{u})
    [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧ E.HasWidthControl W := by
  sorry

/-- **Open.** The van Kampen consequence for the explicit punctured-ball
quotient: a simply connected connected sum has simply connected factors.
No conclusion about the factors is built into `IsConnectedSum`.
Reference: Kleiner-Lott, Section 3.2, p. 9, the final van Kampen step. -/
theorem simply_connected_factors_of_connected_sum (M N X : ClosedThreeManifold.{u})
    (hsum : IsConnectedSum M N X) (hX : SimplyConnectedSpace X) :
    SimplyConnectedSpace M ∧ SimplyConnectedSpace N := by
  sorry

/-- **Open.** A manifold homeomorphic to `S¹ × S²` is not simply connected.
The intended proof uses the nontrivial fundamental group of the circle.
Reference: Kleiner-Lott, Section 3.2, p. 9. -/
theorem not_simply_connected_sphere_handle (M : ClosedThreeManifold.{u})
    (hhandle : M.IsSphereHandle) : ¬SimplyConnectedSpace M := by
  sorry

/-- **Open.** A connected sum of two topological three-spheres is a
three-sphere, for the coordinate-ball quotient used by `IsConnectedSum`.
Reference: Kleiner-Lott, Section 3.2, p. 9, the last connected-sum identity. -/
theorem nonempty_homeomorph_sphere_of_connected_sum_spheres
    (M N X : ClosedThreeManifold.{u}) (hsum : IsConnectedSum M N X)
    (hM : Nonempty (M ≃ₜ SphereThree)) (hN : Nonempty (N ≃ₜ SphereThree)) :
    Nonempty (X ≃ₜ SphereThree) := by
  sorry

end PoincareFormalization.ExtinctionEndgame
