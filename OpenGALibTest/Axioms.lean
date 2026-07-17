import OpenGALib.Riemannian.Geodesic.HopfRinow

/-!
# Axiom regression tests for the Hopf--Rinow facade

These tests ensure that the five main facade theorems remain free of `sorryAx` and depend only on
the standard axioms used throughout Mathlib.
-/

/--
info: 'Riemannian.Geodesic.hopfRinow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.hopfRinow

/--
info: 'Riemannian.Geodesic.isGeodesicallyComplete_of_complete' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.isGeodesicallyComplete_of_complete

/--
info: 'Riemannian.Geodesic.complete_of_isGeodesicallyComplete' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.complete_of_isGeodesicallyComplete

/--
info: 'Riemannian.Geodesic.complete_of_geodesicallyComplete_at' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.complete_of_geodesicallyComplete_at

/--
info: 'Riemannian.Geodesic.exists_minimizing_geodesic' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.exists_minimizing_geodesic
