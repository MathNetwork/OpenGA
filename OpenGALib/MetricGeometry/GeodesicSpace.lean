import OpenGALib.MetricGeometry.LengthSpace

/-!
# Geodesic spaces

A `GeodesicSpace` is a length space in which the infimum defining the
distance is realized: every pair of points is joined by a length-minimizing
path. This is the second of Layer 1's three foundational concepts.

## Ground truth

Burago–Burago–Ivanov, *A Course in Metric Geometry*, §2.5 (Length spaces
with geodesics); Gromov, *Metric Structures*, §1.4.

In Mathlib's tangent-bundle Riemannian setup the analogous notion is the
existence of minimizing `C^1` paths, which is automatic for complete
Riemannian manifolds by the Hopf–Rinow theorem. Layer 1 only records the
metric-side notion; the Riemannian-side existence theorem (Hopf–Rinow) is
the responsibility of Layer 3a / Layer 3b.

## Main declaration

* `GeodesicSpace M` — `LengthSpace M` plus existence of a minimizing path
  between every pair of points.
-/

open Topology unitInterval

namespace OpenGA

/-- **Math.** A *geodesic space*: a length space in which the infimum
defining the distance is attained by some path between every pair of
points.

Ground truth: Burago–Burago–Ivanov §2.5.5 (geodesic spaces are length
spaces in which every pair of points is joined by a shortest path).

A path `γ` with `pathLength γ = edist x y` is a *minimizing geodesic*
joining `x` and `y`. The class only asserts existence; uniqueness and
regularity belong to specialized contexts (Riemannian / CAT(0) / etc.). -/
class GeodesicSpace (M : Type*) [PseudoEMetricSpace M] : Prop
    extends LengthSpace M where
  /-- Every pair of points is joined by a length-minimizing path. -/
  exists_minimizing_path :
    ∀ x y : M, ∃ γ : Path x y, pathLength γ = edist x y

end OpenGA
