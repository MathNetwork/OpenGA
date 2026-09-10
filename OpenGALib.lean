import OpenGALib.Analysis.AreaEnergy
import OpenGALib.Analysis.AreaEnergy.LinearMap
import OpenGALib.Analysis.IntegralComparison
import OpenGALib.Analysis.ModelVolume
import OpenGALib.Analysis.SurgeryComparison
import OpenGALib.Analysis.ScalarLowerBound
import OpenGALib.Analysis.WidthExtinction
import OpenGALib.Analysis.WidthComparison
import OpenGALib.ComparisonGeometry.CurvatureBounds
import OpenGALib.ComparisonGeometry.Volume
import OpenGALib.Interoperability.BishopGromov
import OpenGALib.Interoperability.DifferentialGeometry
import OpenGALib.Interoperability.RicciFlow
import OpenGALib.GeometricMeasureTheory
import OpenGALib.Riemannian.Geodesic.HopfRinow.EVariationLePathELength
import OpenGALib.Riemannian.Geodesic.SymmetryLemma
import OpenGALib.Riemannian.Surface
import OpenGALib.Topology.SphereCovering
import OpenGALib.Topology.ExtinctionEndgame

/-!
# OpenGALib

A Lean 4 formalization of Riemannian geometry on top of Mathlib — the
`sorry`-free supporting cone for the Hopf–Rinow theorem (the theorem
itself lands here once its proof is complete on the development
branch), plus the analysis endpoint of the Colding–Minicozzi
finite-time extinction argument (`OpenGALib.Analysis.WidthExtinction`) and
scalar lower bounds across upward jumps (`OpenGALib.Analysis.ScalarLowerBound`),
plus covering-space consequences for simply connected spaces and
the area-energy inequality with its equality criterion (`OpenGALib.Analysis.AreaEnergy`).
The corresponding linear-map densities are independent of orthonormal frame
(`OpenGALib.Analysis.AreaEnergy.LinearMap`).
Riemannian volume and its integration properties are reused from the pinned
DifferentialGeometry dependency through `OpenGALib.Interoperability.DifferentialGeometry`.
The complete-manifold Bishop-Gromov comparison for nonpositive model curvature,
including nonnegative-Ricci volume doubling, is exposed through
`OpenGALib.Interoperability.BishopGromov`.
The basic ball, volume and local Ricci-bound interfaces live in
`OpenGALib.ComparisonGeometry`; in particular, ball-volume finiteness from
compact closure does not require completeness of the ambient manifold.
Euclidean varifolds following Simon, their Grassmannian, weight measures,
weak-* convergence and parametrized-surface interfaces are available through
`OpenGALib.GeometricMeasureTheory`.
The smooth Ricci-flow scalar lower bound, its use in the width deadline, and
local parametrized area variation are exposed by `OpenGALib.Interoperability.RicciFlow`.
The global area variation of a fixed smooth immersion of a closed surface now
uses the actual induced metric and its Riemannian measure. Smooth Ricci-flow
regularity and compactness supply differentiation under the integral locally
in time, without an additional domination hypothesis.
The reusable induced metric, global area and patch compatibility live in
`OpenGALib.Riemannian.Surface`. Branch points, minimal-surface curvature
identities and the CM sweepout construction remain separate tasks.
-/
