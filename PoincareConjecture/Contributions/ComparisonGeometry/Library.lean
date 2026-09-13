import OpenGALib.ComparisonGeometry.CurvatureBounds
import OpenGALib.Interoperability.BishopGromov

/-!
# Reviewed comparison geometry for the Poincare mission

This entry calls the installed OpenGA and DifferentialGeometry libraries.
Check it from the OpenGA repository root with:
`lake env lean PoincareConjecture/Contributions/ComparisonGeometry/Library.lean`.

The sibling Definitions, Theorems and Solutions directories hold the bounded
Prove2Me export. The metric-ball batch is exported first; the full geometric
comparison requires further dependency publication before the server can use it.

The Bishop-Gromov proof is due to DifferentialGeometry's contributors and is
reused through OpenGA's explicit-metric interface. Its hypotheses still include
completeness, a global Ricci bound and nonpositive model curvature. The mission's
stronger local formulation remains open.
-/

namespace PoincareFormalization

export Riemannian.RiemannianMetric
  (geodesicBall ballVolume RicciBoundedBelowOn isOpen_geodesicBall
   ballVolume_pos ballVolume_lt_top_of_isCompact_closure
   ballVolume_ratio_le antitoneOn_ballVolume_div_modelVolume ballVolume_two_mul_le)

end PoincareFormalization
