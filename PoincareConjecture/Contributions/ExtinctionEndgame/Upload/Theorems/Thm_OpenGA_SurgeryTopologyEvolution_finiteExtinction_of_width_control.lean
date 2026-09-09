import Definitions.Def_OpenGA_ExtinctionWidthControl
import Definitions.Def_OpenGA_WidthExtinctionTime



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




theorem finiteExtinction_of_width_control (E : SurgeryTopologyEvolution M)
    {W : ℝ} (h : E.HasWidthControl W) : E.FiniteExtinction := by sorry



end SurgeryTopologyEvolution



end OpenGA

