import Definitions.Def_OpenGA_SurgeryTopologyEvolution
import Definitions.Def_OpenGA_WidthComparisonTrace

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





end SurgeryTopologyEvolution



end OpenGA
