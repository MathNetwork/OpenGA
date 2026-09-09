import Definitions.Def_OpenGA_ExtinctionWidthControl
import Definitions.Def_OpenGA_WidthExtinctionTime
import Theorems.Thm_OpenGA_WidthComparisonTrace_le_extinctionTime

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



/-- **Math.** If each nonempty slice supplies a trace with the same initial
bound, all slices beyond an explicit positive time must be empty. -/
theorem _root_.solution (E : SurgeryTopologyEvolution M)
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



end SurgeryTopologyEvolution



end OpenGA
