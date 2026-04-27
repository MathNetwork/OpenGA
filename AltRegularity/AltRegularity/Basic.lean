import Mathlib.Topology.MetricSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-!
# AltRegularity.Basic

Common imports and conventions used throughout the formalization of
"Alternative Regularity via Non-Excessive Sweepouts."

The ambient space $M^{n+1}$ in the paper is a closed Riemannian manifold of
dimension $n+1 \ge 3$. For the formalization we use a metric measurable space
endowed with the Borel sigma-algebra and the compact-space property
(`[MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]`).
A future refinement via `SmoothManifoldWithCorners` is left for later.
-/

namespace AltRegularity

end AltRegularity
