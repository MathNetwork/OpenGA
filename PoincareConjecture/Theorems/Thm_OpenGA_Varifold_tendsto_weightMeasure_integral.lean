import Definitions.Def_OpenGA_VarifoldConvergence
import Definitions.Def_OpenGA_EuclideanVarifold
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Maps.Proper.Basic



/-!
# Varifold convergence

The topology is induced by all continuous compactly supported test functions on
`E × Grassmannian E k`, not by the total mass or the weight measure alone.
It is Hausdorff, and convergence is exactly convergence of these integrals.
Spatial weight measures consequently converge against compactly supported tests on `E`.

References: Simon, *Introduction to Geometric Measure Theory*, 2018, Chapter 8;
Colding-Minicozzi, *Width and finite extinction time of Ricci flow*, arXiv:0707.0108,
Section 1.3. The latter works on a compact manifold's Grassmann bundle. No quantitative
bound for a particular metrization is asserted by this qualitative convergence interface.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped CompactlySupported

namespace OpenGA.Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}




















theorem tendsto_weightMeasure_integral {ι : Type*} {l : Filter ι}
    {V : ι → Varifold E k} {W : Varifold E k} (h : Tendsto V l (𝓝 W))
    (φ : C_c(E, ℝ)) :
    Tendsto (fun i => ∫ x, φ x ∂(V i).weightMeasure) l
      (𝓝 (∫ x, φ x ∂W.weightMeasure)) := by sorry



end OpenGA.Varifold

