import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.IsManifold.Basic




















noncomputable section

open TopologicalSpace

namespace DifferentialGeometry
namespace Geometry



theorem isSigmaCompact_of_isOpen
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M]
    {U : Set M} (hU : IsOpen U) : IsSigmaCompact U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

end Geometry
end DifferentialGeometry
