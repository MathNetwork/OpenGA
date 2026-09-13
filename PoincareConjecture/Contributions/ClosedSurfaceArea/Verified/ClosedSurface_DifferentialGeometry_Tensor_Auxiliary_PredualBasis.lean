import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d : ℕ}

noncomputable def Module.Basis.cDualBasis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) :
    Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) :=
  B.dualBasis.map LinearMap.toContinuousLinearMap

end
