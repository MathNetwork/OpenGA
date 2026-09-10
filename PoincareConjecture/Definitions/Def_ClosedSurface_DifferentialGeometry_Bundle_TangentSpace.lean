import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def tangentSpaceModelContinuousLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E := by
  unfold TangentSpace
  exact ContinuousLinearEquiv.refl 𝕜 E

theorem tangentSpaceModelContinuousLinearEquiv_apply (x : M)
    (v : TangentSpace I x) : tangentSpaceModelContinuousLinearEquiv (I := I) x v = v := by
  rfl

end DifferentialGeometry
