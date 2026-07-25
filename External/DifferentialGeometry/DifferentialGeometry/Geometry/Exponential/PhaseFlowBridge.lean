import DifferentialGeometry.Analysis.ODE.PhaseFlowPerturbation
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



theorem freeDiag_eq_unip :
    PhaseFlow.freeDiag (E := E) =
      (unipotentCLE (E := E) : (E × E) →L[Real] (E × E)) := by
  apply ContinuousLinearMap.ext
  intro z
  simp [PhaseFlow.freeDiag_apply, unipotentCLE]

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
