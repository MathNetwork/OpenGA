import DifferentialGeometry.Analysis.ODE.Flow.Variational

set_option autoImplicit false








noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



def flatPhaseCLM : (E × E) →L[Real] (E × E) :=
  (ContinuousLinearMap.snd Real E E).prod (0 : (E × E) →L[Real] E)

@[simp]
theorem flatPhaseCLM_apply (z : E × E) :
    flatPhaseCLM (E := E) z = (z.2, 0) := by
  simp [flatPhaseCLM]


def flatPhaseFlowCLM (t : Real) : (E × E) →L[Real] (E × E) :=
  (ContinuousLinearMap.fst Real E E +
      t • ContinuousLinearMap.snd Real E E).prod
    (ContinuousLinearMap.snd Real E E)

@[simp]
theorem flatPhaseFlowCLM_apply (t : Real) (z : E × E) :
    flatPhaseFlowCLM (E := E) t z = (z.1 + t • z.2, z.2) := by
  simp [flatPhaseFlowCLM]

@[simp]
theorem flatPhaseFlowCLM_zero :
    flatPhaseFlowCLM (E := E) 0 = ContinuousLinearMap.id Real (E × E) := by
  ext z <;> simp


theorem flatPhaseFlow_hasDerivAt (z : E × E) (t : Real) :
    HasDerivAt (fun s : Real => flatPhaseFlowCLM (E := E) s z)
      (flatPhaseCLM (E := E) (flatPhaseFlowCLM (E := E) t z)) t := by
  have hx := ((hasDerivAt_id t).smul_const z.2).const_add z.1
  have hv := hasDerivAt_const t z.2
  simpa using hx.prodMk hv



theorem flatPhase_is_var
    {f : Real → (E × E) → (E × E)}
    (hfd : ∀ t,
      fderiv Real (f t) (0 : E × E) = flatPhaseCLM (E := E))
    (δ : E × E) :
    Analysis.ODE.IsVariationalSolution f (fun _ => (0 : E × E)) δ 0
      (fun t => flatPhaseFlowCLM (E := E) t δ) := by
  constructor
  · simp
  · intro t
    rw [hfd t]
    exact flatPhaseFlow_hasDerivAt δ t

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
