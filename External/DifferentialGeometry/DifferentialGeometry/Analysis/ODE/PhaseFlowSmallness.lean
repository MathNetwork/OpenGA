import DifferentialGeometry.Analysis.ODE.PhaseFlowPerturbation

set_option autoImplicit false









noncomputable section

open Filter Set Topology
open scoped NNReal Topology

namespace DifferentialGeometry
namespace PhaseFlow



@[simp] theorem phaseErr_zero : phaseErr 0 = 0 := by
  apply NNReal.eq
  simp [phaseErr]
  rfl



theorem phaseErr_cont : Continuous phaseErr := by
  unfold phaseErr
  apply Continuous.subtype_mk
  fun_prop



theorem phaseErr_tendsto : Tendsto phaseErr (nhds 0) (nhds 0) := by
  have h : Tendsto phaseErr (nhds (0 : NNReal)) (nhds (phaseErr 0)) :=
    phaseErr_cont.continuousAt
  simpa using h



theorem phaseErr_lt_ev {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ k in nhds 0, phaseErr k < eps :=
  phaseErr_tendsto (Iio_mem_nhds heps)

end PhaseFlow
end DifferentialGeometry
