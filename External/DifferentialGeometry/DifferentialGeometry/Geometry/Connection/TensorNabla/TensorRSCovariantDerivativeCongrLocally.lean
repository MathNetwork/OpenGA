import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle CovariantDerivative Filter Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRSCovariantDerivative_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ σ' : Π b : M, TensorRSSpace r s I b}
    {x : M} (hagree : ∀ᶠ y in 𝓝 x, σ y = σ' y)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
            (fun y : M =>
              TotalSpace.mk' (TensorRSModel r s ℝ E) y (σ y)) x)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
            (fun y : M =>
              TotalSpace.mk' (TensorRSModel r s ℝ E) y (σ' y)) x) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun σ x =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun σ' x := by
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := σ) (σ' := σ') (x := x)
    hσ hσ' Filter.univ_mem hagree

end Connection
end Integral
end DifferentialGeometry

end
