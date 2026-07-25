import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g 0 (s + 1) X Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 (s + 1) Y X
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x =
      riemannOp (tensorCov (I := I) g 0 (s + 1)) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
  tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 (s + 1)
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y)
    hX hY (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff


omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_covGrad_fiberNormSq_le_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ v w : TangentSpace I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g (s + 1) x
  refine ⟨Cx, hCx_nonneg, fun v w => ?_⟩
  exact hbound v w ((covGrad (I := I) (M := M) g 0 s S).toSection x)

end Connection
end Integral
end DifferentialGeometry

end
