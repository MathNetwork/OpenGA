import DifferentialGeometry.Analysis.Integration.L2.Pairing.MovingFrameBracketDivergence
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapLoweredIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_frameSummed_covDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) :
    ∑ i, ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g r s
    (W i).toSection Z.toSection (V i)

theorem weitzenbock_curvature_crossPairing_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  have hw := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g s S
  have hCurv :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := rfl
  rw [hCurv] at hw
  linarith [hw]

theorem movingFrameNullity_of_genuineCrossPairingValue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcd : SmoothCcTensor g 0 (s + 1))
    (hval : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineCurvatureOnlySection (I := I) (M := M) g s S + Gcd).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          genuineCurvatureOnlySection (I := I) (M := M) g s S - Gcd).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  have hpair :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (genuineCurvatureOnlySection (I := I) (M := M) g s S + Gcd).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [hval, weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]
  exact tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing
    (I := I) (M := M) g s S (genuineCurvatureOnlySection (I := I) (M := M) g s S) Gcd hpair

end Connection
end Integral
end DifferentialGeometry

end
