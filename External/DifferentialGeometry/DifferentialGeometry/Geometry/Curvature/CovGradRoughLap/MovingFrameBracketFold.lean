import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderCarrierSection
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameFoldPieces

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

theorem movingFrameRemainderSection_eq_sub_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    movingFrameRemainderSection (I := I) (M := M) g s S =
      pointwiseTensorCurv (I := I) (M := M) g s S -
        genuineCurvatureOnlySection (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) := by
  rw [movingFrameRemainderSection]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem frameSummed_bracketIntegral_empty_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : Fin 0 → SmoothCcTensor g 0 (s + 1)) :
    ∑ i, ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (0 + (s + 1)) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1) (W i).toSection (V i) x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toSection x))
          + covariantTensorInnerPointwise (I := I) (M := M) (0 + (s + 1)) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 (s + 1) (W i).toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toSection (V i) x))
          + tensorInnerScalar (I := I) (M := M) g 0 (s + 1) (W i).toSection
              (covGrad (I := I) (M := M) g 0 s S).toSection x
            * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

end Connection
end Integral
end DifferentialGeometry

end
