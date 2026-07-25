import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]

theorem exists_GcurvSection_eq_appCc_curvatureOpField
    (g : SmoothRiemannianMetric I M) :
    ∃ Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0),
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        genuineCurvatureOnlySection (I := I) (M := M) g s S =
          operatorFieldApply (I := I) (M := M) g ((s + 1) + 0) ((s + 1) + 0) (Φ₀ (s + 1))
            (covGrad (I := I) (M := M) g 0 s S) := by
  obtain ⟨Φ₀, hΦ₀⟩ := exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g
  refine ⟨Φ₀, fun s S => ?_⟩
  rw [← pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]
  exact hΦ₀ (s + 1) (covGrad (I := I) (M := M) g 0 s S)

end Connection
end Integral
end DifferentialGeometry

end
