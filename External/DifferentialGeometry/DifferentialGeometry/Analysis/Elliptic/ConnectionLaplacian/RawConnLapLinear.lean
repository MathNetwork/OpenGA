import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound









noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



noncomputable def rawConnLapLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] SmoothCcTensor g r s where
  toFun T := rawTensorConnLapSmooth (I := I) g r s T
  map_add' T₁ T₂ := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    have hsum :=
      tensorConnLaplacian_of_contMDiff_add (I := I) g r s T₁ T₂
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => T₁.toSection z) T₁.toSection.contMDiff_toFun)
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => T₂.toSection z) T₂.toSection.contMDiff_toFun)
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => (T₁ + T₂).toSection z)
          (T₁ + T₂).toSection.contMDiff_toFun) x
    have hLHS :
        (rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂)).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s (T₁ + T₂)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (T₁ + T₂).toSection z)
              (T₁ + T₂).toSection.contMDiff_toFun)).toSection x := rfl
    have hRHS₁ :
        (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T₁
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₁.toSection z)
              T₁.toSection.contMDiff_toFun)).toSection x := rfl
    have hRHS₂ :
        (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T₂
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₂.toSection z)
              T₂.toSection.contMDiff_toFun)).toSection x := rfl
    have hsum_section :
        (rawTensorConnLapSmooth (I := I) g r s T₁ +
            rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x +
            (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x := by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
      rfl
    rw [hLHS, hsum_section, hRHS₁, hRHS₂]
    exact hsum
  map_smul' c T := by
    change rawTensorConnLapSmooth (I := I) g r s (c • T) =
      c • rawTensorConnLapSmooth (I := I) g r s T
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    have hsmul :=
      tensorConnLaplacian_of_contMDiff_smul (I := I) g r s c T
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => T.toSection z) T.toSection.contMDiff_toFun)
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => (c • T).toSection z)
          (c • T).toSection.contMDiff_toFun) x
    have hLHS :
        (rawTensorConnLapSmooth (I := I) g r s (c • T)).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s (c • T)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (c • T).toSection z)
              (c • T).toSection.contMDiff_toFun)).toSection x := rfl
    have hRHS :
        (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T.toSection z)
              T.toSection.contMDiff_toFun)).toSection x := rfl
    have hsmul_section :
        (c • rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          c • (rawTensorConnLapSmooth (I := I) g r s T).toSection x := by
      rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
      rfl
    rw [hLHS, hsmul_section, hRHS]
    exact hsmul


omit [CompactSpace M] [I.Boundaryless] in
@[simp] theorem rawConnLapLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawConnLapLin (I := I) g r s T =
      rawTensorConnLapSmooth (I := I) g r s T := rfl

end Connection
end Integral
end DifferentialGeometry

end
