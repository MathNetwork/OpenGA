import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] in
theorem rawTensorConnLap_via_chartFrameNormGlobalSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    rawTensorConnLap (I := I) g r s
        (fun y : M => T.toSection y) b =
      rawTensorConnLap_fixedFrame (I := I) g r s
        (fun i : Fin (Module.finrank ℝ E) =>
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
        (fun y : M => T.toSection y) b := by
  classical
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  have hB_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) y
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun y)) :=
    fun i => (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j =>
      chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
        (I := I) (M := M) g α hb i j
  exact rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s
    (fun y : M => T.toSection y) hT_total
    (B := fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
    hB_smooth b hB_orth

end Connection
end Integral
end DifferentialGeometry
