import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] in
theorem tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b)) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) := by
  classical
  have hExp :
      rawTensorConnLap (I := I) g r s
          (fun z : M => T₀.toSection z) b =
        rawTensorConnLap_fixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun z : M => T₀.toSection z) b :=
    rawTensorConnLap_via_chartFrameNormGlobalSmooth
      (I := I) (M := M) g r s T₀ α hb
  have hSum :
      rawTensorConnLap_fixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun z : M => T₀.toSection z) b =
        ∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    rawTensorConnLap_fixedFrame_def (I := I) g r s
      (fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
      (fun z : M => T₀.toSection z) b
  have hRaw_sum :
      rawTensorConnLap (I := I) g r s
          (fun z : M => T₀.toSection z) b =
        ∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    hExp.trans hSum
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) with hL
  have hApply : L (rawTensorConnLap (I := I) g r s
        (fun z : M => T₀.toSection z) b) =
      L (∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) :=
    congrArg L hRaw_sum
  rw [map_sum] at hApply
  simpa [hL, ContinuousLinearMap.comp_apply] using hApply

end Connection
end Integral
end DifferentialGeometry
