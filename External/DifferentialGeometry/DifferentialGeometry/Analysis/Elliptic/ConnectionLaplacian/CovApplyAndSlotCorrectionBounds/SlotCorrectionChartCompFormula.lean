import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorRSInputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun i : Fin r =>
              (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
          : ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun j : Fin s =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) = _
  rw [chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
    ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
    (fun j : Fin s =>
      chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))]
  have hsubst :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin r => TangentSpace I b) ℝ from
        tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))) =
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
          (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) := by
    refine ContinuousMultilinearMap.ext ?_
    intro w
    rw [tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b B))
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) w]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl
  have hsubst_fiber :
      (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
        : Tensor0SSpace r I b) =
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
          (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) :=
    hsubst
  rw [hsubst_fiber]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
          : ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun j : Fin s =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) = _
  exact chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l
    ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
    (fun j : Fin s =>
      chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin 1)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) 1 2 g α T B b k)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace I b) ℝ from
        (show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          ((dualCoordinateProductMultilinearMap (E := E) 1 Idx).compContinuousLinearMap
            (fun i : Fin 1 =>
              (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                (tangentSlotCLM (I := I) 1 k
                  (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin 2 =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) :=
  chartTensorRSInputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb k Idx Jdx

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) 1 2 g α T B b l)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace I b) ℝ from
        (show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          ((dualCoordinateProductMultilinearMap (E := E) 1 Idx).compContinuousLinearMap
            (fun _ : Fin 1 => chartTrivializationLinearMap (I := I) (M := M) α b)))
        (fun j : Fin 2 =>
          tangentSlotCLM (I := I) 2 l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))) :=
  chartTensorRSOutputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb l Idx Jdx

end Connection
end Integral
end DifferentialGeometry
