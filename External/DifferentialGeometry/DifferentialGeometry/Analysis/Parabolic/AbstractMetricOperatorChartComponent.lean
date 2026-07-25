import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Flow.DeTurckOperator
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.ContMDiff.Basic


noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem F_canonical_chart_component_smooth
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hF : DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS (I := I) F)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => F g x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E i))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E j)))
      (chartAt H α).source :=
  hF.1 g α i j

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem F_chart_component_symmetric
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hSymm : ∀ (g : SmoothRiemannianMetric I M) (x : M)
      (v w : TangentSpace I x), F g x v w = F g x w v)
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    F g x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E i))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E j)) =
      F g x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E j))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E i)) :=
  hSymm g x
    ((trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i))
    ((trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E j))

end RicciFlow
end PDE
end DifferentialGeometry
