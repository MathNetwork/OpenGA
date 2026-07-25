import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_two_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ := by
  classical
  have hsmooth :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  have hcc :=
    tensorChartComponentScalar_hasCompactSupport
      (I := I) (M := M) g r s S α Idx Jdx
  have hcont : Continuous
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
    hsmooth.continuous
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (hcont.memLp_of_hasCompactSupport
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) (p := 2) hcc).eLpNorm_lt_top

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := by
  classical
  have hlt :=
    tensorChartComponentScalar_eLpNorm_two_lt_top
      (I := I) (M := M) g r s S α Idx Jdx
  have hne : eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := hlt.ne
  set a : ℝ := (eLpNorm
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal with ha_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + 1, by linarith, ?_⟩
  have h_lhs_eq : eLpNorm
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) = ENNReal.ofReal a := by
    rw [ha_def, ENNReal.ofReal_toReal hne]
  rw [h_lhs_eq]
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have h_one_le :
      (1 : ℝ≥0∞) ≤
        (ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := le_add_self
  have h2 : ENNReal.ofReal (a + 1) ≤
      ENNReal.ofReal (a + 1) *
        (ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) :=
    calc ENNReal.ofReal (a + 1)
        = ENNReal.ofReal (a + 1) * 1 := by rw [mul_one]
      _ ≤ ENNReal.ofReal (a + 1) *
            (ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) :=
            mul_le_mul_of_nonneg_left h_one_le (by exact zero_le _)
  exact h1.trans h2

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_le_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensor g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := fun S =>
  tensorChartComponentScalar_eLpNorm_le_per_section
    (I := I) (M := M) g r s S α Idx Jdx

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
