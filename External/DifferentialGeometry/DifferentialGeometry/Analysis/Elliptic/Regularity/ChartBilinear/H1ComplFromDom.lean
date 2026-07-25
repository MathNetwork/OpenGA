import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
import DifferentialGeometry.Analysis.Elliptic.Operator.VariationalLaplacian
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1ComplFromDom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_approx_seq
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h) := by
  classical
  have h_dense :
      u_h ∈ closure (Set.range (smoothToH1Compl (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToH1Compl (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToH1Compl (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_approx_seq_lp
    (g : SmoothRiemannianMetric I M)
    (f_h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) atTop (𝓝 f_h) := by
  classical
  have h_dense :
      f_h ∈ closure (Set.range (smoothToLp (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToLp (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToLp (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

end ChartBilinearH1ComplFromDom
end Laplacian
end Analysis
end DifferentialGeometry
