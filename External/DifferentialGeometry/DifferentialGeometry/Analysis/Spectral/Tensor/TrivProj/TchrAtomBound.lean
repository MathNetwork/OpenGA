import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.CovNormBound
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
private lemma pouTsupport_subset_chartAt_source (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source := by
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hb_base
  exact hb_base

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_sq_triv_christoffel_correction_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b')
        (X : Π b' : M, TangentSpace I b')
        {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (- (∑ i : Fin r,
                chartTensorRSInputSlotCorrection (I := I) r s g α T X b i)
              + (∑ l : Fin s,
                  chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l))‖ ^ 2 ≤
        K * tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (- (∑ i : Fin r,
                  chartTensorRSInputSlotCorrection (I := I) r s g α T X b i)
                + (∑ l : Fin s,
                    chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)))
            (TensorRSSpace.toModel
              (- (∑ i : Fin r,
                  chartTensorRSInputSlotCorrection (I := I) r s g α T X b i)
                + (∑ l : Fin s,
                    chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l))) := by
  classical
  obtain ⟨K, hK_nn, hK_le⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K, hK_nn, ?_⟩
  intro T X b hb
  set Csum : TensorRSSpace r s I b :=
    - (∑ i : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b i)
      + (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
    with hCsum_def
  have hb_chart_src : b ∈ (chartAt H α).source :=
    pouTsupport_subset_chartAt_source (I := I) (M := M) α hb
  have h_bridge :
      (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          Csum =
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel Csum) :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α hb_chart_src Csum
  have h_twist_bound :
      ‖chartRSTwistInv (I := I) (M := M) α b r s
            (TensorRSSpace.toModel Csum)‖ ^ 2 ≤
        K * tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel Csum) (TensorRSSpace.toModel Csum) :=
    hK_le hb (TensorRSSpace.toModel Csum)
  rw [h_bridge]
  exact h_twist_bound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
