import DifferentialGeometry.Analysis.Spectral.Tensor.Rellich.TensorL2SubsequenceExtraction
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Sequences

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_TensorH1ComplToTensorL2_apply_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (v : TensorH1Compl g r s) :
    ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s v‖ ≤ ‖v‖ := by
  refine UniformSpace.Completion.induction_on (α := SmoothCcTensorH1 g r s) v ?_ ?_
  · have h_cont_lhs : Continuous (fun w : TensorH1Compl g r s =>
        ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s w‖) :=
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.norm
    have h_cont_rhs : Continuous (fun w : TensorH1Compl g r s => ‖w‖) :=
      continuous_norm
    exact isClosed_le h_cont_lhs h_cont_rhs
  · intro a
    have h_eq : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          ((a : TensorH1Compl g r s)) =
        (a.toCcTensor : TensorL2 r s g) := by
      have h := TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
        (I := I) (M := M) g r s a
      simpa using h
    have h_norm : ‖((a : TensorH1Compl g r s) : TensorH1Compl g r s)‖ = ‖a‖ :=
      UniformSpace.Completion.norm_coe a
    rw [h_eq, h_norm]
    have h_coe_norm :
        ‖(a.toCcTensor : TensorL2 r s g)‖ = ‖a.toCcTensor‖ :=
      UniformSpace.Completion.norm_coe _
    rw [h_coe_norm]
    exact SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) a


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma denseRange_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  change DenseRange (UniformSpace.Completion.toComplL :
      SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s)
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_smooth_close_to_TensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (v : TensorH1Compl g r s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : SmoothCcTensorH1 g r s,
      ‖v - smoothToTensorH1Compl (I := I) (M := M) g r s S‖ < δ := by
  have h_dense : DenseRange (smoothToTensorH1Compl (I := I) (M := M) g r s) :=
    denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall] at h_dense
  have hv_in : v ∈ closure
      (Set.range (smoothToTensorH1Compl (I := I) (M := M) g r s)) :=
    h_dense v
  rw [Metric.mem_closure_iff] at hv_in
  obtain ⟨q, ⟨S, hS_eq⟩, hS_close⟩ := hv_in δ hδ
  refine ⟨S, ?_⟩
  rw [show smoothToTensorH1Compl (I := I) (M := M) g r s S = q from hS_eq]
  rw [dist_eq_norm] at hS_close
  exact hS_close

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
