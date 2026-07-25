import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorChartComponentSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.SmoothApprox
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorChartFrameSection
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.PouCutoffComponentBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransitionTransport
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.ChartTransitionTransportCLM


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toEuclidean_extChartAt_mem_chartTargetEuclid
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (toEuclidean (E := E)) (extChartAt I α x) ∈
      chartTargetEuclid (I := I) (M := M) α := by
  refine ⟨extChartAt I α x, ?_, rfl⟩
  exact (extChartAt I α).map_source
    (by rw [extChartAt_source (I := I)]; exact hx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma symm_toEuclidean_symm_toEuclidean_extChartAt
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (extChartAt I α).symm
        ((toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) (extChartAt I α x))) = x := by
  rw [(toEuclidean (E := E)).symm_apply_apply]
  exact (extChartAt I α).left_inv
    (by rw [extChartAt_source (I := I)]; exact hx)

section Unconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

def chosenComp (α : M) (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Classical.choose
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)

omit [CompleteSpace E] in
private lemma chosenComp_contDiffOn
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s i α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).1

omit [CompleteSpace E] in
private lemma chosenComp_hasCompactSupport
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chosenComp (I := I) (M := M) g r s i α P) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).2.1

omit [CompleteSpace E] in
private lemma chosenComp_tsupport (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chosenComp (I := I) (M := M) g r s i α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).2.2.1

omit [CompleteSpace E] in
lemma chosenComp_ae_eq (α : M) (P : TensorCompIdx (E := E) r s) :
    chosenComp (I := I) (M := M) g r s i α P
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α P :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).2.2.2

omit [CompleteSpace E] in
private lemma chosenComp_hu (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s i α P)
        (chartTargetEuclid (I := I) (M := M) α) :=
  fun P => chosenComp_contDiffOn (I := I) (M := M) g r s i α P

omit [CompleteSpace E] in
private lemma chosenComp_hsupp (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      HasCompactSupport (chosenComp (I := I) (M := M) g r s i α P) ∧
        tsupport (chosenComp (I := I) (M := M) g r s i α P) ⊆
          chartTargetEuclid (I := I) (M := M) α :=
  fun P => ⟨chosenComp_hasCompactSupport (I := I) (M := M) g r s i α P,
    chosenComp_tsupport (I := I) (M := M) g r s i α P⟩

def eigenvectorSmoothChart (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α)

omit [CompleteSpace E] in
lemma tensorChartComponentRaw_eigenvectorSmoothChart_self
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chosenComp (I := I) (M := M) g r s i α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α) P hy

noncomputable def eigenvectorSmooth : SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    eigenvectorSmoothChart (I := I) (M := M) g r s i α

omit [CompleteSpace E] in
lemma eigenvectorSmooth_eq :
    eigenvectorSmooth (I := I) (M := M) g r s i =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        eigenvectorSmoothChart (I := I) (M := M) g r s i α := rfl

omit [CompleteSpace E] in
private lemma eigenvectorSmoothChart_toSection_eq_zero_off_source
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x =
      0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α) hx

omit [CompleteSpace E] in
lemma tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        β P.1 P.2 x = 0 := by
  rw [tensorChartComponentRaw_def]
  have hsec :
      (eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x = 0 :=
    eigenvectorSmoothChart_toSection_eq_zero_off_source
      (I := I) (M := M) g r s i α hx
  rw [show tensorTrivProj (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α) β x =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).continuousLinearMapAt ℝ x
        ((eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x)
      from rfl, hsec, map_zero, map_zero]

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
