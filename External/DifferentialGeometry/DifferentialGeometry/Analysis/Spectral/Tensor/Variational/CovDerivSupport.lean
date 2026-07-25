import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn


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
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCovDerivAt_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M)
    (hx_nhds : ∀ᶠ y in 𝓝 x, S.toSection y = 0) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v = 0 := by
  classical
  set cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  have hS_diff :=
    (S.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt (x := x)
  have hzero_diff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (Bundle.zeroSection (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y)) x :=
    (Bundle.mdifferentiable_zeroSection
      (𝕜 := ℝ) (IB := I) (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)).mdifferentiableAt
  have hev : ∀ᶠ y in 𝓝 x,
      (fun y : M => S.toSection y) y =
        ((0 : (y : M) → TensorRSSpace r s I y)) y := hx_nhds
  have hcongr := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := fun y : M => S.toSection y)
    (σ' := (0 : (y : M) → TensorRSSpace r s I y))
    hS_diff hzero_diff (Filter.univ_mem) hev
  have hcov_zero := cov.isCovariantDerivativeOnUniv.zero
    (x := x) (hx := (by trivial : x ∈ (Set.univ : Set M)))
  unfold tensorCovDerivAt
  change cov.toFun (fun y : M => S.toSection y) x v = (0 : E →L[ℝ] _) v
  rw [hcongr, hcov_zero]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivAt_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport S.toFun) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v = 0 := by
  classical
  have hopen : IsOpen (tsupport S.toFun)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hmem : x ∈ (tsupport S.toFun)ᶜ := hx
  have hnhd : (tsupport S.toFun)ᶜ ∈ 𝓝 x := hopen.mem_nhds hmem
  have hev : ∀ᶠ y in 𝓝 x, S.toSection y = 0 := by
    filter_upwards [hnhd] with y hy
    have hy_notsupp : y ∉ Function.support S.toFun := fun hyS => hy (subset_tsupport _ hyS)
    have hy_zero : S.toFun y = 0 := by
      simpa [Function.support, Function.mem_support] using hy_notsupp
    have hto : TensorRSSpace.toModel (S.toSection y) = 0 := by
      have : S.toFun y = TensorRSSpace.toModel (S.toSection y) := rfl
      rw [this] at hy_zero
      exact hy_zero
    have htoModel_zero : TensorRSSpace.toModel
        (0 : TensorRSSpace r s I y) = 0 := TensorRSSpace.toModel_zero
    have hcomb : TensorRSSpace.toModel (S.toSection y) =
        TensorRSSpace.toModel (0 : TensorRSSpace r s I y) := by
      rw [hto, htoModel_zero]
    exact TensorRSSpace.toModel_injective
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := y) hcomb
  exact tensorCovDerivAt_eq_zero_of_eventuallyEq_zero
    (I := I) (M := M) g r s S x hev v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x = 0 := by
  unfold tensorCovDerivPointwiseInner
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S x
      ((chartModelBasis E) i) = 0 :=
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S
      hx ((chartModelBasis E) i)
  rw [hSi, TensorRSSpace.toModel_zero, tensorInnerPointwise_zero_left]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    HasCompactSupport
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  refine IsCompact.of_isClosed_subset S.hasCompactSupport (isClosed_tsupport _) ?_
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  exact hx (tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (I := I) (M := M) g r s S T hx_notsupp)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_tsupport_subset_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tsupport (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) ⊆
      tsupport S.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  exact hx (tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (I := I) (M := M) g r s S T hx_notsupp)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_tsupport_subset_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tsupport (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) ⊆
      tsupport T.toFun := by
  have hswap : tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T S := by
    funext x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x
  rw [hswap]
  exact tensorCovDerivPointwiseInner_tsupport_subset_left
    (I := I) (M := M) g r s T S

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
