import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Analysis.Integration.L2.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Support


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.TensorRSRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace SmoothCcTensor


theorem hasCompactSupport_toFun
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) : HasCompactSupport S.toFun :=
  S.hasCompactSupport


theorem hasCompactSupport_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (S.toFun x)) := by
  refine HasCompactSupport.mono (f := S.toFun) S.hasCompactSupport ?_
  intro x hx
  by_contra hSx
  apply hx
  have hSx_zero : S.toFun x = 0 := by simpa using hSx
  change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x) = 0
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0


theorem hasCompactSupport_inner_cross
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (T.toFun x)) := by
  refine HasCompactSupport.mono (f := S.toFun) S.hasCompactSupport ?_
  intro x hx
  by_contra hSx
  apply hx
  have hSx_zero : S.toFun x = 0 := by simpa using hSx
  change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (T.toFun x) = 0
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T.toFun x)

private lemma rs_baseSet_eq_chart_source (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

omit [Module.Finite ℝ E] in
private lemma tangent_baseSet_eq_chart_source (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := rfl

private lemma contMDiffOn_trivProj_chart_source
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) := by
  have hbase := rs_baseSet_eq_chart_source (E := E) (I := I) (M := M) α r s
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  exact hrewrite

private lemma continuousOn_trivProj_chart_source
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun x : M => (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) :=
  (contMDiffOn_trivProj_chart_source (I := I) (M := M) S α).continuousOn

private lemma continuous_totalSpace_section
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    Continuous
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
  S.toSection.contMDiff.continuous

omit [Module.Finite ℝ E] in
private lemma tangent_continuousLinearMapAt_self (x : M) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (b₀ := x) (b := x) (mem_chart_source H x)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) v

omit [Module.Finite ℝ E] in
private lemma tangent_symmL_self (x : M) :
    (trivializationAt E (TangentSpace I) x).symmL ℝ x = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (b₀ := x) (b := x) (mem_chart_source H x)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) v

private lemma tensor0S_continuousLinearMapAt_self_apply (s : ℕ) (x : M)
    (p : Tensor0SSpace s I x) :
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).continuousLinearMapAt ℝ x p = p := by
  have hx_base : x ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hcLMAt :
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).continuousLinearMapAt ℝ x p =
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x ⟨x, p⟩).2 := by
    change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).linearMapAt ℝ x p = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  rw [hcLMAt]
  have happly : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x ⟨x, p⟩).2 =
      p.compContinuousLinearMap
        (fun _ => (trivializationAt E (TangentSpace I) x).symmL ℝ x) := rfl
  rw [happly, tangent_symmL_self (I := I) (M := M) x]
  ext v
  change p (fun i => (1 : E →L[ℝ] E) (v i)) = p v
  congr

private lemma tensor0S_symmL_self_apply (s : ℕ) (x : M)
    (p : Tensor0SModel s ℝ E) :
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).symmL ℝ x p = p := by
  have hbase : x ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hinv : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).continuousLinearMapAt ℝ x
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).symmL ℝ x p) = p :=
    Bundle.Trivialization.continuousLinearMapAt_symmL
      (R := ℝ) (e := trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x) hbase p
  have hid := tensor0S_continuousLinearMapAt_self_apply (I := I) (M := M) s x
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).symmL ℝ x p)
  exact hid.symm.trans hinv

private lemma tensorRS_centre_point_identity
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (x : M) :
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) x ⟨x, S.toSection x⟩).2 = S.toFun x := by
  have heq :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) x ⟨x, S.toSection x⟩).2 =
      ContinuousLinearMap.inCoordinates (Tensor0SModel r ℝ E) (Tensor0SSpace r I)
        (Tensor0SModel s ℝ E) (Tensor0SSpace s I) x x x x (S.toSection x) := by
    rfl
  rw [heq]
  ext v
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [tensor0S_symmL_self_apply (I := I) (M := M) r x v]
  rw [tensor0S_continuousLinearMapAt_self_apply (I := I) (M := M) s x
    ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x) v)]
  rfl

private lemma inner_self_eq_zero_off_support
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s)
    {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x) = 0 := by
  have hSx_zero : S.toFun x = 0 := by
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0

private lemma inner_cross_eq_zero_off_S_support
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S T : SmoothCcTensor g r s)
    {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (T.toFun x) = 0 := by
  have hSx_zero : S.toFun x = 0 := by
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T.toFun x)


theorem continuous_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) :=
  TensorRSBundle.continuous_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => S.toSection b) (fun b : M => S.toSection b)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s S.toSection α)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s S.toSection α)


theorem continuous_inner_cross
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (T.toFun b)) :=
  TensorRSBundle.continuous_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => S.toSection b) (fun b : M => T.toSection b)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s S.toSection α)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s T.toSection α)


theorem aestronglyMeasurable_inner_self
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (S.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (continuous_inner_self (I := I) (M := M) S).aestronglyMeasurable


theorem aestronglyMeasurable_inner_cross
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (continuous_inner_cross (I := I) (M := M) S T).aestronglyMeasurable


theorem integrable_inner_cross
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (continuous_inner_cross (I := I) (M := M) S T).integrable_of_hasCompactSupport
    (hasCompactSupport_inner_cross (I := I) (M := M) S T)


theorem memL2_toFun
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s) :
    MemL2 (I := I) (M := M) g r s S.toFun :=
  integrable_inner_cross (I := I) (M := M) S S

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
