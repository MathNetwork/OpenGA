import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Operator.PointwiseMixed
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


def smoothCcToL2Submodule (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Submodule ℝ (TensorL2 r s g) :=
  LinearMap.range
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)


def connLaplacianL2Action (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] TensorL2 r s g where
  toFun T :=
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
      (rawTensorConnLapSmooth (I := I) g r s T)
  map_add' T₁ T₂ := by
    have h_lap_add :
        rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂) =
          rawTensorConnLapSmooth (I := I) g r s T₁ +
            rawTensorConnLapSmooth (I := I) g r s T₂ := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      have hsum :=
        tensorConnLaplacian_of_contMDiff_add (I := I) g r s T₁ T₂
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T₁.toSection z) T₁.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T₂.toSection z) T₂.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => (T₁ + T₂).toSection z)
            (T₁ + T₂).toSection.contMDiff_toFun) x
      have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂)).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s (T₁ + T₂)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (T₁ + T₂).toSection z)
              (T₁ + T₂).toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T₁
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₁.toSection z)
              T₁.toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T₂
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₂.toSection z)
              T₂.toSection.contMDiff_toFun)).toSection x := rfl
      have hsum_section :
          (rawTensorConnLapSmooth (I := I) g r s T₁ +
              rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
            (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x +
              (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x := by
        rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
        rfl
      rw [hLHS, hsum_section, hRHS₁, hRHS₂]
      exact hsum
    rw [h_lap_add, SmoothCcTensor.toL2_add]
  map_smul' c T := by
    have h_lap_smul :
        rawTensorConnLapSmooth (I := I) g r s (c • T) =
          c • rawTensorConnLapSmooth (I := I) g r s T := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      have hsmul :=
        tensorConnLaplacian_of_contMDiff_smul (I := I) g r s c T
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T.toSection z) T.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => (c • T).toSection z)
            (c • T).toSection.contMDiff_toFun) x
      have hLHS : (rawTensorConnLapSmooth (I := I) g r s (c • T)).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s (c • T)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (c • T).toSection z)
              (c • T).toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T.toSection z)
              T.toSection.contMDiff_toFun)).toSection x := rfl
      have hsmul_section :
          (c • rawTensorConnLapSmooth (I := I) g r s T).toSection x =
            c • (rawTensorConnLapSmooth (I := I) g r s T).toSection x := by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
        rfl
      rw [hLHS, hsmul_section, hRHS]
      exact hsmul
    rw [h_lap_smul, SmoothCcTensor.toL2_smul]
    rfl

omit [CompactSpace M] in
@[simp] lemma connLaplacianL2Action_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    connLaplacianL2Action (I := I) g r s T =
      SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (rawTensorConnLapSmooth (I := I) g r s T) := rfl


def toL2RangeRestrict (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] smoothCcToL2Submodule (I := I) g r s :=
  LinearMap.rangeRestrict
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2RangeRestrict_surjective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Surjective (toL2RangeRestrict (I := I) g r s) := by
  intro u
  obtain ⟨T, hT⟩ := u.property
  refine ⟨T, ?_⟩
  apply Subtype.ext
  exact hT


def smoothCcSection (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] SmoothCcTensor g r s :=
  Classical.choose
    ((toL2RangeRestrict (I := I) g r s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (toL2RangeRestrict_surjective (I := I) g r s)))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2RangeRestrict_smoothCcSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (toL2RangeRestrict (I := I) g r s).comp (smoothCcSection (I := I) g r s) =
      LinearMap.id :=
  Classical.choose_spec
    ((toL2RangeRestrict (I := I) g r s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (toL2RangeRestrict_surjective (I := I) g r s)))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2RangeRestrict_smoothCcSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    (toL2RangeRestrict (I := I) g r s) (smoothCcSection (I := I) g r s u) =
      u := by
  have h := toL2RangeRestrict_smoothCcSection (I := I) g r s
  exact congrArg (fun (f : _ →ₗ[ℝ] _) => f u) h


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2_smoothCcSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (smoothCcSection (I := I) g r s u) = (u : TensorL2 r s g) := by
  have h := toL2RangeRestrict_smoothCcSection_apply (I := I) g r s u
  have hval : ((toL2RangeRestrict (I := I) g r s)
      (smoothCcSection (I := I) g r s u)).val = (u : TensorL2 r s g) := by
    exact congrArg Subtype.val h
  change SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
      (smoothCcSection (I := I) g r s u) = (u : TensorL2 r s g)
  have hrr : ((toL2RangeRestrict (I := I) g r s)
      (smoothCcSection (I := I) g r s u)).val =
      SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (smoothCcSection (I := I) g r s u) := rfl
  rw [hrr] at hval
  exact hval


def connLaplacianL2OnDomain (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] TensorL2 r s g :=
  (connLaplacianL2Action (I := I) g r s).comp
    (smoothCcSection (I := I) g r s)

omit [CompactSpace M] in
@[simp] lemma connLaplacianL2OnDomain_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    connLaplacianL2OnDomain (I := I) g r s u =
      connLaplacianL2Action (I := I) g r s
        (smoothCcSection (I := I) g r s u) := rfl


def connLaplacianL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g where
  domain := smoothCcToL2Submodule (I := I) g r s
  toFun := connLaplacianL2OnDomain (I := I) g r s


omit [CompactSpace M] in
@[simp] theorem connLaplacianL2_domain_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (connLaplacianL2 (I := I) g r s).domain =
      smoothCcToL2Submodule (I := I) g r s := rfl


omit [CompactSpace M] in
theorem connLaplacianL2_apply_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    (connLaplacianL2 (I := I) g r s)
        ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩ =
      connLaplacianL2Action (I := I) g r s
        (smoothCcSection (I := I) g r s
          ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩) := rfl


omit [CompactSpace M] in
theorem toL2_mem_connLaplacianL2_domain
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain := by
  rw [connLaplacianL2_domain_eq]
  exact LinearMap.mem_range_self _ T

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
