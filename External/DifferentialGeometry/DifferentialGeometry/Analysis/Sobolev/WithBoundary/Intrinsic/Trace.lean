import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Defs
import DifferentialGeometry.Geometry.Boundary.SurfaceMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private local instance instMeasurableSpaceM : MeasurableSpace M := borel M
private local instance instBorelSpaceM : BorelSpace M := ⟨rfl⟩
private local instance instMeasurableSpaceBoundary :
    MeasurableSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :=
  borel _
private local instance instBorelSpaceBoundary :
    BorelSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) := ⟨rfl⟩

def boundaryRestrict (u : M → ℝ) :
    BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M → ℝ :=
  fun x => u (x : M)

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryRestrict_apply (u : M → ℝ)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryRestrict (n := n) (M := M) u x = u (x : M) := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryRestrict_add (u v : M → ℝ) :
    boundaryRestrict (n := n) (M := M) (fun x => u x + v x) =
      fun x => boundaryRestrict (n := n) (M := M) u x +
        boundaryRestrict (n := n) (M := M) v x := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryRestrict_const_smul (c : ℝ) (u : M → ℝ) :
    boundaryRestrict (n := n) (M := M) (fun x => c * u x) =
      fun x => c * boundaryRestrict (n := n) (M := M) u x := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryRestrict_zero :
    boundaryRestrict (n := n) (M := M) (fun _ : M => (0 : ℝ)) =
      fun _ => (0 : ℝ) := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
theorem boundaryRestrict_continuous {u : M → ℝ} (hu : Continuous u) :
    Continuous (boundaryRestrict (n := n) (M := M) u) :=
  hu.comp continuous_subtype_val

theorem boundaryRestrict_aestronglyMeasurable
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {u : M → ℝ} (hu : Continuous u) :
    AEStronglyMeasurable (boundaryRestrict (n := n) (M := M) u)
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  (boundaryRestrict_continuous (n := n) (M := M) hu).aestronglyMeasurable

instance instCompactSpaceBoundaryManifold [CompactSpace M] :
    CompactSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) := by
  have hOne : (∞ : WithTop ℕ∞) ≠ 0 := by
    intro h
    have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
    exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')
  have h_closed :
      IsClosed
        ((modelWithCornersEuclideanHalfSpace n).boundary M) :=
    ModelWithCorners.isClosed_boundary
      (I := modelWithCornersEuclideanHalfSpace n) (n := ∞) hOne
  have h_compact :
      IsCompact
        ((modelWithCornersEuclideanHalfSpace n).boundary M) :=
    h_closed.isCompact
  exact isCompact_iff_compactSpace.mp h_compact

instance instIsFiniteMeasureSurfaceMeasure
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) :
    IsFiniteMeasure
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    surfaceMeasure_isFiniteMeasureOnCompacts (I := modelWithCornersEuclideanHalfSpace n)
      (M := M) g
  exact CompactSpace.isFiniteMeasure
    (μ := surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)

def boundaryTotalMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) : ℝ≥0∞ :=
  (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)
    Set.univ

theorem boundaryTotalMeasure_lt_top
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryTotalMeasure (n := n) (M := M) g < ⊤ :=
  measure_lt_top _ _

theorem boundaryTotalMeasure_ne_top
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryTotalMeasure (n := n) (M := M) g ≠ ⊤ :=
  (boundaryTotalMeasure_lt_top (n := n) (M := M) g).ne

private theorem exists_continuous_bound_of_compact
    [CompactSpace M] {u : M → ℝ} (hu : Continuous u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖u x‖ ≤ C := by
  have hu_norm : Continuous (fun x : M => ‖u x‖) := hu.norm
  have h_range_compact : IsCompact (Set.range (fun x : M => ‖u x‖)) :=
    isCompact_range hu_norm
  have h_bdd : BddAbove (Set.range (fun x : M => ‖u x‖)) := h_range_compact.bddAbove
  obtain ⟨C₀, hC₀⟩ := h_bdd
  refine ⟨max 0 C₀, le_max_left _ _, fun x => ?_⟩
  have hxR : ‖u x‖ ∈ Set.range (fun x : M => ‖u x‖) := ⟨x, rfl⟩
  exact (hC₀ hxR).trans (le_max_right _ _)

theorem boundaryRestrict_memLp_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    MemLp (boundaryRestrict (n := n) (M := M) u) p
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  obtain ⟨C, _hC_nonneg, hC⟩ :=
    exists_continuous_bound_of_compact (M := M) hu
  have h_bound :
      ∀ x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M,
        ‖boundaryRestrict (n := n) (M := M) u x‖ ≤ C := fun x => hC (x : M)
  have h_ae : ∀ᵐ x ∂(surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n)
      (M := M) g),
        ‖boundaryRestrict (n := n) (M := M) u x‖ ≤ C :=
    Filter.Eventually.of_forall h_bound
  exact MemLp.of_bound
    (boundaryRestrict_aestronglyMeasurable (n := n) (M := M) g hu) C h_ae

theorem boundaryRestrict_eLpNorm_le_of_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} {C : ℝ}
    (hC : ∀ x : M, ‖u x‖ ≤ C) :
    eLpNorm (boundaryRestrict (n := n) (M := M) u) p
        (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
      boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
        ENNReal.ofReal C := by
  have h_ae : ∀ᵐ x ∂(surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n)
      (M := M) g),
        ‖boundaryRestrict (n := n) (M := M) u x‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact hC (x : M)
  exact eLpNorm_le_of_ae_bound h_ae

theorem boundaryRestrict_eLpNorm_le_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (boundaryRestrict (n := n) (M := M) u) p
          (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
        boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
          ENNReal.ofReal C := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_continuous_bound_of_compact (M := M) hu
  exact ⟨C, hC_nonneg,
    boundaryRestrict_eLpNorm_le_of_bound (n := n) (M := M) g p hC⟩

def boundaryTrace (u : M → ℝ) :
    BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M → ℝ :=
  boundaryRestrict (n := n) (M := M) u

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryTrace_apply (u : M → ℝ)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryTrace (n := n) (M := M) u x = u (x : M) := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryTrace_eq_boundaryRestrict (u : M → ℝ) :
    boundaryTrace (n := n) (M := M) u =
      boundaryRestrict (n := n) (M := M) u := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
theorem boundaryTrace_eq_restrict_of_continuous
    {u : M → ℝ} (_hu : Continuous u) :
    boundaryTrace (n := n) (M := M) u =
      fun x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        u (x : M) := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryTrace_add (u v : M → ℝ) :
    boundaryTrace (n := n) (M := M) (fun x => u x + v x) =
      fun x => boundaryTrace (n := n) (M := M) u x +
        boundaryTrace (n := n) (M := M) v x := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryTrace_const_smul (c : ℝ) (u : M → ℝ) :
    boundaryTrace (n := n) (M := M) (fun x => c * u x) =
      fun x => c * boundaryTrace (n := n) (M := M) u x := rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
@[simp] lemma boundaryTrace_zero :
    boundaryTrace (n := n) (M := M) (fun _ : M => (0 : ℝ)) =
      fun _ => (0 : ℝ) := rfl

theorem boundaryTrace_memLp_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    MemLp (boundaryTrace (n := n) (M := M) u) p
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  boundaryRestrict_memLp_of_continuous (n := n) (M := M) g p hu

theorem boundaryTrace_eLpNorm_le_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (boundaryTrace (n := n) (M := M) u) p
          (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
        boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
          ENNReal.ofReal C :=
  boundaryRestrict_eLpNorm_le_of_continuous (n := n) (M := M) g p hu

theorem boundaryTrace_eLpNorm_le_of_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} {C : ℝ}
    (hC : ∀ x : M, ‖u x‖ ≤ C) :
    eLpNorm (boundaryTrace (n := n) (M := M) u) p
        (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
      boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
        ENNReal.ofReal C :=
  boundaryRestrict_eLpNorm_le_of_bound (n := n) (M := M) g p hC

omit [IsManifold (𝓡∂ n) ∞ M] in
theorem boundaryTrace_eq_restrict_of_contMDiff
    {u : M → ℝ}
    (hu : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ∞ u) :
    boundaryTrace (n := n) (M := M) u =
      fun x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        u (x : M) :=
  boundaryTrace_eq_restrict_of_continuous (n := n) (M := M) hu.continuous

theorem boundaryTrace_memLp_of_contMDiff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ}
    (hu : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ∞ u) :
    MemLp (boundaryTrace (n := n) (M := M) u) p
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  boundaryTrace_memLp_of_continuous (n := n) (M := M) g p hu.continuous

theorem boundaryTrace_eLpNorm_le_of_contMDiff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ}
    (hu : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ∞ u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (boundaryTrace (n := n) (M := M) u) p
          (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
        boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
          ENNReal.ofReal C :=
  boundaryTrace_eLpNorm_le_of_continuous (n := n) (M := M) g p hu.continuous

@[reducible]
def boundaryHyperplaneEuclid : Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane (d := n)

@[reducible]
def closedHalfSpaceEuclid : Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace (d := n)

@[reducible]
def openHalfSpaceEuclid : Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace (d := n)

@[reducible]
def interiorHalfSpaceEuclid (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
    (d := n) Ω

theorem zero_on_boundary_of_tsupport_subset_openHalfSpace
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp : tsupport u ⊆ openHalfSpaceEuclid (n := n))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ boundaryHyperplaneEuclid (n := n)) :
    u y = 0 := by
  have h_y_not_in_open :
      y ∉ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace
            (d := n) := by
    intro h_in
    have h_zero : y 0 = 0 := hy
    have h_pos : (0 : ℝ) < y 0 := h_in
    rw [h_zero] at h_pos
    exact lt_irrefl _ h_pos
  have h_y_not_in_supp : y ∉ tsupport u := fun hy_supp =>
    h_y_not_in_open (h_supp hy_supp)
  exact image_eq_zero_of_notMem_tsupport h_y_not_in_supp

theorem zero_on_boundaryHyperplane_of_tsupport_subset_interiorHalfSpace
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ interiorHalfSpaceEuclid (n := n) Ω)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ boundaryHyperplaneEuclid (n := n)) :
    u y = 0 := by
  have h_supp' :
      tsupport u ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace
          (d := n) := by
    intro x hx
    have h_in :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset_openHalfSpace
        (d := n) Ω (h_supp hx)
    exact h_in
  exact zero_on_boundary_of_tsupport_subset_openHalfSpace
    (n := n) (u := u) h_supp' hy

theorem trace_via_inclEuclidean_eq_zero_of_tsupport_subset_openHalfSpace
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ openHalfSpaceEuclid (n := n))
    (x' : EuclideanSpace ℝ (Fin (n - 1))) :
    u
        (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
          n x') =
      0 := by
  refine zero_on_boundary_of_tsupport_subset_openHalfSpace
    (n := n) h_supp ?_
  change
    (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
        n x') 0 = 0
  exact
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean_zero_coord
      n x'

theorem trace_via_inclEuclidean_eq_zero_of_tsupport_subset_interiorHalfSpace
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ interiorHalfSpaceEuclid (n := n) Ω)
    (x' : EuclideanSpace ℝ (Fin (n - 1))) :
    u
        (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
          n x') =
      0 := by
  refine zero_on_boundaryHyperplane_of_tsupport_subset_interiorHalfSpace
    (n := n) (Ω := Ω) (u := u) h_supp ?_
  change
    (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
        n x') 0 = 0
  exact
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean_zero_coord
      n x'

theorem eLpNorm_trace_eq_zero_of_tsupport_subset_openHalfSpace
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ openHalfSpaceEuclid (n := n))
    (p : ℝ≥0∞)
    (μ : Measure (EuclideanSpace ℝ (Fin (n - 1)))) :
    eLpNorm
        (fun x' : EuclideanSpace ℝ (Fin (n - 1)) =>
          u
            (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
              n x'))
        p μ = 0 := by
  have h_zero :
      (fun x' : EuclideanSpace ℝ (Fin (n - 1)) =>
        u
          (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
            n x')) =
      (fun _ : EuclideanSpace ℝ (Fin (n - 1)) => (0 : ℝ)) := by
    funext x'
    exact trace_via_inclEuclidean_eq_zero_of_tsupport_subset_openHalfSpace
      (n := n) h_supp x'
  rw [h_zero]
  exact eLpNorm_zero

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
