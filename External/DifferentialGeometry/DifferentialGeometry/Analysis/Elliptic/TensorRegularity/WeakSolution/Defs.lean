import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartWeakIdentity


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

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

noncomputable def tensorComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ =
      chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorComponentEuclid_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y =
      tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [tensorComponentEuclid_def]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorComponentEuclid_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y = 0 := by
  rw [tensorComponentEuclid_def]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s T α P₀.1 P₀.2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_eq_zero_of_section_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {x : M} (hx : T.toSection x = 0) :
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x = 0 := by
  classical
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [hx, map_zero, map_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) ⊆
      tsupport T.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  have hzero : T.toFun x = 0 := image_eq_zero_of_notMem_tsupport hx_notsupp
  have hsec : T.toSection x = 0 := by
    have hmod : TensorRSSpace.toModel (T.toSection x) = 0 := hzero
    have := (tensorRSSpace_continuousLinearEquiv (I := I) r s x).injective
      (a₁ := T.toSection x) (a₂ := 0)
    apply this
    rw [show (tensorRSSpace_continuousLinearEquiv (I := I) r s x) (T.toSection x) =
        TensorRSSpace.toModel (T.toSection x) from rfl, hmod, map_zero]
  exact hx (tensorChartComponentRaw_eq_zero_of_section_eq_zero
    (I := I) (M := M) g r s T α Idx Jdx hsec)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_tsupport_subset_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    tsupport (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) ⊆
      (chartAt H α).source :=
  (tensorChartComponentRaw_tsupport_subset (I := I) (M := M) g r s T α Idx Jdx).trans
    hT_supp

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hraw_supp : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_supp
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact ((tensorComponentEuclid_contDiffOn (I := I) (M := M)
      g r s T α P₀).contDiffWithinAt hy).contDiffAt (hopen.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hK_target h)
    have hKc_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    refine (contDiff_const (c := (0 : ℝ))).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hKc_open.mem_nhds hyK] with z hz
    by_cases hzT : z ∈ chartTargetEuclid (I := I) (M := M) α
    · exact chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hzT hz
    · exact tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hzT

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hraw_supp : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_supp
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hsupp : Function.support
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyK
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hyT hyK)
    · exact hy (tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hyT)
  exact (closure_minimal hsupp hK_compact.isClosed).trans hK_target

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hraw_supp : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_supp
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hsupp : Function.support
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyK
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hyT hyK)
    · exact hy (tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hyT)
  exact HasCompactSupport.of_support_subset_isCompact hK_compact hsupp

omit [CompleteSpace E] in
theorem tensorComponent_isSmoothWeakSolution_of_chartIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (f : EuclN → ℝ)
    (hbilin :
      ∀ φ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (Set.univ : Set EuclN) →
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
          ∫ y in (Set.univ : Set EuclN), f y * φ y) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) f := by
  classical
  refine ⟨tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp, ?_⟩
  intro φ hφ hφ_cs hφ_supp
  exact hbilin φ hφ hφ_cs hφ_supp

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
