import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Regular

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartAtlasPOU_exists_thickening_cutoff
    [T2Space M] [SigmaCompactSpace M]
    (α : M) :
    ∃ χ : C^∞⟮I, M; ℝ⟯,
      (∀ x : M, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ tsupport (chartAtlasPOU I M α : M → ℝ), χ x = 1) ∧
      tsupport (χ : M → ℝ) ⊆ (chartAt H α).source := by
  classical
  set s : Set M := tsupport (chartAtlasPOU I M α : M → ℝ) with hs_def
  set U : Set M := (chartAt H α).source with hU_def
  have hs_closed : IsClosed s := isClosed_tsupport _
  have hU_open : IsOpen U := (chartAt H α).open_source
  have hs_sub_U : s ⊆ U := chartAtlasPOU_isSubordinate (I := I) (M := M) α
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : ParacompactSpace M :=
    paracompact_of_locallyCompact_sigmaCompact (X := M)
  haveI : T4Space M := T4Space.of_paracompactSpace_t2Space (X := M)
  haveI : NormalSpace M := inferInstance
  obtain ⟨V, hV_open, hs_sub_V, hVcl_sub_U⟩ :=
    normal_exists_closure_subset (X := M) hs_closed hU_open hs_sub_U
  have hs_sub_int_V : s ⊆ interior V := by
    rw [hV_open.interior_eq]
    exact hs_sub_V
  obtain ⟨f, hf_one_nhds, hf_zero_outside, hf_Icc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (M := M) (n := ⊤) hs_closed hs_sub_int_V
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(hf_Icc x).1, (hf_Icc x).2⟩
  · intro x hx
    have hx_nhds : x ∈ s := hx
    exact hf_one_nhds.self_of_nhdsSet _ hx_nhds
  · have hsupp_f : Function.support (f : M → ℝ) ⊆ V := by
      intro x hx
      by_contra hxV
      have : f x = 0 := hf_zero_outside x hxV
      exact hx this
    have htsupp_f : tsupport (f : M → ℝ) ⊆ closure V := by
      have := closure_mono hsupp_f
      simpa [tsupport] using this
    exact htsupp_f.trans hVcl_sub_U

end Measure
end Integral
end DifferentialGeometry
