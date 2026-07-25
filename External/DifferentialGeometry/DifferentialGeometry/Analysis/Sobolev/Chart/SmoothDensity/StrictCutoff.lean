import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity


noncomputable section

open Set Topology Bundle Manifold Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

open DifferentialGeometry.Integral.Measure

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma isClosed_compl_chartAt_source_aux (α : M) :
    IsClosed ((chartAt H α).sourceᶜ) :=
  (chartAt H α).open_source.isClosed_compl

omit [CompactSpace M] [I.Boundaryless] in
private lemma isClosed_tsupport_chartAtlasPOU_aux (α : M) :
    IsClosed (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  isClosed_tsupport _

omit [CompactSpace M] [I.Boundaryless] in
private lemma tsupport_chartAtlasPOU_subset_aux (α : M) :
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

omit [CompactSpace M] [I.Boundaryless] in
private lemma disjoint_complSource_tsupport_chartAtlasPOU_aux (α : M) :
    Disjoint ((chartAt H α).sourceᶜ)
      (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  Set.disjoint_compl_left_iff_subset.mpr
    (tsupport_chartAtlasPOU_subset_aux (I := I) α)

private def chartStrictCutoffBundled (α : M) : C^∞⟮I, M; ℝ⟯ :=
  ((Classical.choose
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source_aux (M := M) α)
      (isClosed_tsupport_chartAtlasPOU_aux (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU_aux (I := I) α))) :
        C^∞⟮I, M; ℝ⟯)

omit [I.Boundaryless] in
private lemma chartStrictCutoffBundled_spec (α : M) :
    (∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) ∧
    (∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1) ∧
    ∀ x, ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈
        Set.Icc (0 : ℝ) 1 :=
  Classical.choose_spec
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source_aux (M := M) α)
      (isClosed_tsupport_chartAtlasPOU_aux (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU_aux (I := I) α))

def chartStrictCutoff (α : M) : M → ℝ :=
  ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)

omit [I.Boundaryless] in
private lemma chartStrictCutoff_eq_bundled (α : M) :
    chartStrictCutoff (I := I) α =
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  rfl

omit [I.Boundaryless] in
theorem chartStrictCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartStrictCutoff (I := I) α) :=
  (chartStrictCutoffBundled (I := I) α).contMDiff

omit [I.Boundaryless] in
theorem chartStrictCutoff_nonneg (α : M) (x : M) :
    0 ≤ chartStrictCutoff (I := I) α x :=
  ((chartStrictCutoffBundled_spec (I := I) α).2.2 x).1

omit [I.Boundaryless] in
theorem chartStrictCutoff_le_one (α : M) (x : M) :
    chartStrictCutoff (I := I) α x ≤ 1 :=
  ((chartStrictCutoffBundled_spec (I := I) α).2.2 x).2

omit [I.Boundaryless] in
theorem chartStrictCutoff_eventually_zero_nhdsSet_compl_source (α : M) :
    ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ), chartStrictCutoff (I := I) α x = 0 :=
  (chartStrictCutoffBundled_spec (I := I) α).1

omit [I.Boundaryless] in
theorem chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU (α : M) :
    ∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoffBundled_spec (I := I) α).2.1

omit [I.Boundaryless] in
theorem chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU (α : M) {x : M}
    (hx : x ∈ tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU
    (I := I) α).self_of_nhdsSet _ hx

omit [I.Boundaryless] in
theorem chartStrictCutoff_eq_zero_of_notMem_chartAt_source (α : M) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    chartStrictCutoff (I := I) α x = 0 := by
  have hmem : x ∈ ((chartAt H α).sourceᶜ) := hx
  exact (chartStrictCutoff_eventually_zero_nhdsSet_compl_source
    (I := I) α).self_of_nhdsSet _ hmem

omit [I.Boundaryless] in
theorem chartStrictCutoff_tsupport_subset (α : M) :
    tsupport (chartStrictCutoff (I := I) α) ⊆ (chartAt H α).source := by
  classical
  have hev : ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      chartStrictCutoff (I := I) α x = 0 :=
    chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) α
  rw [eventually_nhdsSet_iff_exists] at hev
  obtain ⟨U, hUopen, hUsub, hUzero⟩ := hev
  have hUcomp : IsClosed (Uᶜ) := hUopen.isClosed_compl
  have hsupp_sub : Function.support (chartStrictCutoff (I := I) α) ⊆ Uᶜ := by
    intro x hx
    by_contra hxU
    have hxU' : x ∈ U := by
      simpa using hxU
    exact hx (hUzero x hxU')
  have htsupp_sub : tsupport (chartStrictCutoff (I := I) α) ⊆ Uᶜ :=
    closure_minimal hsupp_sub hUcomp
  have hUcomp_sub : Uᶜ ⊆ (chartAt H α).source := by
    intro x hx
    by_contra hx_not
    have : x ∈ U := hUsub hx_not
    exact hx this
  exact htsupp_sub.trans hUcomp_sub

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
