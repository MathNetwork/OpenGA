import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartMetric
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.Compact


noncomputable section

open Bundle Manifold Set Filter Topology
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
theorem chartImage_pouTsupport_isCompact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact ((extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  have h_tsupp_compact : IsCompact (tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (isClosed_tsupport _).isCompact
  have h_tsupp_sub_src :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have h_tsupp_sub_extSrc :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]
    exact h_tsupp_sub_src hx
  have h_cont :
      ContinuousOn (extChartAt I α : M → E)
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (continuousOn_extChartAt α).mono h_tsupp_sub_extSrc
  exact h_tsupp_compact.image_of_continuousOn h_cont

omit [NeZero (Module.finrank ℝ E)] in
theorem chartImage_pouTsupport_subset_target
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    (extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      (extChartAt I α).target := by
  classical
  rintro y ⟨x, hx, rfl⟩
  have h_tsupp_sub_src :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact h_tsupp_sub_src hx
  exact (extChartAt I α).map_source hx_src

omit [NeZero (Module.finrank ℝ E)] in
theorem chartImage_pouTsupport_subset_interior_target
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] (α : M) :
    (extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      interior ((extChartAt I α).target : Set E) := by
  have h_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target (I := I) α
  rw [h_open.interior_eq]
  exact chartImage_pouTsupport_subset_target (I := I) (M := M) α

theorem chartChristoffel_bdd_on_compact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K)
    (hK_sub_interior : K ⊆ interior ((extChartAt I α).target : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E,
      y ∈ K →
        ∀ i j k : Fin (Module.finrank ℝ E),
          |chartChristoffel (I := I) g α i j k y| ≤ C := by
  classical
  have h_cont :
      ∀ i j k : Fin (Module.finrank ℝ E),
        ContinuousOn (fun y : E => |chartChristoffel (I := I) g α i j k y|) K := by
    intro i j k
    have h_smooth :
        ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
          (interior ((extChartAt I α).target : Set E)) :=
      chartChristoffel_contDiffOn_interior (I := I) g α i j k
    have h_cont_int :
        ContinuousOn (chartChristoffel (I := I) g α i j k)
          (interior ((extChartAt I α).target : Set E)) :=
      h_smooth.continuousOn
    have h_cont_K :
        ContinuousOn (chartChristoffel (I := I) g α i j k) K :=
      h_cont_int.mono hK_sub_interior
    exact continuous_abs.continuousOn.comp h_cont_K (mapsTo_image _ _)
  have h_bound :
      ∀ i j k : Fin (Module.finrank ℝ E),
        ∃ Cijk : ℝ, 0 ≤ Cijk ∧
          ∀ y ∈ K, |chartChristoffel (I := I) g α i j k y| ≤ Cijk := by
    intro i j k
    by_cases hKne : K.Nonempty
    · obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
        hK_compact.exists_isMaxOn hKne (h_cont i j k)
      refine ⟨|chartChristoffel (I := I) g α i j k y₀|, abs_nonneg _, ?_⟩
      intro y hy
      exact hy₀_max hy
    · refine ⟨0, le_refl _, ?_⟩
      intro y hy
      exact absurd hy (by
        rw [Set.not_nonempty_iff_eq_empty] at hKne
        rw [hKne]
        exact Set.notMem_empty y)
  choose Cijk hCijk_nonneg hCijk_bd using h_bound
  set s : Finset (Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    Finset.univ with hs_def
  set C : ℝ :=
    s.sup' (by
      refine Finset.univ_nonempty_iff.mpr ?_
      have : Nonempty (Fin (Module.finrank ℝ E)) :=
        ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
      exact ⟨⟨this.some, this.some, this.some⟩⟩)
      (fun p => Cijk p.1 p.2.1 p.2.2) with hC_def
  refine ⟨C, ?_, ?_⟩
  · have hne : s.Nonempty := by
      refine Finset.univ_nonempty_iff.mpr ?_
      have : Nonempty (Fin (Module.finrank ℝ E)) :=
        ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
      exact ⟨⟨this.some, this.some, this.some⟩⟩
    obtain ⟨p₀, hp₀_mem⟩ := hne
    refine (hCijk_nonneg p₀.1 p₀.2.1 p₀.2.2).trans ?_
    exact Finset.le_sup' (fun p => Cijk p.1 p.2.1 p.2.2) hp₀_mem
  · intro y hy i j k
    refine (hCijk_bd i j k y hy).trans ?_
    have hp_mem : (i, j, k) ∈ s := Finset.mem_univ _
    exact Finset.le_sup' (fun p => Cijk p.1 p.2.1 p.2.2) hp_mem

theorem chartChristoffel_bdd_on_pou_tsupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E,
      y ∈ (extChartAt I α) ''
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) →
        ∀ i j k : Fin (Module.finrank ℝ E),
          |chartChristoffel (I := I) g α i j k y| ≤ C :=
  chartChristoffel_bdd_on_compact (I := I) (M := M) g α
    (chartImage_pouTsupport_isCompact (I := I) (M := M) α)
    (chartImage_pouTsupport_subset_interior_target (I := I) (M := M) α)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
