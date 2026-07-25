import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartH2NonSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_weak_second_partial_bound_by_geometric_constant
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_open : IsOpen Ω'') (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ C_geom i k) ∧
      ∀ (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
        (i k : Fin (Module.finrank ℝ E)),
        ∃ g_ik : EuclN → ℝ,
          MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            (D.weak_partial i) Ω'' ∧
          eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (eLpNorm (D.weak_partial l) 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (eLpNorm D.u_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (eLpNorm D.f_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data_quantitative
      (I := I) (M := M) (E := E) (H := H) (g := g) (α := α)
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  refine ⟨C_geom, hC_geom_nn, fun D i k => ?_⟩
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    exists_weak_second_partial_of_uniform_diffQuot_bound (I := I) (M := M) (g := g) (α := α)
      D hΩ''_open hΩ''_compact_closure hR₀_pos h_room
      (M_bound := fun i k => C_geom i k * Real.sqrt (
        (∑ l : Fin (Module.finrank ℝ E),
          (eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        + (eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
        + (eLpNorm D.f_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2))
      (hM_nn := fun i k => mul_nonneg (hC_geom_nn i k) (Real.sqrt_nonneg _))
      (h_uniform_bd := fun i k h hpos hle => hC_geom D hpos hle)
      i k
  exact ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩

end ChartH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
