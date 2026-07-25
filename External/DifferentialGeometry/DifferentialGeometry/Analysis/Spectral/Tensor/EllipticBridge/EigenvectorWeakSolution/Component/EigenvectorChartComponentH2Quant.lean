import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorVariationalIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.TensorNonSmoothDiffQuotQuant

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
theorem eigenvector_chartComponent_h2_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ι : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
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
      ∀ (i k : Fin (Module.finrank ℝ E)),
        ∃ g_ik : EuclN → ℝ,
          MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            ((eigenvectorTensorChartBilinearData (I := I) (M := M)
              g r s ι α P₀).weak_partial i) Ω'' ∧
          eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (eLpNorm ((eigenvectorTensorChartBilinearData (I := I) (M := M)
                    g r s ι α P₀).weak_partial l) 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (eLpNorm (eigenvectorTensorChartBilinearData (I := I) (M := M)
                    g r s ι α P₀).u_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (eLpNorm (eigenvectorTensorChartBilinearData (I := I) (M := M)
                    g r s ι α P₀).f_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    tensor_h2_chart_loc_of_data_quantitative (I := I) (M := M) (g := g)
      (α := α) (r := r) (s := s) (P₀ := P₀)
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open
      hΩ''_compact_closure h_room
  exact ⟨C_geom, hC_geom_nn,
    fun i k => hC_geom
      (eigenvectorTensorChartBilinearData (I := I) (M := M)
        g r s ι α P₀) i k⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
