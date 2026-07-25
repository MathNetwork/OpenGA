import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.H2FromSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainH2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2FromSmooth
open DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem chartH2_localBound_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ 1 →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room :
      Metric.cthickening (1 : ℝ) (closure Ω'') ⊆
        chartTargetEuclid (I := I) (M := M) α) :
    ∃ (M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∀ i k, 0 ≤ M_bound i k) ∧
      (∀ i k : Fin (Module.finrank ℝ E),
        ∃ g_ik : EuclN → ℝ,
          MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            ((chartBilinearH1ComplData_of_laplacianDomain
              (I := I) (M := M) g α hu_h).weak_partial i) Ω'' ∧
          eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (M_bound i k)) := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain
    (I := I) (M := M) g α hu_h with hD_def
  obtain ⟨M_bound, hM_nn, h_uniform_bd⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data
      (I := I) (M := M) (g := g) (α := α) D
      hη hη_supp hη_range hN h_fderiv_eta
      hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' (R₀ := 1) one_pos hh_supp_in_Ω'
      hη_one_on_Ω'' hΩ''_open.measurableSet
  have hh₀ : (0 : ℝ) < 1 := by norm_num
  have h_h2 :=
    exists_weak_second_partial_of_uniform_diffQuot_bound
      (I := I) (M := M) (g := g) (α := α) D
      hΩ''_open hΩ''_compact_closure hh₀ h_room
      hM_nn h_uniform_bd
  exact ⟨M_bound, hM_nn, h_h2⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_memWkpChart_two_chartBilinearRoute
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ :=
  laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness

end LaplacianDomainH2
end Laplacian
end Analysis
end DifferentialGeometry
