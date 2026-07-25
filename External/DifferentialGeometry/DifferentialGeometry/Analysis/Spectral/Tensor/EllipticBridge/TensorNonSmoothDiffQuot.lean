import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.TensorChartBilinearData
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor_h2_chart_loc_of_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ M_bound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) := by
  classical
  exact exists_weak_second_partial_of_uniform_diffQuot_bound (I := I) (M := M)
    (g := g) (α := α) D.toChartData
    hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd

section ElaborationTests

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ M_bound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k))
    (i k : Fin (Module.finrank ℝ E)) :
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) :=
  tensor_h2_chart_loc_of_uniform_bound D hΩ''_open hΩ''_compact_closure hh₀
    h_room hM_nn h_uniform_bd i k

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
