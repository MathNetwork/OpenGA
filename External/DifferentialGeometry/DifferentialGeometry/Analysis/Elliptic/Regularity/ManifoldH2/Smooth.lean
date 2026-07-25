import DifferentialGeometry.Analysis.Elliptic.Operator.ChartLocalLaplacian
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ManifoldH2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
theorem loc_chart_pulled
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {w F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution w F)
    (hF_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp F 2 ((volume : Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g : EuclN → ℝ,
      MemLp g 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g
        (fun y : EuclN => (fderiv ℝ w y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ w x) (EuclideanSpace.single j 1))^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (w x)^2 ∂(volume : Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(volume : Measure EuclN)) := by
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  have h_closure_in :
      closure Ω'' ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  obtain ⟨C, hC_nn, h_eng⟩ := loc_smooth_solution
    (d := Module.finrank ℝ E)
    B hΩ'' hΩ''_compact_closure h_closure_in h_room
  intro i k
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hF_l2_loc i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

omit [NeZero (Module.finrank ℝ E)] in

omit [FiniteDimensional ℝ E] in
theorem memLp_two_continuous_compactSupport_restrict
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((volume : Measure EuclN).restrict Ω') := by
  have h_global : MemLp f 2 (volume : Measure EuclN) :=
    hf_cont.memLp_of_hasCompactSupport (μ := volume) (p := 2) hf_cs
  exact h_global.restrict _

theorem loc_chart_pulled_manifold
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_cs : HasCompactSupport u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution
      (chartPullback (I := I) α u) F)
    (hF_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp F 2 ((volume : Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN => (fderiv ℝ (chartPullback (I := I) α u) y)
          (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ (chartPullback (I := I) α u) x)
                      (EuclideanSpace.single j 1))^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (chartPullback (I := I) α u x)^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(volume : Measure EuclN)) := by
  let _ := g
  let _ := hu_smooth
  let _ := hu_cs
  let _ := hu_supp
  exact loc_chart_pulled (E := E)
    B h_weak hF_l2_loc hΩ'' hΩ''_compact_closure

end ManifoldH2
end Laplacian
end Analysis
end DifferentialGeometry
