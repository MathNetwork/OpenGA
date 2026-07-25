import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorNonSmoothRegularity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

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
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

private lemma memWkp_succ_of_chosenWeakPartial_memWkp
    {m : ℕ} {Ω : Set EuclN} {u : EuclN → ℝ}
    (h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω)
    (h_partials : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i u Ω) Ω) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2 u Ω := by
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
  exact ⟨h_w1p, h_partials⟩

omit [CompleteSpace E] in
theorem eigenvector_chartComponent_memWkp_two_k
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {k : ℕ} (hk : k ≤ 1) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' := by
  have h_two : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' :=
    eigenvector_chartComponent_memWkp g r s i α P₀
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_le : 2 * k ≤ 2 := by omega
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le h_le h_two

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

theorem tensorChartComponent_memWkp_succ_of_diffData
    {m : ℕ} {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    {u : EuclN → ℝ}
    (h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω'')
    {v : Fin (Module.finrank ℝ E) → EuclN → ℝ}
    (h_diff_ae : ∀ l : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        2 l u Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω''] v l)
    (h_diff_memWkp : ∀ l : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * m) 2 (v l) Ω'') :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * m + 1) 2 u Ω'' := by
  refine memWkp_succ_of_chosenWeakPartial_memWkp h_w1p (fun l => ?_)
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open (h_diff_ae l)).mpr
      (h_diff_memWkp l)

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {k : ℕ} (hk : k ≤ 1) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' :=
  eigenvector_chartComponent_memWkp_two_k g r s i α P₀
    hΩ''_open hΩ''_compact_closure hR₀_pos h_room hk

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
