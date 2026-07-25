import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation









noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "D3Idx" =>
  Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)



def gramD3DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p : D3Idx,
    |partialDeriv (E := E) p.1
        (partialDeriv (E := E) p.2.1
          (partialDeriv (E := E) p.2.2.1
            (chartGramOnE (I := I) g₁ α p.2.2.2.1 p.2.2.2.2))) y -
      partialDeriv (E := E) p.1
        (partialDeriv (E := E) p.2.1
          (partialDeriv (E := E) p.2.2.1
            (chartGramOnE (I := I) g₂ α p.2.2.2.1 p.2.2.2.2))) y|

omit [NeZero (Module.finrank ℝ E)] in

theorem gramD3_sub_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (d c m a b : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) d
        (partialDeriv (E := E) c
          (partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b))) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) c
          (partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b))) y| ≤
      gramD3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  let p : D3Idx := (d, (c, (m, (a, b))))
  have h := Finset.single_le_sum
    (f := fun q : D3Idx =>
      |partialDeriv (E := E) q.1
          (partialDeriv (E := E) q.2.1
            (partialDeriv (E := E) q.2.2.1
              (chartGramOnE (I := I) g₁ α q.2.2.2.1 q.2.2.2.2))) y -
        partialDeriv (E := E) q.1
          (partialDeriv (E := E) q.2.1
            (partialDeriv (E := E) q.2.2.1
              (chartGramOnE (I := I) g₂ α q.2.2.2.1 q.2.2.2.2))) y|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  simpa only [gramD3DiffSup, p] using h

omit [NeZero (Module.finrank ℝ E)] in

theorem gramD3DiffSup_nonneg
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ gramD3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _



def metricJet3DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y +
    gramD3DiffSup (I := I) (M := M) g₁ g₂ α y

omit [NeZero (Module.finrank ℝ E)] in

theorem metricJet3_nonneg
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (chartMetricJet2DiffSup_nonneg _ _ _ _)
    (gramD3DiffSup_nonneg (I := I) (M := M) g₁ g₂ α y)

omit [NeZero (Module.finrank ℝ E)] in

theorem metricJet2_le_jet3
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (gramD3DiffSup_nonneg (I := I) (M := M) g₁ g₂ α y)

omit [NeZero (Module.finrank ℝ E)] in

theorem gramD3_le_jet3
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    gramD3DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (chartMetricJet2DiffSup_nonneg _ _ _ _)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
