import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartRicciStructuralDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckVFComp_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g₁ g_bg α k y -
        chartDeTurckVFComp (I := I) g₂ g_bg α k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y) *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y) +
          chartInvGramOnE (I := I) g₂ α a b y *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g₂ α a b k y)) := by
  classical
  rw [chartDeTurckVFComp_def, chartDeTurckVFComp_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [BoundarylessManifold I M] in

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartDeTurckVFComp_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
        partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g₂ g_bg α k) y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α a b) y -
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y) *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y) +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α a b) y *
            (chartChristoffel (I := I) g₁ α a b k y -
              chartChristoffel (I := I) g₂ α a b k y) +
          ((chartInvGramOnE (I := I) g₁ α a b y - chartInvGramOnE (I := I) g₂ α a b y) *
              (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
                partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y) +
            chartInvGramOnE (I := I) g₂ α a b y *
              (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α a b k) y -
                partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α a b k) y))) := by
  classical
  rw [partialDeriv_chartDeTurckVFComp_eq (I := I) g₁ g_bg α m k hy,
    partialDeriv_chartDeTurckVFComp_eq (I := I) g₂ g_bg α m k hy,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in

theorem chartLieDeTurckCompAdvectionTerm_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g₁ g_bg α k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) -
      (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g₂ g_bg α k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartDeTurckVFComp (I := I) g₁ g_bg α k y -
              chartDeTurckVFComp (I := I) g₂ g_bg α k y) *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y +
          chartDeTurckVFComp (I := I) g₂ g_bg α k y *
            (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y -
              partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in

theorem chartLieDeTurckCompIDerivTerm_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ α k j y *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₂ α k j y *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartGramOnE (I := I) g₁ α k j y - chartGramOnE (I := I) g₂ α k j y) *
            partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
          chartGramOnE (I := I) g₂ α k j y *
            (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
              partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in

theorem chartLieDeTurckCompJDerivTerm_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ α i k y *
          partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₂ α i k y *
          partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartGramOnE (I := I) g₁ α i k y - chartGramOnE (I := I) g₂ α i k y) *
            partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
          chartGramOnE (I := I) g₂ α i k y *
            (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
              partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem chartLieDeTurckComp_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
        chartLieDeTurckComp (I := I) g₂ g_bg α i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          ((chartDeTurckVFComp (I := I) g₁ g_bg α k y -
                chartDeTurckVFComp (I := I) g₂ g_bg α k y) *
              partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y +
            chartDeTurckVFComp (I := I) g₂ g_bg α k y *
              (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y -
                partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y))) +
        (∑ k : Fin (Module.finrank ℝ E),
            ((chartGramOnE (I := I) g₁ α k j y - chartGramOnE (I := I) g₂ α k j y) *
                partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
              chartGramOnE (I := I) g₂ α k j y *
                (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) +
          (∑ k : Fin (Module.finrank ℝ E),
            ((chartGramOnE (I := I) g₁ α i k y - chartGramOnE (I := I) g₂ α i k y) *
                partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y +
              chartGramOnE (I := I) g₂ α i k y *
                (partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y -
                  partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) := by
  classical
  rw [chartLieDeTurckComp_def, chartLieDeTurckComp_def]
  rw [show ((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) +
            (∑ k, chartGramOnE (I := I) g₁ α k j y *
                partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) +
            (∑ k, chartGramOnE (I := I) g₁ α i k y *
                partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y)) -
          ((∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y) +
            (∑ k, chartGramOnE (I := I) g₂ α k j y *
                partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y) +
            (∑ k, chartGramOnE (I := I) g₂ α i k y *
                partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) =
        ((∑ k, chartDeTurckVFComp (I := I) g₁ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₁ α i j) y) -
            (∑ k, chartDeTurckVFComp (I := I) g₂ g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g₂ α i j) y)) +
          (((∑ k, chartGramOnE (I := I) g₁ α k j y *
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
              (∑ k, chartGramOnE (I := I) g₂ α k j y *
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α k) y)) +
            ((∑ k, chartGramOnE (I := I) g₁ α i k y *
                  partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₁ g_bg α k) y) -
              (∑ k, chartGramOnE (I := I) g₂ α i k y *
                  partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g₂ g_bg α k) y))) from by
        ring]
  rw [chartLieDeTurckCompAdvectionTerm_sub_eq (I := I) g₁ g₂ g_bg α i j y,
    chartLieDeTurckCompIDerivTerm_sub_eq (I := I) g₁ g₂ g_bg α i j y,
    chartLieDeTurckCompJDerivTerm_sub_eq (I := I) g₁ g₂ g_bg α i j y]
  ring

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
