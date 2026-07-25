import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.ChartVectorField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ChristoffelLinearization


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


def chartLinearizedDeTurckVFPrincipal (g _g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α a b y *
      chartLinearizedChristoffelPrincipal (I := I) g α h a b k y

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLinearizedDeTurckVFPrincipal_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedDeTurckVFPrincipal_background_indep
    (g g' g'' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y =
      chartLinearizedDeTurckVFPrincipal (I := I) g g'' α h k y := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem chartLinearizedDeTurckVFPrincipal_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α
      (0 : ChartMetricPerturbation E) k y = 0 := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) a b k y
        = ∑ _a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E),
            (0 : ℝ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [chartLinearizedChristoffelPrincipal_zero, mul_zero]
    _ = 0 := by simp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedDeTurckVFPrincipal_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y =
      chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y +
        chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def, chartLinearizedDeTurckVFPrincipal_def,
    chartLinearizedDeTurckVFPrincipal_def]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedDeTurckVFPrincipal_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y =
      c • chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def, chartLinearizedDeTurckVFPrincipal_def,
    smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_smul, smul_eq_mul]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedDeTurckVFPrincipal_contDiffOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k =
      fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := by
    funext y
    rw [chartLinearizedDeTurckVFPrincipal_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  · exact (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h a b k).mono
      interior_subset

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedDeTurckVFPrincipal_differentiableOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) :
    DifferentiableOn ℝ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k)
      (interior (extChartAt I α).target) :=
  (chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g g' α h k).differentiableOn
    (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedDeTurckVFPrincipal_differentiableAt_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k) y := by
  have hcd : ContDiffOn ℝ ∞ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k)
      (interior (extChartAt I α).target) :=
    chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g g' α h k
  exact (hcd.differentiableOn (by simp)).differentiableAt
    (isOpen_interior.mem_nhds hy)

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
