import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSymbol
import DifferentialGeometry.Geometry.Operator.HessianTrace


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartDeTurckVFComp (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α a b y *
      (chartChristoffel (I := I) g α a b k y -
        chartChristoffel (I := I) g' α a b k y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckVFComp_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g g' α k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g' α a b k y) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem chartDeTurckVFComp_self
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g g α k y = 0 := by
  classical
  rw [chartDeTurckVFComp_def]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g α a b k y)
        = ∑ a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E),
            (0 : ℝ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [sub_self, mul_zero]
    _ = 0 := by simp

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_contDiffOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : chartDeTurckVFComp (I := I) g g' α k =
      fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            (chartChristoffel (I := I) g α a b k y -
              chartChristoffel (I := I) g' α a b k y) := by
    funext y
    rw [chartDeTurckVFComp_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  · have hg : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α a b k
    have hg' : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g' α a b k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g' α a b k
    exact hg.sub hg'

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_differentiableOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentiableOn ℝ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) :=
  (chartDeTurckVFComp_contDiffOn_interior (I := I) g g' α k).differentiableOn
    (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_differentiableAt_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartDeTurckVFComp (I := I) g g' α k) y := by
  have hcd : ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) :=
    chartDeTurckVFComp_contDiffOn_interior (I := I) g g' α k
  exact (hcd.differentiableOn (by simp)).differentiableAt
    (isOpen_interior.mem_nhds hy)

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
