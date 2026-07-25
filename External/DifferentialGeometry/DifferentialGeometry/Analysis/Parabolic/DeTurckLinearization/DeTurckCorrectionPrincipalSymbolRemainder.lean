import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSecondOrder


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


def chartDeTurckCorrHessBlock (g _g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α k l y *
      (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
       partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
       partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrHessBlock_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
           partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
           partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y) := rfl


def chartDeTurckCorrGramDerivBlock (g _g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
      (partialDeriv (E := E) a (h l b) y +
       partialDeriv (E := E) b (h l a) y -
       partialDeriv (E := E) l (h a b) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrGramDerivBlock_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (partialDeriv (E := E) a (h l b) y +
           partialDeriv (E := E) b (h l a) y -
           partialDeriv (E := E) l (h a b) y) := rfl

def chartDeTurckCorrPrincipalSymbolExpr (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrPrincipalSymbolExpr_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrPrincipalSymbolExpr_eq_explicit
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α k l y *
                    (partialDeriv (E := E) i (partialDeriv (E := E) a (h l b)) y +
                     partialDeriv (E := E) i (partialDeriv (E := E) b (h l a)) y -
                     partialDeriv (E := E) i (partialDeriv (E := E) l (h a b)) y))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α k l y *
                    (partialDeriv (E := E) j (partialDeriv (E := E) a (h l b)) y +
                     partialDeriv (E := E) j (partialDeriv (E := E) b (h l a)) y -
                     partialDeriv (E := E) j (partialDeriv (E := E) l (h a b)) y))) := by
  rw [chartDeTurckCorrPrincipalSymbolExpr_def]
  simp only [chartDeTurckCorrHessBlock_def]

def chartDeTurckCorrFirstOrderRemainder (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y))) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y)))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrFirstOrderRemainder_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                  chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                  chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y))) := rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
      ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y) +
       (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y)) := by
  classical
  rw [partialDeriv_chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k d hy]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y +
          chartInvGramOnE (I := I) g α a b y *
            partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h a b k d hy,
    chartDeTurckCorrGramDerivBlock_def, chartDeTurckCorrHessBlock_def]
  rw [show ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
              (partialDeriv (E := E) a (h l b) y +
               partialDeriv (E := E) b (h l a) y -
               partialDeriv (E := E) l (h a b) y) +
            chartInvGramOnE (I := I) g α k l y *
              (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
               partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
               partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y))) =
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
              (partialDeriv (E := E) a (h l b) y +
               partialDeriv (E := E) b (h l a) y -
               partialDeriv (E := E) l (h a b) y)) +
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
               partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
               partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y)) from by
    rw [Finset.sum_add_distrib, mul_add]]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j y =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y +
        chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    chartDeTurckCorrFirstOrderRemainder_def]
  have hexp : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y) +
         (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y)) :=
    fun d k => partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded
      (I := I) g g' α h k d hy
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hexp i k]
    ring
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hexp j k]
    ring
  rw [hsum1, hsum2]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
    [I.Boundaryless]
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j (extChartAt I α x) =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j (extChartAt I α x) +
        chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder
    (I := I) g g' α h i j hx_int

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrFirstOrderRemainder_eq_first_order_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) l (h a b) y)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) l (h a b) y)))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) l (h a b) y)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) l (h a b) y)))) := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartLinearizedChristoffelPrincipal_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartDeTurckCorrGramDerivBlock_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartLinearizedChristoffelPrincipal_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartDeTurckCorrGramDerivBlock_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring

section BlockLinearity

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_zero
    (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p
        (partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b)) y = 0 := by
  have hinner : partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b) =
      fun _ : E => (0 : ℝ) := by
    funext y'
    have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
    rw [hconst, partialDeriv_const]
  rw [hinner, partialDeriv_const]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_zero_apply
    (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p ((0 : ChartMetricPerturbation E) a b) y = 0 := by
  have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
  rw [hconst, partialDeriv_const]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((h₁ + h₂) a b)) y =
      partialDeriv (E := E) p (partialDeriv (E := E) q (h₁ a b)) y +
        partialDeriv (E := E) p (partialDeriv (E := E) q (h₂ a b)) y := by
  have hinner : partialDeriv (E := E) q ((h₁ + h₂) a b) =
      fun y' => partialDeriv (E := E) q (h₁ a b) y' +
        partialDeriv (E := E) q (h₂ a b) y' := by
    funext y'
    have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
    rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
          (h₁.differentiableAt a b y') (h₂.differentiableAt a b y')]
  rw [hinner, partialDeriv_add (E := E)
        (partialDeriv (E := E) q (h₁ a b)) (partialDeriv (E := E) q (h₂ a b))
        (partialDeriv_perturbation_differentiableAt h₁ q a b y)
        (partialDeriv_perturbation_differentiableAt h₂ q a b y)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p ((h₁ + h₂) a b) y =
      partialDeriv (E := E) p (h₁ a b) y + partialDeriv (E := E) p (h₂ a b) y := by
  have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
  rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
        (h₁.differentiableAt a b y) (h₂.differentiableAt a b y)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((c • h) a b)) y =
      c * partialDeriv (E := E) p (partialDeriv (E := E) q (h a b)) y := by
  have hinner : partialDeriv (E := E) q ((c • h) a b) =
      fun y' => c • partialDeriv (E := E) q (h a b) y' := by
    funext y'
    have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
    rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y')]
  rw [hinner, partialDeriv_const_smul (E := E) c
        (partialDeriv (E := E) q (h a b))
        (partialDeriv_perturbation_differentiableAt h q a b y), smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p ((c • h) a b) y =
      c * partialDeriv (E := E) p (h a b) y := by
  have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
  rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y),
    smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrHessBlock_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α
      (0 : ChartMetricPerturbation E) d a b k y = 0 := by
  classical
  rw [chartDeTurckCorrHessBlock_def]
  have hzero : (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) d
            (partialDeriv (E := E) a ((0 : ChartMetricPerturbation E) l b)) y +
         partialDeriv (E := E) d
            (partialDeriv (E := E) b ((0 : ChartMetricPerturbation E) l a)) y -
         partialDeriv (E := E) d
            (partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) a b)) y)) = 0 := by
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_zero d a l b y,
      partialDeriv_partialDeriv_zero d b l a y,
      partialDeriv_partialDeriv_zero d l a b y]
    ring
  rw [hzero, mul_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrHessBlock_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) d a b k y =
      chartDeTurckCorrHessBlock (I := I) g g' α h₁ d a b k y +
        chartDeTurckCorrHessBlock (I := I) g g' α h₂ d a b k y := by
  classical
  rw [chartDeTurckCorrHessBlock_def, chartDeTurckCorrHessBlock_def,
    chartDeTurckCorrHessBlock_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_partialDeriv_add_apply h₁ h₂ d a l b y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ d b l a y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ d l a b y]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrHessBlock_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α (c • h) d a b k y =
      c * chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y := by
  classical
  rw [chartDeTurckCorrHessBlock_def, chartDeTurckCorrHessBlock_def]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) d (partialDeriv (E := E) a ((c • h) l b)) y +
           partialDeriv (E := E) d (partialDeriv (E := E) b ((c • h) l a)) y -
           partialDeriv (E := E) d (partialDeriv (E := E) l ((c • h) a b)) y)) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
           partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
           partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_smul_apply c h d a l b y,
      partialDeriv_partialDeriv_smul_apply c h d b l a y,
      partialDeriv_partialDeriv_smul_apply c h d l a b y]
    ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrGramDerivBlock_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α
      (0 : ChartMetricPerturbation E) d a b k y = 0 := by
  classical
  rw [chartDeTurckCorrGramDerivBlock_def]
  have hzero : (∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
        (partialDeriv (E := E) a ((0 : ChartMetricPerturbation E) l b) y +
         partialDeriv (E := E) b ((0 : ChartMetricPerturbation E) l a) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) a b) y)) = 0 := by
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [partialDeriv_zero_apply a l b y, partialDeriv_zero_apply b l a y,
      partialDeriv_zero_apply l a b y]
    ring
  rw [hzero, mul_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrGramDerivBlock_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) d a b k y =
      chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ d a b k y +
        chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ d a b k y := by
  classical
  rw [chartDeTurckCorrGramDerivBlock_def, chartDeTurckCorrGramDerivBlock_def,
    chartDeTurckCorrGramDerivBlock_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_add_apply h₁ h₂ a l b y, partialDeriv_add_apply h₁ h₂ b l a y,
    partialDeriv_add_apply h₁ h₂ l a b y]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrGramDerivBlock_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) d a b k y =
      c * chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y := by
  classical
  rw [chartDeTurckCorrGramDerivBlock_def, chartDeTurckCorrGramDerivBlock_def]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (partialDeriv (E := E) a ((c • h) l b) y +
           partialDeriv (E := E) b ((c • h) l a) y -
           partialDeriv (E := E) l ((c • h) a b) y)) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (partialDeriv (E := E) a (h l b) y +
           partialDeriv (E := E) b (h l a) y -
           partialDeriv (E := E) l (h a b) y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_smul_apply c h a l b y, partialDeriv_smul_apply c h b l a y,
      partialDeriv_smul_apply c h l a b y]
    ring]
  ring

end BlockLinearity

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrPrincipalSymbolExpr_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def]
  have hzero : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α
              (0 : ChartMetricPerturbation E) d a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartDeTurckCorrHessBlock_zero, mul_zero]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hzero i k, mul_zero]),
    Finset.sum_eq_zero (fun k _ => by rw [hzero j k, mul_zero]), add_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrPrincipalSymbolExpr_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α (h₁ + h₂) i j y =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h₁ i j y +
        chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h₂ i j y := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    chartDeTurckCorrPrincipalSymbolExpr_def]
  have hsplit : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) d a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₁ d a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₂ d a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrHessBlock_add]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) i a b k y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₁ i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₂ i a b k y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsplit i k, mul_add]]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) j a b k y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₁ j a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₂ j a b k y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsplit j k, mul_add]]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrPrincipalSymbolExpr_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α (c • h) i j y =
      c • chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    smul_eq_mul]
  have hscale : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α (c • h) d a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrHessBlock_smul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (c • h) i a b k y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hscale i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (c • h) j a b k y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hscale j k]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrFirstOrderRemainder_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def]
  have hbranchA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α
              (0 : ChartMetricPerturbation E) a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_zero, mul_zero]
  have hbranchB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α
              (0 : ChartMetricPerturbation E) d a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartDeTurckCorrGramDerivBlock_zero, mul_zero]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hbranchA i k, hbranchB i k]; ring),
    Finset.sum_eq_zero (fun k _ => by rw [hbranchA j k, hbranchB j k]; ring), add_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrFirstOrderRemainder_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α (h₁ + h₂) i j y =
      chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h₁ i j y +
        chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h₂ i j y := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def, chartDeTurckCorrFirstOrderRemainder_def,
    chartDeTurckCorrFirstOrderRemainder_def]
  have hA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_add]
    ring
  have hB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) d a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ d a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ d a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrGramDerivBlock_add]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) i a b k y))) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ i a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ i a b k y))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA i k, hB i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) j a b k y))) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ j a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ j a b k y))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA j k, hB j k]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrFirstOrderRemainder_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α (c • h) i j y =
      c • chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def, chartDeTurckCorrFirstOrderRemainder_def,
    smul_eq_mul]
  have hA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_smul, smul_eq_mul]
    ring
  have hB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) d a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrGramDerivBlock_smul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) i a b k y))) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA i k, hB i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) j a b k y))) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA j k, hB j k]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrPrincipalSymbolExpr_symm
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h j i y := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def, chartDeTurckCorrPrincipalSymbolExpr_def]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g α i k y]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g α k j y]

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
