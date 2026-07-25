import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSymbolFormula


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

section GramBridge

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_extChartAt_self (g : SmoothRiemannianMetric I M) (x : M)
    (k j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g x k j (extChartAt I x x) =
      chartGramMatrix (I := I) g x x k j := by
  rw [chartGramOnE_def, extChartAt_to_inv]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma sum_chartGram_mul_chartInvGram_self (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    ∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l =
      (if l = j then (1 : ℝ) else 0) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx
  have hentry : (chartInvGramMatrix (I := I) g x x *
      chartGramMatrix (I := I) g x x) l j = (1 : Matrix _ _ ℝ) l j := by
    rw [hmul]
  rw [Matrix.one_apply, Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartInvGramMatrix_self_symm (I := I) g x l k]
  ring

end GramBridge

section SymbolComponent


def deTurckCorrSymbolComp (g _g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                ((chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ a *
                    formComp (I := I) x t l b +
                  (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ b *
                    formComp (I := I) x t l a -
                  (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ l *
                    formComp (I := I) x t a b))) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x i k (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                    formComp (I := I) x t l b +
                  (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                    formComp (I := I) x t l a -
                  (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                    formComp (I := I) x t a b)))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckCorrSymbolComp_def (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ t i j =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k j (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x i k (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := rfl

end SymbolComponent

section ClosedForm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma block_term_a (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
            formComp (I := I) x t m b) =
      (chartModelBasis E).repr ξ d *
        raisedFormContractionSnd (I := I) g x ξ t m := by
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
              formComp (I := I) x t m b)
      = ∑ b : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ d *
            (raisedCovectorComp (I := I) g x ξ b * formComp (I := I) x t m b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x a b]
        ring
    _ = (chartModelBasis E).repr ξ d *
          raisedFormContractionSnd (I := I) g x ξ t m := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma block_term_b (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
            formComp (I := I) x t m a) =
      (chartModelBasis E).repr ξ d *
        raisedFormContractionSnd (I := I) g x ξ t m := by
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
              formComp (I := I) x t m a)
      = ∑ a : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ d *
            (raisedCovectorComp (I := I) g x ξ a * formComp (I := I) x t m a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (chartModelBasis E).repr ξ d *
          raisedFormContractionSnd (I := I) g x ξ t m := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma block_term_trace (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
            formComp (I := I) x t a b) =
      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
        formMetricTrace (I := I) g x t := by
  rw [formMetricTrace_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma deTurckCorr_block_contraction (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x k m *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b)) =
      (chartModelBasis E).repr ξ d *
            raisedFormContractionSnd (I := I) g x ξ t m -
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
          formMetricTrace (I := I) g x t) := by
  have hstage1 : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            (chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b))) =
        chartInvGramMatrix (I := I) g x x a b *
          ((1 / 2 : ℝ) *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                formComp (I := I) x t m b +
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                formComp (I := I) x t m a -
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                formComp (I := I) x t a b)) := by
    intro a b
    set P : Fin (Module.finrank ℝ E) → ℝ := fun l =>
      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
          formComp (I := I) x t l b +
        (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
          formComp (I := I) x t l a -
        (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
          formComp (I := I) x t a b with hP
    calc
      ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l * P l))
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g x x k l * P l))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g x x k l * P l))) :=
          Finset.sum_comm
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (if l = m then (1 : ℝ) else 0) *
              (chartInvGramMatrix (I := I) g x x a b * ((1 / 2 : ℝ) * P l)) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← sum_chartGram_mul_chartInvGram_self (I := I) g x m l, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ = chartInvGramMatrix (I := I) g x x a b * ((1 / 2 : ℝ) * P m) := by
          rw [Finset.sum_eq_single m]
          · rw [if_pos rfl, one_mul]
          · intro l _ hl
            rw [if_neg hl, zero_mul]
          · intro hm
            exact absurd (Finset.mem_univ m) hm
  have reorder :
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := by
    have hrow : (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
    rw [hrow, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  rw [reorder]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            (chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b)))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((1 / 2 : ℝ) *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                formComp (I := I) x t m b +
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                formComp (I := I) x t m a -
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                formComp (I := I) x t a b)) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hstage1 a b]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((1 / 2 : ℝ) *
              ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b +
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                  formComp (I := I) x t m a -
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                  formComp (I := I) x t a b))
      = (1 / 2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x a b *
              ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b +
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                  formComp (I := I) x t m a -
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                  formComp (I := I) x t a b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (1 / 2 : ℝ) *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x a b *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                    formComp (I := I) x t m a)) -
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x a b *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                    formComp (I := I) x t a b))) := by
        refine congrArg _ ?_
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (chartModelBasis E).repr ξ d *
            raisedFormContractionSnd (I := I) g x ξ t m -
          (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
            formMetricTrace (I := I) g x t) := by
        rw [block_term_a (I := I) g x ξ t d m, block_term_b (I := I) g x ξ t d m,
          block_term_trace (I := I) g x ξ t d m]
        ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrSymbolComp_eq_closedForm (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ t i j =
      (chartModelBasis E).repr ξ i *
          raisedFormContractionSnd (I := I) g x ξ t j +
        (chartModelBasis E).repr ξ j *
          raisedFormContractionSnd (I := I) g x ξ t i -
        (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ j *
          formMetricTrace (I := I) g x t := by
  have hgram : ∀ k j' : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j' (extChartAt I x x) =
        chartGramMatrix (I := I) g x x k j' :=
    fun k j' => chartGramOnE_extChartAt_self (I := I) g x k j'
  have hinv : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x a b (extChartAt I x x) =
        chartInvGramMatrix (I := I) g x x a b :=
    fun a b => chartInvGramOnE_extChartAt_self (I := I) g x a b
  have hksum : ∀ d m : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k m (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        (chartModelBasis E).repr ξ d *
              raisedFormContractionSnd (I := I) g x ξ t m -
          (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
            formMetricTrace (I := I) g x t) := by
    intro d m
    rw [← deTurckCorr_block_contraction (I := I) g x ξ t d m]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram k m]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hinv a b]
    refine congrArg _ ?_
    refine congrArg _ ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hinv k l]
  have hsecond :
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x i k (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k i (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x i k]
  rw [deTurckCorrSymbolComp_def, hsecond, hksum i j, hksum j i]
  ring

end ClosedForm

section Linearity

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrSymbolComp_add (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ (t + t') i j =
      deTurckCorrSymbolComp (I := I) g g' x ξ t i j +
        deTurckCorrSymbolComp (I := I) g g' x ξ t' i j := by
  rw [deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ (t + t') i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t' i j,
    raisedFormContractionSnd_add, raisedFormContractionSnd_add, formMetricTrace_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrSymbolComp_smul (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ (a • t) i j =
      a * deTurckCorrSymbolComp (I := I) g g' x ξ t i j := by
  rw [deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ (a • t) i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t i j,
    raisedFormContractionSnd_smul, raisedFormContractionSnd_smul, formMetricTrace_smul]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem deTurckCorrSymbolComp_zero (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i j = 0 := by
  rw [deTurckCorrSymbolComp_eq_closedForm, raisedFormContractionSnd_zero,
    raisedFormContractionSnd_zero, formMetricTrace_zero]
  ring

end Linearity

section Symmetry

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrSymbolComp_symm (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ t i j =
      deTurckCorrSymbolComp (I := I) g g' x ξ t j i := by
  rw [deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t j i]
  ring

end Symmetry

section BackgroundIndependence

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrSymbolComp_background_independent
    (g g'₁ g'₂ : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g'₁ x ξ t i j =
      deTurckCorrSymbolComp (I := I) g g'₂ x ξ t i j := by
  rw [deTurckCorrSymbolComp_def, deTurckCorrSymbolComp_def]

end BackgroundIndependence

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
