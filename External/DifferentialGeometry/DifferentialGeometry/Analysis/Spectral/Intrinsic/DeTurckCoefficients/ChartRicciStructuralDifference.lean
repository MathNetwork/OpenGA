import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RicciDiffAffine
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem invGramOnE_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y =
      ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₁ α k p y *
          (chartGramOnE (I := I) g₂ α p q y - chartGramOnE (I := I) g₁ α p q y) *
          chartInvGramOnE (I := I) g₂ α q l y := by
  classical
  set x : M := (extChartAt I α).symm y with hx_def
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_mem_baseSet_of_mem_interior_target (I := I) α hy
  have hA_unit : IsUnit (chartGramMatrix (I := I) g₁ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g₁ α hx_base))
  have hB_unit : IsUnit (chartGramMatrix (I := I) g₂ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g₂ α hx_base))
  have hAB : IsUnit (chartGramMatrix (I := I) g₁ α x) ↔
      IsUnit (chartGramMatrix (I := I) g₂ α x) := ⟨fun _ => hB_unit, fun _ => hA_unit⟩
  have h_id : (chartGramMatrix (I := I) g₁ α x)⁻¹ - (chartGramMatrix (I := I) g₂ α x)⁻¹ =
      (chartGramMatrix (I := I) g₁ α x)⁻¹ *
        (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) *
        (chartGramMatrix (I := I) g₂ α x)⁻¹ := Matrix.inv_sub_inv hAB
  have h_entry :
      (chartGramMatrix (I := I) g₁ α x)⁻¹ k l - (chartGramMatrix (I := I) g₂ α x)⁻¹ k l =
        ((chartGramMatrix (I := I) g₁ α x)⁻¹ *
          (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) *
          (chartGramMatrix (I := I) g₂ α x)⁻¹) k l := by
    have := congrArg (fun X : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
      X k l) h_id
    simpa using this
  have h_expand :
      ((chartGramMatrix (I := I) g₁ α x)⁻¹ *
          (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) *
          (chartGramMatrix (I := I) g₂ α x)⁻¹) k l =
        ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartGramMatrix (I := I) g₁ α x)⁻¹ k p *
            (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) p q *
            (chartGramMatrix (I := I) g₂ α x)⁻¹ q l := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
  have hkey :
      chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y =
        ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartGramMatrix (I := I) g₁ α x)⁻¹ k p *
            (chartGramMatrix (I := I) g₂ α x - chartGramMatrix (I := I) g₁ α x) p q *
            (chartGramMatrix (I := I) g₂ α x)⁻¹ q l := by
    rw [show chartInvGramOnE (I := I) g₁ α k l y = (chartGramMatrix (I := I) g₁ α x)⁻¹ k l from rfl,
      show chartInvGramOnE (I := I) g₂ α k l y = (chartGramMatrix (I := I) g₂ α x)⁻¹ k l from rfl,
      h_entry, h_expand]
  rw [hkey]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show chartInvGramOnE (I := I) g₁ α k p y = (chartGramMatrix (I := I) g₁ α x)⁻¹ k p from rfl,
    show chartInvGramOnE (I := I) g₂ α q l y = (chartGramMatrix (I := I) g₂ α x)⁻¹ q l from rfl,
    show chartGramOnE (I := I) g₂ α p q y = chartGramMatrix (I := I) g₂ α x p q from rfl,
    show chartGramOnE (I := I) g₁ α p q y = chartGramMatrix (I := I) g₁ α x p q from rfl,
    Matrix.sub_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem gramBracket_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) :
    gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y =
      (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j) y -
          partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y) +
        (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i) y -
          partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y) -
        (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y) := by
  unfold gramBracket
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem gramBracketDeriv_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) (y : E) :
    gramBracketDeriv (I := I) g₁ α m i j l y - gramBracketDeriv (I := I) g₂ α m i j l y =
      (partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j)) y) +
        (partialDeriv (E := E) m (partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i)) y) -
        (partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j)) y) := by
  unfold gramBracketDeriv
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g₁ α i j k y - chartChristoffel (I := I) g₂ α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
            gramBracket (I := I) g₁ α i j l y +
          chartInvGramOnE (I := I) g₂ α k l y *
            (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y)) := by
  classical
  rw [chartChristoffel_eq_sum_invGramOnE_bracket, chartChristoffel_eq_sum_invGramOnE_bracket,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartChristoffel_sub_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
        partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y) *
            gramBracket (I := I) g₁ α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
            (gramBracket (I := I) g₁ α i j l y - gramBracket (I := I) g₂ α i j l y) +
          ((chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
              gramBracketDeriv (I := I) g₁ α m i j l y +
            chartInvGramOnE (I := I) g₂ α k l y *
              (gramBracketDeriv (I := I) g₁ α m i j l y -
                gramBracketDeriv (I := I) g₂ α m i j l y))) := by
  classical
  rw [partialDeriv_chartChristoffel_eq (I := I) g₁ α m i j k hy,
    partialDeriv_chartChristoffel_eq (I := I) g₂ α m i j k hy,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderTerm_sub_eq_christoffelDerivDiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderTerm (I := I) g₁ α i k y -
        chartRicciSecondOrderTerm (I := I) g₂ α i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
              partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
          (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y)) := by
  classical
  rw [chartRicciSecondOrderTerm, chartRicciSecondOrderTerm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciFirstOrderTerm_sub_eq_christoffelDiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderTerm (I := I) g₁ α i k y -
        chartRicciFirstOrderTerm (I := I) g₂ α i k y =
      ∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        (((chartChristoffel (I := I) g₁ α j m j y -
                chartChristoffel (I := I) g₂ α j m j y) *
              chartChristoffel (I := I) g₁ α i k m y +
            chartChristoffel (I := I) g₂ α j m j y *
              (chartChristoffel (I := I) g₁ α i k m y -
                chartChristoffel (I := I) g₂ α i k m y)) -
          ((chartChristoffel (I := I) g₁ α k m j y -
                chartChristoffel (I := I) g₂ α k m j y) *
              chartChristoffel (I := I) g₁ α i j m y +
            chartChristoffel (I := I) g₂ α k m j y *
              (chartChristoffel (I := I) g₁ α i j m y -
                chartChristoffel (I := I) g₂ α i j m y))) := by
  classical
  rw [chartRicciFirstOrderTerm, chartRicciFirstOrderTerm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_sub_eq_christoffelDiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y =
      (∑ j : Fin (Module.finrank ℝ E),
          ((partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
                partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
            (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
              partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y))) +
        (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (((chartChristoffel (I := I) g₁ α j m j y -
                  chartChristoffel (I := I) g₂ α j m j y) *
                chartChristoffel (I := I) g₁ α i k m y +
              chartChristoffel (I := I) g₂ α j m j y *
                (chartChristoffel (I := I) g₁ α i k m y -
                  chartChristoffel (I := I) g₂ α i k m y)) -
            ((chartChristoffel (I := I) g₁ α k m j y -
                  chartChristoffel (I := I) g₂ α k m j y) *
                chartChristoffel (I := I) g₁ α i j m y +
              chartChristoffel (I := I) g₂ α k m j y *
                (chartChristoffel (I := I) g₁ α i j m y -
                  chartChristoffel (I := I) g₂ α i j m y)))) := by
  rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₁ α i k y,
    chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) g₂ α i k y]
  rw [show chartRicciSecondOrderTerm (I := I) g₁ α i k y +
            chartRicciFirstOrderTerm (I := I) g₁ α i k y -
          (chartRicciSecondOrderTerm (I := I) g₂ α i k y +
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) =
        (chartRicciSecondOrderTerm (I := I) g₁ α i k y -
            chartRicciSecondOrderTerm (I := I) g₂ α i k y) +
          (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
            chartRicciFirstOrderTerm (I := I) g₂ α i k y) from by ring]
  rw [chartRicciSecondOrderTerm_sub_eq_christoffelDerivDiff (I := I) g₁ g₂ α i k y,
    chartRicciFirstOrderTerm_sub_eq_christoffelDiff (I := I) g₁ g₂ α i k y]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
