import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

lemma chartCoeff_pullback
    (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M}
    (hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hβ : x ∈ (trivializationAt E (TangentSpace I) β).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    chartCoeff (I := I) α X k x =
      ∑ j, transitionMatrix (I := I) α β x k j *
        chartCoeff (I := I) β X j x := by
  classical
  have hβ_recompose := chartCoeff_recompose (I := I) β X hβ
  have hα_recompose := chartCoeff_recompose (I := I) α X hα
  have hbasis : ∀ j : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) β j x =
        ∑ k, transitionMatrix (I := I) α β x k j •
          chartBasisVecFiber (I := I) α k x :=
    fun j => chartBasisVecFiber_pullback (I := I) α β hα hβ j
  have hexpand :
      X x = ∑ k : Fin (Module.finrank ℝ E),
              (∑ j, transitionMatrix (I := I) α β x k j *
                chartCoeff (I := I) β X j x) •
                chartBasisVecFiber (I := I) α k x := by
    rw [hβ_recompose]
    simp_rw [hbasis]
    have hsmul_sum : ∀ j,
        chartCoeff (I := I) β X j x •
            ∑ k, transitionMatrix (I := I) α β x k j •
              chartBasisVecFiber (I := I) α k x =
          ∑ k, (transitionMatrix (I := I) α β x k j *
                  chartCoeff (I := I) β X j x) •
            chartBasisVecFiber (I := I) α k x := by
      intro j
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [smul_smul, mul_comm]
    simp_rw [hsmul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_smul]
  have hli := chartBasisFamily_linearIndependent (I := I) α hα
  rw [Fintype.linearIndependent_iff] at hli
  set f : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    chartCoeff (I := I) α X k x -
      ∑ j, transitionMatrix (I := I) α β x k j *
        chartCoeff (I := I) β X j x
  have hf : ∑ k, f k • chartBasisVecFiber (I := I) α k x = 0 := by
    simp only [f, sub_smul]
    rw [Finset.sum_sub_distrib]
    rw [← hα_recompose, ← hexpand, sub_self]
  have hf0 : f = 0 := funext (hli f hf)
  have := congrFun hf0 k
  simp only [f, Pi.zero_apply, sub_eq_zero] at this
  exact this

end DivergenceTheorem
end Integral
end DifferentialGeometry
