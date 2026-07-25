import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartTransition
import DifferentialGeometry.Analysis.Integration.Measure.Invariance



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartTransitionAtEntry (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) : ℝ :=
  (chartModelBasis E).repr
    (chartTransitionAt (I := I) α β x ((chartModelBasis E) a)) i

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
@[simp] lemma chartTransitionAtEntry_def (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) :
    chartTransitionAtEntry (I := I) α β x i a =
      (chartModelBasis E).repr
        (chartTransitionAt (I := I) α β x
          ((chartModelBasis E) a)) i := rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma fderivWithin_range_I_eq_fderiv [I.Boundaryless]
    (f : E → E) (y : E) :
    fderivWithin ℝ f (Set.range I) y = fderiv ℝ f y := by
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
lemma tangentCoordChange_eq_chartTransitionAt [I.Boundaryless]
    (α β : M) (p : M) :
    tangentCoordChange I α β p =
      chartTransitionAt (I := I) α β (extChartAt I α p) := by
  rw [tangentCoordChange_def]
  rw [chartTransitionAt_def]
  rw [chartTransitionMap_def]
  exact fderivWithin_range_I_eq_fderiv (I := I)
    (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α p)

omit [InnerProductSpace ℝ E] in
theorem chartGramOnE_eq_sum_chartTransition [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (x : E)
    (hx : x ∈ (extChartAt I α) ''
              ((chartAt H α).source ∩ (chartAt H β).source))
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j x =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionAtEntry (I := I) α β x a i *
        chartTransitionAtEntry (I := I) α β x b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) := by
  classical
  obtain ⟨p, ⟨hp_α_src, hp_β_src⟩, hp_eq⟩ := hx
  have hp_ext_α : p ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hp_α_src
  have hp_ext_β : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β_src
  have hx_eq : extChartAt I α p = x := hp_eq
  have hp_symm : (extChartAt I α).symm x = p := by
    rw [← hx_eq, (extChartAt I α).left_inv hp_ext_α]
  have h_tβ : chartTransitionMap (I := I) α β x = extChartAt I β p := by
    change extChartAt I β ((extChartAt I α).symm x) = extChartAt I β p
    rw [hp_symm]
  have hp_triv_α : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source; exact hp_α_src
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β_src
  have h_lhs :
      chartGramOnE (I := I) g α i j x =
        chartGramMatrix g α p i j := by
    change chartGramMatrix g α ((extChartAt I α).symm x) i j =
        chartGramMatrix g α p i j
    rw [hp_symm]
  have h_rhs_inner : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g β a b
        (chartTransitionMap (I := I) α β x) =
      chartGramMatrix g β p a b := by
    intro a b
    change chartGramMatrix g β
        ((extChartAt I β).symm (chartTransitionMap (I := I) α β x)) a b =
      chartGramMatrix g β p a b
    rw [h_tβ, (extChartAt I β).left_inv hp_ext_β]
  rw [h_lhs]
  rw [chartGramMatrix_pullback_eq_sum (I := I) g β α
        hp_triv_β hp_triv_α i j]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [h_rhs_inner k l]
  congr 1
  congr 1
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) α β p]
    simp only [chartTransitionAtEntry_def, hx_eq]
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) α β p]
    simp only [chartTransitionAtEntry_def, hx_eq]

omit [InnerProductSpace ℝ E] in
theorem chartGramOnE_pullback_under_chartTransition [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (x : E)
    (hx : x ∈ (extChartAt I α) ''
              ((chartAt H α).source ∩ (chartAt H β).source))
    (a b : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartTransitionAtEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) i a *
        chartTransitionAtEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) j b *
        chartGramOnE (I := I) g α i j x := by
  classical
  obtain ⟨p, ⟨hp_α_src, hp_β_src⟩, hp_eq⟩ := hx
  have hp_ext_α : p ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hp_α_src
  have hp_ext_β : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β_src
  have hx_eq : extChartAt I α p = x := hp_eq
  have hp_symm : (extChartAt I α).symm x = p := by
    rw [← hx_eq, (extChartAt I α).left_inv hp_ext_α]
  have h_tβ : chartTransitionMap (I := I) α β x = extChartAt I β p := by
    change extChartAt I β ((extChartAt I α).symm x) = extChartAt I β p
    rw [hp_symm]
  have hp_triv_α : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source; exact hp_α_src
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β_src
  have h_lhs :
      chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) =
        chartGramMatrix g β p a b := by
    change chartGramMatrix g β
        ((extChartAt I β).symm (chartTransitionMap (I := I) α β x)) a b =
      chartGramMatrix g β p a b
    rw [h_tβ, (extChartAt I β).left_inv hp_ext_β]
  have h_rhs_inner : ∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i j x =
        chartGramMatrix g α p i j := by
    intro i j
    change chartGramMatrix g α ((extChartAt I α).symm x) i j =
      chartGramMatrix g α p i j
    rw [hp_symm]
  rw [h_lhs]
  rw [chartGramMatrix_pullback_eq_sum (I := I) g α β
        hp_triv_α hp_triv_β a b]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_rhs_inner i j]
  congr 1
  congr 1
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) β α p]
    simp only [chartTransitionAtEntry_def, h_tβ]
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt (I := I) β α p]
    simp only [chartTransitionAtEntry_def, h_tβ]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
