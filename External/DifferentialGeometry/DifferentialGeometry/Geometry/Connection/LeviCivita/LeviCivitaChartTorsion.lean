import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartLieBracket

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [NeZero (Module.finrank ℝ E)] in
lemma christoffelCorrection_symm_cancel
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (v w : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (trivToE (I := I) α x w) v =
      christoffelCorrection (I := I) g α x (trivToE (I := I) α x v) w := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g α j i k (extChartAt I α x)]
  congr 1
  ring


omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivita_torsion_free_on (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
      x ∈ chartLeviCivitaGoodSet (I := I) α →
      chartLeviCivita (I := I) g α Y x (X x)
        - chartLeviCivita (I := I) g α X x (Y x) =
        VectorField.mlieBracket I X Y x := by
  intro X Y x hX hY hx
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  rw [chartLeviCivita_apply (I := I) g α Y hx (X x)]
  rw [chartLeviCivita_apply (I := I) g α X hx (Y x)]
  rw [← map_sub]
  have hreorg :
      (fderiv ℝ (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
        + christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Y x) (X x))
      - (fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x))
        + christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α X x) (Y x))
      =
      (fderiv ℝ (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
        - fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x))) := by
    have hY_repr : chartE_section_repr (I := I) α Y x =
        trivToE (I := I) α x (Y x) :=
      chartE_section_repr_eq_trivToE (I := I) α Y x
    have hX_repr : chartE_section_repr (I := I) α X x =
        trivToE (I := I) α x (X x) :=
      chartE_section_repr_eq_trivToE (I := I) α X x
    rw [hY_repr, hX_repr]
    have hcancel :
        christoffelCorrection (I := I) g α x (trivToE (I := I) α x (Y x)) (X x) =
          christoffelCorrection (I := I) g α x (trivToE (I := I) α x (X x)) (Y x) :=
      christoffelCorrection_symm_cancel (I := I) g α x (X x) (Y x)
    rw [hcancel]
    abel
  rw [hreorg]
  exact (mlieBracket_eq_chart_fderiv_diff_general (I := I) α x X Y
    hx_src hx_base hx_int hX hY).symm

end Connection
end Integral
end DifferentialGeometry
