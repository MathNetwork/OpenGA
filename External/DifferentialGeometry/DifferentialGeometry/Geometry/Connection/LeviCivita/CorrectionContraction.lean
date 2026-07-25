import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Geodesic.Equation

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]



omit [NeZero (Module.finrank ℝ E)] in
theorem correction_eq_contr
    (g : SmoothRiemannianMetric I M) (a x : M) (Y : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g a x Y v =
      chartChristoffelContraction (I := I) g a
        (trivToE (I := I) a x v) Y (extChartAt I a x) := by
  classical
  rw [christoffelCorrection_apply, chartChristoffelContraction_def]
  set F : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → E :=
    fun i j k ↦
      (chartChristoffel (I := I) g a i j k (extChartAt I a x) *
          (chartModelBasis E).repr (trivToE (I := I) a x v) i *
          (chartModelBasis E).repr Y j) • (chartModelBasis E) k with hF
  have hLHS :
      (∑ i, ∑ j, ∑ k,
          ((chartModelBasis E).repr (trivToE (I := I) a x v) i *
                (chartModelBasis E).repr Y j *
                chartChristoffel (I := I) g a i j k (extChartAt I a x)) •
            (chartModelBasis E) k) =
        ∑ i, ∑ j, ∑ k, F i j k := by
    refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦
      Finset.sum_congr rfl (fun k _ ↦ ?_)))
    rw [hF]
    congr 1
    ring
  have hRHS :
      (∑ k,
          (∑ i, ∑ j,
              chartChristoffel (I := I) g a i j k (extChartAt I a x) *
                chartCoord (E := E) i (trivToE (I := I) a x v) *
                chartCoord (E := E) j Y) •
            (chartModelBasis E) k) =
        ∑ i, ∑ j, ∑ k, F i j k := by
    have hstep :
        (∑ k,
            (∑ i, ∑ j,
                chartChristoffel (I := I) g a i j k (extChartAt I a x) *
                  chartCoord (E := E) i (trivToE (I := I) a x v) *
                  chartCoord (E := E) j Y) •
              (chartModelBasis E) k) =
          ∑ k, ∑ i, ∑ j, F i j k := by
      refine Finset.sum_congr rfl (fun k _ ↦ ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [hF, chartCoord_def, chartCoord_def]
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [Finset.sum_comm]
  rw [hLHS, hRHS]



omit [NeZero (Module.finrank ℝ E)] in
theorem const_cov_eq_contr
    (g : SmoothRiemannianMetric 𝓘(Real, E) E) (a z v w : E) :
    (leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (fun _ : E ↦ w) z) v =
      chartChristoffelContraction (I := 𝓘(Real, E)) g a v w z := by
  have hzgood : z ∈ chartLeviCivitaGoodSet (I := 𝓘(Real, E)) a := by
    rw [mem_chartLeviCivitaGoodSet_iff]
    simp
  have hfield :
      (tangentConstAt (I := 𝓘(Real, E)) z w : E → E) = fun _ : E ↦ w := by
    funext p
    unfold tangentConstAt TensorLieDeriv.tangentConstInChart
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (I := 𝓘(Real, E)) (b₀ := z) (b := p) (by simp)]
    rw [TangentBundle.coordChange_model_space]
    rfl
  have hrepr :
      chartE_section_repr (I := 𝓘(Real, E)) a (fun _ : E ↦ w) =
        fun _ : E ↦ w := by
    funext p
    rw [chartE_section_repr_eq_trivToE]
    change (trivializationAt E (TangentSpace 𝓘(Real, E)) a).continuousLinearMapAt
      Real p w = w
    rw [TangentBundle.continuousLinearMapAt_model_space]
    rfl
  rw [← hfield]
  change (LeviCivita (I := 𝓘(Real, E)) g).toFun
      (tangentConstAt (I := 𝓘(Real, E)) z w) z v = _
  rw [LeviCivita_chart_apply (I := 𝓘(Real, E)) g a hzgood
    (mdifferentiableAt_tangentConstAt_self (I := 𝓘(Real, E)) z w) v]
  rw [hfield]
  rw [chartLeviCivita_apply (I := 𝓘(Real, E)) g a
    (fun _ : E ↦ w) hzgood v]
  rw [hrepr]
  rw [show ((fun _ : E ↦ w) ∘ (extChartAt 𝓘(Real, E) a).symm) =
    (fun _ : E ↦ w) from rfl]
  rw [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_add]
  rw [correction_eq_contr]
  simp only [trivFromE, trivToE, TangentBundle.symmL_model_space,
    TangentBundle.continuousLinearMapAt_model_space,
    extChartAt_self_apply, modelWithCornersSelf_coe, id_eq]
  change chartChristoffelContraction (I := 𝓘(Real, E)) g a v w z = _
  rfl

end Connection
end Integral
end DifferentialGeometry
