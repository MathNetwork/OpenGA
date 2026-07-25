import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ChartDictionary


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartRawRepr (α : M) (X : Π y : M, TangentSpace I y) (z : E) : E :=
  (X ((extChartAt I α).symm z) : E)

def chartTrivRepr (α : M) (X : Π y : M, TangentSpace I y) (z : E) : E :=
  chartE_section_repr (I := I) α X ((extChartAt I α).symm z)

def chartMovingTriv (α : M) (z : E) : E →L[ℝ] E :=
  trivToE (I := I) α ((extChartAt I α).symm z)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartTrivRepr_eq_movingTriv_rawRepr
    (α : M) (X : Π y : M, TangentSpace I y) (z : E) :
    chartTrivRepr (I := I) α X z
      = chartMovingTriv (I := I) α z (chartRawRepr (I := I) α X z) := by
  unfold chartTrivRepr chartMovingTriv chartRawRepr
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartMovingTriv_basepoint
    (α : M) (v : E) :
    chartMovingTriv (I := I) α (extChartAt I α α) v = v := by
  unfold chartMovingTriv
  have hself : (extChartAt I α).symm (extChartAt I α α) = α :=
    (extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)
  rw [hself]
  have hcore : trivToE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartTrivRepr_fderiv_eq
    (α : M) (X : Π y : M, TangentSpace I y) (h : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartTrivRepr (I := I) α X) (extChartAt I α α) h
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) h
        + (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) h)
            (chartRawRepr (I := I) α X (extChartAt I α α)) := by
  classical
  set z₀ : E := extChartAt I α α with hz₀
  have hTeq : chartTrivRepr (I := I) α X
      = fun z => chartMovingTriv (I := I) α z (chartRawRepr (I := I) α X z) :=
    funext (fun z => chartTrivRepr_eq_movingTriv_rawRepr (I := I) α X z)
  rw [hTeq]
  rw [fderiv_clm_apply hC hR]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [chartMovingTriv_basepoint (I := I) α (fderiv ℝ (chartRawRepr (I := I) α X) z₀ h)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLeviCivita_flat_summand_eq_rawRepr
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
        (extChartAt I α α) w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) w)
            (chartRawRepr (I := I) α X (extChartAt I α α)) := by
  have hcomp : (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
      = chartTrivRepr (I := I) α X := rfl
  rw [hcomp]
  exact chartTrivRepr_fderiv_eq (I := I) α X w hR hC

end Bridge

end DifferentialGeometry.PDE.RicciFlow.ODE
