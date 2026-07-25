import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.EuclideanVariationalODE
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.VariationalFlow
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem hasDerivAt_clm_pre_post
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) (Q : E →L[ℝ] E) (d : E) :
    HasDerivAt (fun s : ℝ => Q (A s d)) (Q (A' d)) t := by
  have hEval : HasDerivAt (fun s : ℝ => A s d) (A' d) t := by
    have := (ContinuousLinearMap.apply ℝ E d).hasFDerivAt.comp_hasDerivAt t hA
    simpa [ContinuousLinearMap.apply_apply] using this
  have := Q.hasFDerivAt.comp_hasDerivAt t hEval
  simpa using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem hasDerivAt_mfderiv_flow_of_chart
    (Fam : ℝ → (M → M)) (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Fam s) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d))) :
    HasDerivAt (fun s : ℝ => (mfderiv I I (Fam s) x v : E)) (Q (Dchart' d)) t := by
  have hchart : HasDerivAt (fun s : ℝ => Q (Dchart s d)) (Q (Dchart' d)) t :=
    hasDerivAt_clm_pre_post hDchart Q d
  exact hchart.congr_of_eventuallyEq hagree

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartLeviCivita_flat_add_christoffel
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) x) (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun X x v
      = trivFromE (I := I) α x
          (fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v)
            + christoffelCorrection (I := I) g α x
                (chartE_section_repr (I := I) α X x) v) := by
  rw [LeviCivita_chart_apply (I := I) g α hx hX v]
  rw [chartLeviCivita_apply (I := I) g α X hx v]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartLeviCivita_flat_eq_sub_christoffel
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) x) (v : TangentSpace I x) :
    trivFromE (I := I) α x
        (fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v))
      = (LeviCivita (I := I) g).toFun X x v
          - trivFromE (I := I) α x
              (christoffelCorrection (I := I) g α x
                (chartE_section_repr (I := I) α X x) v) := by
  have hsplit := chartLeviCivita_flat_add_christoffel (I := I) g α X hx hX v
  rw [map_add] at hsplit
  rw [hsplit]
  abel

end DifferentialGeometry.PDE.RicciFlow.ODE
