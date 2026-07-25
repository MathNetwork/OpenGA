import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ManifoldFlowOrbitReduction


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section OrbitODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartCloseTriv (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  trivFromE (I := I) α ((Φ_fam s : M → M) x)

def chartCloseFderiv (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartCloseDop_eq_comp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam α x s
      = (chartCloseTriv (I := I) Φ_fam α x s).comp
          (chartCloseFderiv (I := I) Φ_fam α x s) :=
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartCloseTriv_basepoint
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (w : E) :
    chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t w = w := by
  classical
  unfold chartCloseTriv
  set α : M := Φ_fam t x with hα
  have hcore : trivFromE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) w

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseDop_hasDerivAt_clm_comp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    {T' P' : E →L[ℝ] E}
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam α x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam α x) P' t) :
    HasDerivAt (flowOrbitChartTrivDerivOp (I := I) Φ_fam α x)
      (T'.comp (chartCloseFderiv (I := I) Φ_fam α x t)
        + (chartCloseTriv (I := I) Φ_fam α x t).comp P') t := by
  have hcomp : (fun s : ℝ =>
        (chartCloseTriv (I := I) Φ_fam α x s).comp
          (chartCloseFderiv (I := I) Φ_fam α x s))
      = flowOrbitChartTrivDerivOp (I := I) Φ_fam α x := by
    funext s
    exact (chartCloseDop_eq_comp (I := I) Φ_fam α x s).symm
  have := hT.clm_comp hP
  rwa [hcomp] at this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseDop_deriv_basepoint_apply
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (T' P' : E →L[ℝ] E) :
    (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
        + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v
      = T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v := by
  classical
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
  rw [chartCloseTriv_basepoint (I := I) Φ_fam t x (P' v)]
  have hPv : chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t v
      = mfderiv I I (Φ_fam t : M → M) x v := by
    have hdop : flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x t v
        = chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t v := by
      rw [chartCloseDop_apply]
      exact chartCloseTriv_basepoint (I := I) Φ_fam t x
        (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t v)
    rw [← hdop]
    exact chartCloseDop_basepoint_apply_eq_mfderiv (I := I) Φ_fam t x v
  rw [hPv]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_orbitODE_factors
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {T' P' : E →L[ℝ] E}
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x) P' t)
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
        + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
        + (-trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hDchart := chartCloseDop_hasDerivAt_clm_comp (I := I) Φ_fam (Φ_fam t x) x t hT hP
  exact rawVariationalIdentity_of_manifoldFlowFamily_chartClose (I := I) g X Φ_fam t x v
    hcont hDchart hRdiff hCdiff hsplit

end OrbitODE

end DifferentialGeometry.PDE.RicciFlow.ODE
