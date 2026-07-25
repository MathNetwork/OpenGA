import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.FactorProducers
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.EuclideanVariationalODE
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.FlatPairedResidual


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff NNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.PDE.DeTurck

section Discharge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem hasDerivAt_partialSpatialFderiv_of_isLocalFlow_at_chart
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ Φ U)
    (α x : M) {t : ℝ}
    (hxsU : (extChartAt I α x, t) ∈ U)
    (hx : extChartAt I α x ∈ Metric.ball x₀ r) (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fun z => (fun z' s' => Φ (z', s')) z s)
        (extChartAt I α x))
      ((fderiv ℝ (f t) (Φ (extChartAt I α x, t))).comp
        (fderiv ℝ (fun z => Φ (z, t)) (extChartAt I α x))) t :=
  IsLocalFlow.hasDerivAt_partial_spatial_fderiv hΦ hf hUopen hΦsmooth hxsU hx ht

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [BoundarylessManifold I M] in
theorem hagree_of_spatial_chart_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ) (Φ_eucl : E → ℝ → E)
    (hreal : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y = (extChartAt I α).symm (Φ_eucl (extChartAt I α y) s)
        ∧ Φ_eucl (extChartAt I α y) s ∈ (extChartAt I α).target) :
    ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I α ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s) := by
  filter_upwards [hreal] with s hs
  filter_upwards [hs] with y hy
  obtain ⟨hpt, htgt⟩ := hy
  rw [hpt, (extChartAt I α).right_inv htgt]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem chartMovingTriv_orbit_hasDerivAt_of_chartJet
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart : E}
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) α z) G'
      (extChartAt I α ((Φ_fam t : M → M) x)))
    (hc : HasDerivAt (fun s : ℝ => extChartAt I α ((Φ_fam s : M → M) x)) velChart t) :
    HasDerivAt (fun s : ℝ => chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))) (G' velChart) t := by
  have := hGfd.comp_hasDerivAt t hc
  simpa using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseFactors_of_chart_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (x : M) (t : ℝ)
    (Φ_eucl : E → ℝ → E) {D'_eucl g' : E →L[ℝ] E}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x)) D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x))
    (hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I (Φ_fam t x) y) s))
    (hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) g' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x)
        ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
            (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g') t
      ∧ HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x)
          (D'_eucl.comp (trivToE (I := I) (Φ_fam t x) x)) t := by
  refine ⟨chartCloseTriv_hasDerivAt_of_movingTriv (I := I) Φ_fam t x hg hcontAt, ?_⟩
  exact chartCloseFderiv_hasDerivAt_of_eucl (I := I) Φ_fam (Φ_fam t x) x t Φ_eucl
    hx_src heucl heucl_diff hagree

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem rawVariationalIdentityFlat_of_chart_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (x : M) (t : ℝ) (v : TangentSpace I x)
    (Φ_eucl : E → ℝ → E) {D'_eucl g' : E →L[ℝ] E}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x)) D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x))
    (hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I (Φ_fam t x) y) s))
    (hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) g' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g')
      (D'_eucl.comp (trivToE (I := I) (Φ_fam t x) x)) := by
  obtain ⟨hT, hP⟩ := chartCloseFactors_of_chart_realisation (I := I) Φ_fam x t Φ_eucl
    hx_src heucl heucl_diff hagree hg hcontAt
  exact rawVariationalIdentityFlat_of_orbitODE_factors (I := I) Φ_fam t x v hcontAt hT hP

end Discharge

section PairedResidualDischarge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leviCivita_flowBasepoint_eq_chartFderiv_add_corrections
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (u : TangentSpace I x)
    (hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x))) :
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x u)
      = (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x u)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x u))
        + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
            (chartE_section_repr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x u) :=
  leviCivita_basepoint_eq_rawFderiv_add_corrections (I := I) g (Φ_fam t x)
    (X : ∀ y : M, TangentSpace I y) (mfderiv I I (Φ_fam t : M → M) x u)
    hα (X.mdifferentiableAt) hRdiff hCdiff

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem variational_flow_flat_paired_residual_of_chart_realisation
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hflatval_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v)))
    (hflatval_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x w))) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) t :=
  variational_flow_flat_paired_residual_hasDerivAt (I := I) g X Φ_fam t x v w
    T'v P'v T'w P'w hv_flat hw_flat hflatval_v hflatval_w
    (leviCivita_flowBasepoint_eq_chartFderiv_add_corrections (I := I) g X Φ_fam t x v hα hRdiff hCdiff)
    (leviCivita_flowBasepoint_eq_chartFderiv_add_corrections (I := I) g X Φ_fam t x w hα hRdiff hCdiff)

end PairedResidualDischarge

end DifferentialGeometry.PDE.RicciFlow.ODE
