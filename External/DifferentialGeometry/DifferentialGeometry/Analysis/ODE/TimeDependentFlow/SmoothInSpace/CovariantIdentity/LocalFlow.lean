import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatToCovariant
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.EuclideanVariationalODE

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Reconciliation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartTrivRepr (I := I) α X) (extChartAt I α α) w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + movingTrivCorrection (I := I) α X w := by
  rw [chartTrivRepr_fderiv_eq (I := I) α X w hR hC, movingTrivCorrection]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem flatLinearization_eq_rawFderiv_add_movingTriv
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (fun z => -(chartTrivRepr (I := I) α X z)) (extChartAt I α α) w
      = -(fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
          + movingTrivCorrection (I := I) α X w) := by
  rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  rw [chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv (I := I) α X w hR hC]

end Reconciliation

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem hcov_of_flatTrivPart_and_movingTrivResidual
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (Dchart' : E →L[ℝ] E) (d : E)
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : Q (Dchart' d)
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
    Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)) := by
  classical
  have hAdecomp :
      fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
          (extChartAt I (Φ_fam t x) (Φ_fam t x))
          (mfderiv I I (Φ_fam t : M → M) x v)
        = fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v) :=
    chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv (I := I) (Φ_fam t x)
      (X : ∀ y : M, TangentSpace I y) (mfderiv I I (Φ_fam t : M → M) x v) hRdiff hCdiff
  rw [hsplit, hAdecomp, map_add]
  abel

end Assembly

section Producer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_isLocalFlow
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : Q (Dchart' d)
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
  have hcov := hcov_of_flatTrivPart_and_movingTrivResidual (I := I) g X Φ_fam t x v
    Q Dchart' d hRdiff hCdiff hsplit
  exact rawVariationalIdentity_of_flatChartFderiv_witness (I := I) g X Φ_fam t x v Q d
    hDchart hcontAt hwitness hRdiff hCdiff hcov

end Producer

end DifferentialGeometry.PDE.RicciFlow.ODE
