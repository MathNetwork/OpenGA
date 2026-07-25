import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ChartDictionary

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Decomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def movingTrivCorrection (α : M) (X : Π y : M, TangentSpace I y) (w : E) : E :=
  (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) w)
    (chartRawRepr (I := I) α X (extChartAt I α α))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π y : M, TangentSpace I y) (w : E)
    (hRdiff : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    chartLeviCivitaInnerCLM (I := I) g α X α w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + movingTrivCorrection (I := I) α X w
        + christoffelCorrection (I := I) g α α
            (chartE_section_repr (I := I) α X α) w := by
  classical
  rw [chartLeviCivitaInnerCLM_apply]
  have htriv_id : trivToE (I := I) α α w = w := by
    have hbase := chartMovingTriv_basepoint (I := I) α w
    have hself : (extChartAt I α).symm (extChartAt I α α) = α :=
      (extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)
    rw [chartMovingTriv, hself] at hbase
    exact hbase
  rw [htriv_id]
  rw [chartLeviCivita_flat_summand_eq_rawRepr (I := I) α X w hRdiff hCdiff]
  rw [movingTrivCorrection]

end Decomposition

section Reconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem hQinner_of_flat_value_and_corrections
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
    (hcov : Q (Dchart' d)
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
              (mfderiv I I (Φ_fam t : M → M) x v))) :
    Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)) := by
  classical
  set α := Φ_fam t x with hα
  set w : E := mfderiv I I (Φ_fam t : M → M) x v with hw
  have hdecomp :
      chartLeviCivitaInnerCLM (I := I) g α (X : ∀ y : M, TangentSpace I y) α w
        = fderiv ℝ (chartRawRepr (I := I) α (X : ∀ y : M, TangentSpace I y))
            (extChartAt I α α) w
          + movingTrivCorrection (I := I) α (X : ∀ y : M, TangentSpace I y) w
          + christoffelCorrection (I := I) g α α
              (chartE_section_repr (I := I) α (X : ∀ y : M, TangentSpace I y) α) w :=
    chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections (I := I) g α
      (X : ∀ y : M, TangentSpace I y) w hRdiff hCdiff
  rw [hcov, hdecomp, map_add, map_add, neg_add, neg_add]
  abel

end Reconstruction

section Producer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_flatChartFderiv_witness
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
    (hcov : Q (Dchart' d)
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
              (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hQinner :
      Q (Dchart' d)
        = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)) :=
    hQinner_of_flat_value_and_corrections (I := I) g X Φ_fam t x v Q Dchart' d
      hRdiff hCdiff hcov
  exact rawVariationalIdentity_of_chartFderiv_witness (I := I) g X Φ_fam t x v Q d
    hDchart hcontAt hwitness hQinner

end Producer

end DifferentialGeometry.PDE.RicciFlow.ODE
