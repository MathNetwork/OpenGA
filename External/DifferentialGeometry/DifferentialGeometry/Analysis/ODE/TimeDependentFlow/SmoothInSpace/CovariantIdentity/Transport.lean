import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.VariationalLift

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section InnerCLMBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem trivFromE_innerCLM_eq_leviCivita_at_orbit
    (g : SmoothRiemannianMetric I M)
    (X : Π x : M, TangentSpace I x)
    (α : M) (d : TangentSpace I α)
    (hα : α ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) α) :
    trivFromE (I := I) α α (chartLeviCivitaInnerCLM (I := I) g α X α d)
      = (LeviCivita (I := I) g) X α d := by
  have hchart :
      chartLeviCivita (I := I) g α X α d
        = trivFromE (I := I) α α (chartLeviCivitaInnerCLM (I := I) g α X α d) := by
    rw [chartLeviCivita_apply (I := I) g α X hα d]
    rw [chartLeviCivitaInnerCLM_apply (I := I) g α X α d]
  have hbundled :
      (LeviCivita (I := I) g) X α d = chartLeviCivita (I := I) g α X α d :=
    LeviCivita_chart_apply (I := I) g α hα hX d
  rw [hbundled, hchart]

end InnerCLMBridge

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem rawVariationalIdentity_of_chartFlow_value
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hQval : Q (Dchart' d)
      = -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have h1 :=
    hasDerivAt_mfderiv_flow_of_chart (I := I) (Fam := fun s => (Φ_fam s : M → M))
      t x v Q d hDchart hagree
  rw [hQval] at h1
  exact h1

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem rawVariationalIdentity_of_chartFlow
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hLC : trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
        (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
          (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v))
      = (LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v))
    (hQinner : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hQval : Q (Dchart' d)
      = -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) := by
    rw [hQinner, hLC]
  exact rawVariationalIdentity_of_chartFlow_value (I := I) g X Φ_fam t x v Q d
    hDchart hagree hQval

end Transport

end DifferentialGeometry.PDE.RicciFlow.ODE
