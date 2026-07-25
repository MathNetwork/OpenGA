import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.Transport

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section OrbitValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leviCivita_orbit_value_eq
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) :
    trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
        (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
          (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v))
      = (LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) := by
  have hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x) :=
    self_mem_chartLeviCivitaGoodSet (I := I) (Φ_fam t x)
  have hX : MDiffAt (T% (X : ∀ x : M, TangentSpace I x)) (Φ_fam t x) :=
    (X.contMDiff (Φ_fam t x)).mdifferentiableAt (by simp)
  exact trivFromE_innerCLM_eq_leviCivita_at_orbit (I := I) g
    (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v) hα hX

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem negCovariant_value_of_innerCLM_value
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) (val : E)
    (hQinner : val
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    val
      = -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) := by
  rw [hQinner, leviCivita_orbit_value_eq (I := I) g X Φ_fam t x v]

end OrbitValue

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_chartFlow_innerCLM
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hQinner : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hQval := negCovariant_value_of_innerCLM_value (I := I) g X Φ_fam t x v
    (Q (Dchart' d)) hQinner
  exact rawVariationalIdentity_of_chartFlow_value (I := I) g X Φ_fam t x v Q d
    hDchart hagree hQval

end Assembly

end DifferentialGeometry.PDE.RicciFlow.ODE
