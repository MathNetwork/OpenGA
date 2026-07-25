import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.ConcreteFlow

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section OrbitReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseDop_apply_eq_mfderiv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) (v : TangentSpace I x)
    (hsrc : (Φ_fam s : M → M) x ∈ (chartAt H α).source) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam α x s v = mfderiv I I (Φ_fam s : M → M) x v := by
  have hF : MDifferentiableAt I I (Φ_fam s : M → M) x :=
    flowFamily_mdifferentiableAt_fixed_time (I := I) Φ_fam s x
  rw [chartCloseDop_apply]
  exact (mfderiv_flow_eq_chartFderiv_apply (I := I) (Φ_fam s : M → M) α v hF hsrc).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseDop_basepoint_apply_eq_mfderiv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x t v
      = mfderiv I I (Φ_fam t : M → M) x v :=
  chartCloseDop_apply_eq_mfderiv (I := I) Φ_fam (Φ_fam t x) x t v (mem_chart_source H _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseDop_eventuallyEq_mfderiv_orbit
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    (fun s : ℝ => flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)
      =ᶠ[𝓝 t] (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) := by
  have hmem : ∀ᶠ s : ℝ in 𝓝 t,
      (Φ_fam s : M → M) x ∈ (chartAt H (Φ_fam t x)).source :=
    flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  filter_upwards [hmem] with s hs
  exact chartCloseDop_apply_eq_mfderiv (I := I) Φ_fam (Φ_fam t x) x s v hs

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem rawVariationalIdentity_iff_hasDerivAt_chartCloseDop
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v
      ↔ HasDerivAt (fun s : ℝ => flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)
          (-(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)) t := by
  unfold RawVariationalIdentity
  exact (Filter.EventuallyEq.hasDerivAt_iff
    (chartCloseDop_eventuallyEq_mfderiv_orbit (I := I) Φ_fam t x v hcontAt)).symm

end OrbitReduction

end DifferentialGeometry.PDE.RicciFlow.ODE
