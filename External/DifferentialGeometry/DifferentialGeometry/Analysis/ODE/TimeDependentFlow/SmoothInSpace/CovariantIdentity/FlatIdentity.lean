import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ManifoldFlowOrbitODE
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatToCovariant
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelCorrectionBasepoint

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section FlatIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def RawVariationalIdentityFlat
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) (T' P' : E →L[ℝ] E) : Prop :=
  HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
    (T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v) t

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem rawVariationalIdentityFlat_iff_flat_value
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) (T' P' : E →L[ℝ] E)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P'
      ↔ HasDerivAt (fun s : ℝ => flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)
          (T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v) t := by
  unfold RawVariationalIdentityFlat
  exact (Filter.EventuallyEq.hasDerivAt_iff
    (chartCloseDop_eventuallyEq_mfderiv_orbit (I := I) Φ_fam t x v hcontAt)).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem rawVariationalIdentityFlat_of_orbitODE_factors
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {T' P' : E →L[ℝ] E}
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x) P' t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P' := by
  have hDchart := chartCloseDop_hasDerivAt_clm_comp (I := I) Φ_fam (Φ_fam t x) x t hT hP
  have hEvalv :
      HasDerivAt (fun s : ℝ => flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)
        ((T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
            + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v) t := by
    have := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt t hDchart
    simpa using this
  rw [chartCloseDop_deriv_basepoint_apply (I := I) Φ_fam t x v T' P'] at hEvalv
  exact (rawVariationalIdentityFlat_iff_flat_value (I := I) Φ_fam t x v T' P' hcontAt).2 hEvalv

end FlatIdentity

end DifferentialGeometry.PDE.RicciFlow.ODE
