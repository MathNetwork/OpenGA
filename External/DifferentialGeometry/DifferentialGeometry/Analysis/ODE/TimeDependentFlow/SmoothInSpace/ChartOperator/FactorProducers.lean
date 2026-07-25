import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ManifoldFlowOrbitODE
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.EuclideanVariationalODE
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.VariationalLift
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.ODE.Flow

section FactorProducers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

theorem hasDerivAt_clm_comp_right
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) (R : E →L[ℝ] E) :
    HasDerivAt (fun s : ℝ => (A s).comp R) (A'.comp R) t := by
  have hcompR : HasFDerivAt (fun L : E →L[ℝ] E => L.comp R)
      ((ContinuousLinearMap.compL ℝ E E E).flip R) (A t) :=
    ((ContinuousLinearMap.compL ℝ E E E).flip R).hasFDerivAt
  have := hcompR.comp_hasDerivAt t hA
  simpa using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

theorem chartCloseFderiv_eq_eucl_comp_trivToE
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ)
    (Φ_eucl : E → ℝ → E)
    (hx_src : x ∈ (chartAt H α).source)
    (heucl_diff : DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I α x))
    (hagree : (fun y => extChartAt I α ((Φ_fam s : M → M) y))
      =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s)) :
    chartCloseFderiv (I := I) Φ_fam α x s
      = (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp
          (trivToE (I := I) α x) := by
  unfold chartCloseFderiv
  have hmfeq : mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x
      = mfderiv I 𝓘(ℝ, E) (fun y => Φ_eucl (extChartAt I α y) s) x :=
    Filter.EventuallyEq.mfderiv_eq hagree
  rw [hmfeq]
  have hsrc_eq : mfderiv I 𝓘(ℝ, E) (extChartAt I α) x = trivToE (I := I) α x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hx_src).symm
  have hext_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) hx_src
  have heucl_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ_eucl z s)
      (extChartAt I α x) :=
    heucl_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ, E) ((fun z => Φ_eucl z s) ∘ (extChartAt I α)) x
        = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ_eucl z s) (extChartAt I α x)).comp
            (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x heucl_mdiff hext_diff
  have hcompfun : (fun y => Φ_eucl (extChartAt I α y) s)
      = (fun z => Φ_eucl z s) ∘ (extChartAt I α) := rfl
  rw [hcompfun, hchain, hsrc_eq]
  rw [mfderiv_eq_fderiv]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

theorem chartCloseFderiv_hasDerivAt_of_eucl
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    (Φ_eucl : E → ℝ → E) {D'_eucl : E →L[ℝ] E}
    (hx_src : x ∈ (chartAt H α).source)
    (heucl : HasDerivAt (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x))
      D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I α x))
    (hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I α ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s)) :
    HasDerivAt (chartCloseFderiv (I := I) Φ_fam α x)
      (D'_eucl.comp (trivToE (I := I) α x)) t := by
  letI : InnerProductSpace ℝ (TangentSpace I x) := (inferInstance : InnerProductSpace ℝ E)
  have hpost : HasDerivAt
      (fun s : ℝ => (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp (trivToE (I := I) α x))
      (D'_eucl.comp (trivToE (I := I) α x)) t :=
    hasDerivAt_clm_comp_right heucl (trivToE (I := I) α x)
  have hev : (fun s : ℝ => chartCloseFderiv (I := I) Φ_fam α x s)
      =ᶠ[𝓝 t] (fun s : ℝ =>
        (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp (trivToE (I := I) α x)) := by
    filter_upwards [heucl_diff, hagree] with s hsd hsa
    exact chartCloseFderiv_eq_eucl_comp_trivToE (I := I) Φ_fam α x s Φ_eucl hx_src hsd hsa
  exact hpost.congr_of_eventuallyEq hev

section MovingTrivInverse

variable [CompleteSpace E]

omit [CompleteSpace E] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartMovingTriv_basepoint_isUnit (α : M) :
    IsUnit (chartMovingTriv (I := I) α (extChartAt I α α)) := by
  have h1 : chartMovingTriv (I := I) α (extChartAt I α α) = (1 : E →L[ℝ] E) := by
    ext v
    simpa using chartMovingTriv_basepoint (I := I) α v
  rw [h1]
  exact isUnit_one

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] in
theorem chartCloseTriv_eq_ringInverse_chartMovingTriv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ)
    (hsrc : (Φ_fam s : M → M) x ∈ (chartAt H α).source) :
    chartCloseTriv (I := I) Φ_fam α x s
      = Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α ((Φ_fam s : M → M) x))) := by
  set b : M := (Φ_fam s : M → M) x with hb_def
  have hbase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hsrc
  have hbsymm : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv (by simpa [extChartAt_source] using hsrc)
  have hmul : chartMovingTriv (I := I) α (extChartAt I α b)
      * chartCloseTriv (I := I) Φ_fam α x s = 1 := by
    rw [ContinuousLinearMap.mul_def]; ext w
    change chartMovingTriv (I := I) α (extChartAt I α b)
        (chartCloseTriv (I := I) Φ_fam α x s w) = w
    unfold chartCloseTriv chartMovingTriv
    rw [hbsymm]
    exact trivToE_trivFromE (I := I) α hbase w
  have hmul' : chartCloseTriv (I := I) Φ_fam α x s
      * chartMovingTriv (I := I) α (extChartAt I α b) = 1 := by
    rw [ContinuousLinearMap.mul_def]; ext w
    change chartCloseTriv (I := I) Φ_fam α x s
        (chartMovingTriv (I := I) α (extChartAt I α b) w) = w
    unfold chartCloseTriv chartMovingTriv
    rw [hbsymm]
    exact trivFromE_trivToE (I := I) α hbase w
  have hunit : IsUnit (chartMovingTriv (I := I) α (extChartAt I α b)) :=
    isUnit_iff_exists_and_exists.mpr
      ⟨⟨chartCloseTriv (I := I) Φ_fam α x s, hmul⟩, ⟨chartCloseTriv (I := I) Φ_fam α x s, hmul'⟩⟩
  symm
  calc Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α b))
      = Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α b))
          * (chartMovingTriv (I := I) α (extChartAt I α b)
              * chartCloseTriv (I := I) Φ_fam α x s) := by rw [hmul, mul_one]
    _ = (Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α b))
          * chartMovingTriv (I := I) α (extChartAt I α b))
          * chartCloseTriv (I := I) Φ_fam α x s := by rw [mul_assoc]
    _ = chartCloseTriv (I := I) Φ_fam α x s := by
          rw [Ring.inverse_mul_cancel _ hunit, one_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartCloseTriv_hasDerivAt_of_movingTriv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) {g' : E →L[ℝ] E}
    (hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) g' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x)
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g') t := by
  classical
  set α : M := Φ_fam t x with hα
  have ht_self : (Φ_fam t : M → M) x = α := rfl
  have hbase_eq : (fun s : ℝ => chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))) t
      = chartMovingTriv (I := I) α (extChartAt I α α) := by
    simp only [ht_self]
  have hunit1 : chartMovingTriv (I := I) α (extChartAt I α α) = (1 : E →L[ℝ] E) := by
    ext v; simpa using chartMovingTriv_basepoint (I := I) α v
  have hinv_fderiv : HasFDerivAt (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (1 : E →L[ℝ] E) (1 : E →L[ℝ] E))
      (chartMovingTriv (I := I) α (extChartAt I α α)) := by
    have hu : (chartMovingTriv (I := I) α (extChartAt I α α)) = ((1 : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) :=
      by rw [hunit1]; rfl
    rw [hu]
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := E →L[ℝ] E) (1 : (E →L[ℝ] E)ˣ)
    simpa using this
  have hgt_eq : (fun s : ℝ => chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))) t
      = chartMovingTriv (I := I) α (extChartAt I α α) := hbase_eq
  have hchain : HasDerivAt
      (fun s : ℝ => Ring.inverse (chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))))
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g') t := by
    have := (hgt_eq ▸ hinv_fderiv).comp_hasDerivAt t hg
    simpa using this
  have hmem : ∀ᶠ s : ℝ in 𝓝 t,
      (Φ_fam s : M → M) x ∈ (chartAt H α).source :=
    flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  have hev : (chartCloseTriv (I := I) Φ_fam α x)
      =ᶠ[𝓝 t] (fun s : ℝ => Ring.inverse (chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x)))) := by
    filter_upwards [hmem] with s hs
    exact chartCloseTriv_eq_ringInverse_chartMovingTriv (I := I) Φ_fam α x s hs
  exact hchain.congr_of_eventuallyEq hev

end MovingTrivInverse

end FactorProducers

end DifferentialGeometry.PDE.RicciFlow.ODE
