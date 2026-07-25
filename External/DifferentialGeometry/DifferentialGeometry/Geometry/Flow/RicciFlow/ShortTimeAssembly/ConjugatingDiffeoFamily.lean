import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.ForwardFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private theorem contMDiffWithinAt_neg_tangentBundleSection
    (X : ℝ → ∀ x : M, TangentSpace I x)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (-(X q.1 q.2)) : TangentBundle I M))
      u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hXfib.neg
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).map_neg (X x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).map_neg (X q₀.1 q₀.2)

omit [NeZero (Module.finrank ℝ E)] in
theorem conjugating_diffeo_family_jointsmooth
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T_DT : ℝ) (hDT : 0 < T_DT)
    (h_smooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T_DT ×ˢ Set.univ)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T_DT ∧ ∃ Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M),
      Φ_fam 0 = _root_.Diffeomorph.refl I M ∞ ∧
      (∀ x : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x)
          (Set.Ici (0 : ℝ)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) x))))) ∧
      (∀ x : M,
        ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) ∧
      (ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (Set.Ico 0 T ×ˢ Set.univ)) ∧
      (∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)),
        ContinuousOn (fun p : ℝ × M =>
          (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
            (mfderiv I I (Φ_fam p.1 : M → M) p.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)) : TangentBundle I M))
          (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) := by
  set X_DT : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => -(deTurckVF (I := I) (g_DT s) g_bg x) with hXDT
  have hsmooth0_X : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Icc (0 : ℝ) T_DT ×ˢ Set.univ) :=
    fun q hq => contMDiffWithinAt_neg_tangentBundleSection
      (fun s x => (deTurckVF (I := I) (g_DT s) g_bg x : TangentSpace I x)) (h_smooth0 q hq)
  obtain ⟨Φ, hΦ0, hdiffeo, hflow, hΦcont0,
      hΦbundle0, hΦorbit_joint, hΦsection_joint, lo, hi, hlo, hhi, hΦsm⟩ :=
    forward_flow_existence_smooth_neighborhood_of_jointsmooth_field
      (I := I) X_DT T_DT hDT hsmooth0_X
  obtain ⟨Φ_fam, hfam0, hfameq, hfamode⟩ :=
    time_dependent_vf_bare_flow_family (I := I) X_DT T_DT hDT Φ hΦ0
      (fun t ht htT => hdiffeo t ⟨ht, htT⟩)
      (fun t ht htT x => hflow t ⟨ht, htT⟩ x)
  have hfun_eqOn : ∀ s ∈ Set.Ico (0 : ℝ) T_DT, (Φ_fam s : M → M) = fun y : M => Φ s y := by
    intro s hs
    funext y
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hfam0, hΦ0]; rfl
    · exact hfameq s h0 hs.2 y
  refine ⟨T_DT, hDT, le_refl _, Φ_fam, hfam0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x s hs
    exact hfamode s hs.1 hs.2 x
  · intro x
    have heqOn : Set.EqOn (fun s : ℝ => (Φ_fam s : M → M) x) (fun s : ℝ => Φ s x)
        (Set.Ico 0 T_DT) := by
      intro s hs
      change (Φ_fam s : M → M) x = Φ s x
      rw [hfun_eqOn s hs]
    refine (hΦcont0 x).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hDT) heqOn) ?_
    rw [hfun_eqOn 0 ⟨le_rfl, hDT⟩]
  · intro x v
    have hbeq : Set.EqOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M))
        (fun s : ℝ => (TotalSpace.mk' E (Φ s x)
          (mfderiv I I (fun y : M => Φ s y) x v) : TangentBundle I M)) (Set.Ico 0 T_DT) := by
      intro s hs
      change (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M)
        = (TotalSpace.mk' E (Φ s x) (mfderiv I I (fun y : M => Φ s y) x v) : TangentBundle I M)
      rw [hfun_eqOn s hs]
    refine (hΦbundle0 x v).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hDT) hbeq) ?_
    change (TotalSpace.mk' E ((Φ_fam 0 : M → M) x)
        (mfderiv I I (Φ_fam 0 : M → M) x v) : TangentBundle I M)
      = (TotalSpace.mk' E (Φ 0 x) (mfderiv I I (fun y : M => Φ 0 y) x v) : TangentBundle I M)
    rw [hfun_eqOn 0 ⟨le_rfl, hDT⟩]
  · refine hΦorbit_joint.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    change (Φ_fam s : M → M) x = Φ s x
    rw [hfun_eqOn s hs]
  · intro x₀ i
    refine (hΦsection_joint x₀ i).congr ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    change (TotalSpace.mk' E ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x (Integral.Measure.chartBasisVecFiber (I := I) x₀ i x))
        : TangentBundle I M)
      = (TotalSpace.mk' E (Φ s x)
          (mfderiv I I (fun y : M => Φ s y) x
            (Integral.Measure.chartBasisVecFiber (I := I) x₀ i x)) : TangentBundle I M)
    rw [hfun_eqOn s hs]
  · have hIcoSub : Set.Ico (0 : ℝ) T_DT ⊆ Set.Ioo lo hi := fun t ht =>
      ⟨lt_of_lt_of_le hlo ht.1, lt_trans ht.2 hhi⟩
    have hraw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2)
        (Set.Ico (0 : ℝ) T_DT ×ˢ Set.univ) :=
      hΦsm.mono (Set.prod_mono hIcoSub (subset_refl _))
    refine hraw.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    change (Φ_fam s : M → M) x = Φ s x
    rw [hfun_eqOn s hs]

omit [NeZero (Module.finrank ℝ E)] in
theorem conjugating_diffeo_family
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T_DT : ℝ) (hDT : 0 < T_DT)
    (h_smooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T_DT ×ˢ Set.univ)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T_DT ∧ ∃ Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M),
      Φ_fam 0 = _root_.Diffeomorph.refl I M ∞ ∧
      (∀ x : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x)
          (Set.Ici (0 : ℝ)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) x))))) ∧
      (∀ x : M,
        ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) ∧
      (ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (Set.Ico 0 T ×ˢ Set.univ)) ∧
      (∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)),
        ContinuousOn (fun p : ℝ × M =>
          (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
            (mfderiv I I (Φ_fam p.1 : M → M) p.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)) : TangentBundle I M))
          (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) := by
  obtain ⟨T, hT0, hT_le, Φ_fam, h0, hode, hcont0, hbundle0, horbit, hsection, -⟩ :=
    conjugating_diffeo_family_jointsmooth (I := I) g_DT g_bg T_DT hDT h_smooth0
  exact ⟨T, hT0, hT_le, Φ_fam, h0, hode, hcont0, hbundle0, horbit, hsection⟩

end DifferentialGeometry.PDE.RicciFlow
