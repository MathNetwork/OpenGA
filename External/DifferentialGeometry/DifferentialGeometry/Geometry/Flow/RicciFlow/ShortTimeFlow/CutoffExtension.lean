import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold


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

namespace CutoffExtensionAux

noncomputable def cutoffEta (a b δ : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((s - (a - 2 * δ)) / δ) *
    Real.smoothTransition (((b + 2 * δ) - s) / δ)

theorem cutoffEta_contDiff (a b δ : ℝ) : ContDiff ℝ ∞ (cutoffEta a b δ) := by
  unfold cutoffEta
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem cutoffEta_eq_one (a b δ s : ℝ) (hδ : 0 < δ) (hs : s ∈ Set.Ioo (a - δ) (b + δ)) :
    cutoffEta a b δ s = 1 := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold cutoffEta
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hδ]; linarith
  · rw [le_div_iff₀ hδ]; linarith

theorem cutoffEta_mem_Icc_of_ne_zero (a b δ s : ℝ) (hδ : 0 < δ)
    (hs : cutoffEta a b δ s ≠ 0) : s ∈ Set.Icc (a - 2 * δ) (b + 2 * δ) := by
  unfold cutoffEta at hs
  refine ⟨?_, ?_⟩
  · by_contra h
    have hlt : s < a - 2 * δ := lt_of_not_ge h
    have hnum : s - (a - 2 * δ) < 0 := by linarith
    have hle : (s - (a - 2 * δ)) / δ ≤ 0 := (div_neg_of_neg_of_pos hnum hδ).le
    rw [Real.smoothTransition.zero_of_nonpos hle, zero_mul] at hs
    exact hs rfl
  · by_contra h
    have hlt : b + 2 * δ < s := lt_of_not_ge h
    have hnum : (b + 2 * δ) - s < 0 := by linarith
    have hle : ((b + 2 * δ) - s) / δ ≤ 0 := (div_neg_of_neg_of_pos hnum hδ).le
    rw [Real.smoothTransition.zero_of_nonpos hle, mul_zero] at hs
    exact hs rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

omit [IsManifold I ∞ M] in
theorem cutoffEta_section_contMDiff (a b δ : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => cutoffEta a b δ q.1) :=
  (cutoffEta_contDiff a b δ).contMDiff.comp contMDiff_fst

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

theorem smul_tangentMap_cmdwa
    (X : ℝ → ∀ x : M, TangentSpace I x) (η : ℝ → ℝ)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hη : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => η q.1) u q₀)
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M))
      u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hη.smul hXfib
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).2 (η x.1) (X x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).2 (η q₀.1) (X q₀.1 q₀.2)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem smul_tangentMap_global
    (X : ℝ → ∀ x : M, TangentSpace I x) (η : ℝ → ℝ) (T : ℝ)
    (hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => η q.1))
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (htsupp : tsupport (fun q : ℝ × M => η q.1) ⊆
      Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M)) := by
  set U : Set (ℝ × M) := Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) with hU
  set V : Set (ℝ × M) := (tsupport (fun q : ℝ × M => η q.1))ᶜ with hV
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hVopen : IsOpen V := (isClosed_tsupport _).isOpen_compl
  have honU : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M)) U :=
    fun q hq => smul_tangentMap_cmdwa X η (hηsm.contMDiffOn q hq) (hX q hq)
  have honV : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M)) V := by
    have hzero : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (0 : TangentSpace I q.2) : TangentBundle I M)) V :=
      ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp
        contMDiff_snd).contMDiffOn
    refine hzero.congr ?_
    intro q hq
    have hη0 : η q.1 = 0 := by
      have hnotsupp : q ∉ Function.support (fun q : ℝ × M => η q.1) :=
        fun hc => hq (subset_tsupport _ hc)
      simpa [Function.mem_support] using hnotsupp
    simp [hη0]
  have hcover : U ∪ V = Set.univ := by
    refine Set.eq_univ_of_forall (fun q => ?_)
    by_cases h : q ∈ tsupport (fun q : ℝ × M => η q.1)
    · exact Or.inl (htsupp h)
    · exact Or.inr h
  exact contMDiff_of_contMDiffOn_union_of_isOpen honU honV hcover hUopen hVopen

end CutoffExtensionAux

open CutoffExtensionAux in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem interior_field_global_cutoff_extension
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {a b : ℝ} (hab : 0 < a) (_hab' : a < b) (hbT : b < T) :
    ∃ (Xt : ℝ → ∀ x : M, TangentSpace I x) (δ : ℝ), 0 < δ ∧
      (∀ s ∈ Set.Ioo (a - δ) (b + δ), ∀ x : M, Xt s x = X_DT s x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)) ∧
      AutonomizedFieldJointC1 (I := I) Xt := by
  set δ : ℝ := min a (T - b) / 3 with hδ_def
  have hTb : 0 < T - b := by linarith
  have hmin_pos : 0 < min a (T - b) := lt_min hab hTb
  have hle_a : min a (T - b) ≤ a := min_le_left _ _
  have hle_Tb : min a (T - b) ≤ T - b := min_le_right _ _
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hlo : 0 < a - 2 * δ := by
    rw [hδ_def]
    have : 2 * (min a (T - b) / 3) ≤ 2 * (a / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hhi : b + 2 * δ < T := by
    rw [hδ_def]
    have : 2 * (min a (T - b) / 3) ≤ 2 * ((T - b) / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  refine ⟨fun s x => cutoffEta a b δ s • X_DT s x, δ, hδ_pos, ?_, ?_, ?_⟩
  · intro s hs x
    simp only [cutoffEta_eq_one a b δ s hδ_pos hs, one_smul]
  · have hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => cutoffEta a b δ q.1) := cutoffEta_section_contMDiff a b δ
    have htsupp : tsupport (fun q : ℝ × M => cutoffEta a b δ q.1) ⊆
        Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
      have hclosed : IsClosed (Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M)) :=
        isClosed_Icc.prod isClosed_univ
      have hsupp_sub : Function.support (fun q : ℝ × M => cutoffEta a b δ q.1) ⊆
          Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M) := by
        intro q hq
        rw [Function.mem_support] at hq
        exact ⟨cutoffEta_mem_Icc_of_ne_zero a b δ q.1 hδ_pos hq, Set.mem_univ _⟩
      refine (closure_minimal hsupp_sub hclosed).trans ?_
      refine Set.prod_mono (fun x hx => ?_) (subset_refl _)
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact smul_tangentMap_global X_DT (cutoffEta a b δ) T hηsm hint htsupp
  · have hsm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (cutoffEta a b δ q.1 • X_DT q.1 q.2) :
            TangentBundle I M)) := by
      have hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => cutoffEta a b δ q.1) := cutoffEta_section_contMDiff a b δ
      have htsupp : tsupport (fun q : ℝ × M => cutoffEta a b δ q.1) ⊆
          Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
        have hclosed : IsClosed (Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M)) :=
          isClosed_Icc.prod isClosed_univ
        have hsupp_sub : Function.support (fun q : ℝ × M => cutoffEta a b δ q.1) ⊆
            Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M) := by
          intro q hq
          rw [Function.mem_support] at hq
          exact ⟨cutoffEta_mem_Icc_of_ne_zero a b δ q.1 hδ_pos hq, Set.mem_univ _⟩
        refine (closure_minimal hsupp_sub hclosed).trans ?_
        refine Set.prod_mono (fun x hx => ?_) (subset_refl _)
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact smul_tangentMap_global X_DT (cutoffEta a b δ) T hηsm hint htsupp
    exact autonomizedFieldJointC1_of_contMDiff (fun s x => cutoffEta a b δ s • X_DT s x) hsm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem deturck_vf_autonomized_c1
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M))) :
    AutonomizedFieldJointC1 (I := I) Xt :=
  autonomizedFieldJointC1_of_contMDiff Xt hXt

end DifferentialGeometry.PDE.RicciFlow
