import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.Hartman
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FromZeroManifoldOrbit
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FromZeroManifoldOrbitUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ForwardIntegralCurveUniqueness


open Set Function Filter Bundle
open scoped Topology Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]

noncomputable def timeWindowBump (a b δ : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((s - (a - 2 * δ)) / δ) *
    Real.smoothTransition (((b + 2 * δ) - s) / δ)

theorem timeWindowBump_contDiff (a b δ : ℝ) : ContDiff ℝ ∞ (timeWindowBump a b δ) := by
  unfold timeWindowBump
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem timeWindowBump_eq_one (a b δ s : ℝ) (hδ : 0 < δ) (hs : s ∈ Set.Ioo (a - δ) (b + δ)) :
    timeWindowBump a b δ s = 1 := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold timeWindowBump
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hδ]; linarith
  · rw [le_div_iff₀ hδ]; linarith

theorem timeWindowBump_mem_Icc_of_ne_zero (a b δ s : ℝ) (hδ : 0 < δ)
    (hs : timeWindowBump a b δ s ≠ 0) : s ∈ Set.Icc (a - 2 * δ) (b + 2 * δ) := by
  unfold timeWindowBump at hs
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

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompleteSpace E] [CompactSpace M] [FiniteDimensional ℝ E] in
theorem timeWindowBump_section_contMDiff (a b δ : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => timeWindowBump a b δ q.1) :=
  (timeWindowBump_contDiff a b δ).contMDiff.comp contMDiff_fst


omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem smul_tangentBundleSection_contMDiffWithinAt
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


omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem smul_tangentBundleSection_contMDiff
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
    fun q hq => smul_tangentBundleSection_contMDiffWithinAt X η (hηsm.contMDiffOn q hq) (hX q hq)
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


omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem interior_field_global_cutoff_extension_loc
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
  refine ⟨fun s x => timeWindowBump a b δ s • X_DT s x, δ, hδ_pos, ?_, ?_, ?_⟩
  · intro s hs x
    simp only [timeWindowBump_eq_one a b δ s hδ_pos hs, one_smul]
  · have hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => timeWindowBump a b δ q.1) := timeWindowBump_section_contMDiff a b δ
    have htsupp : tsupport (fun q : ℝ × M => timeWindowBump a b δ q.1) ⊆
        Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
      have hclosed : IsClosed (Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M)) :=
        isClosed_Icc.prod isClosed_univ
      have hsupp_sub : Function.support (fun q : ℝ × M => timeWindowBump a b δ q.1) ⊆
          Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M) := by
        intro q hq
        rw [Function.mem_support] at hq
        exact ⟨timeWindowBump_mem_Icc_of_ne_zero a b δ q.1 hδ_pos hq, Set.mem_univ _⟩
      refine (closure_minimal hsupp_sub hclosed).trans ?_
      refine Set.prod_mono (fun x hx => ?_) (subset_refl _)
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact smul_tangentBundleSection_contMDiff X_DT (timeWindowBump a b δ) T hηsm hint htsupp
  · have hsm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (timeWindowBump a b δ q.1 • X_DT q.1 q.2) :
            TangentBundle I M)) := by
      have hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => timeWindowBump a b δ q.1) := timeWindowBump_section_contMDiff a b δ
      have htsupp : tsupport (fun q : ℝ × M => timeWindowBump a b δ q.1) ⊆
          Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
        have hclosed : IsClosed (Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M)) :=
          isClosed_Icc.prod isClosed_univ
        have hsupp_sub : Function.support (fun q : ℝ × M => timeWindowBump a b δ q.1) ⊆
            Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M) := by
          intro q hq
          rw [Function.mem_support] at hq
          exact ⟨timeWindowBump_mem_Icc_of_ne_zero a b δ q.1 hδ_pos hq, Set.mem_univ _⟩
        refine (closure_minimal hsupp_sub hclosed).trans ?_
        refine Set.prod_mono (fun x hx => ?_) (subset_refl _)
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact smul_tangentBundleSection_contMDiff X_DT (timeWindowBump a b δ) T hηsm hint htsupp
    exact autonomizedFieldJointC1_of_contMDiff (fun s x => timeWindowBump a b δ s • X_DT s x) hsm


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_timeSlice_of_jointlyContMDiffOn
    {Ψ : M → ℝ → M} {a b : ℝ} (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
      (Set.Ioo a b ×ˢ (Set.univ : Set M))) :
    ContMDiff I I ∞ (fun x : M => Ψ x t) := by
  intro x
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => ((t, y) : ℝ × M)) :=
    contMDiff_const.prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun y : M => ((t, y) : ℝ × M)) Set.univ
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := fun y _ => ⟨ht, Set.mem_univ _⟩
  have hmem : ((t, x) : ℝ × M) ∈ Set.Ioo a b ×ˢ (Set.univ : Set M) := ⟨ht, Set.mem_univ _⟩
  have hcomp : ContMDiffWithinAt I I ∞ (fun y : M => Ψ y t) Set.univ x := by
    have h1 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
        (Set.Ioo a b ×ˢ (Set.univ : Set M)) (t, x) := hsm (t, x) hmem
    exact h1.comp x (hpair x).contMDiffWithinAt hmaps
  exact hcomp.contMDiffAt (by simp)


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem hasMFDerivWithinAt_piecewise_of_agree_at_junction
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (f1 f2 : ℝ → M) {c c' : ℝ} (hcc' : c < c')
    (hagree : f1 c = f2 c)
    (hf1 : ∀ t ∈ Set.Ico (0 : ℝ) c, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f1 (Set.Ici (0:ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f1 t))))
    (hf1c : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f1 (Set.Iic c) c
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))))
    (hf2 : ∀ t ∈ Set.Ico c c', HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f2 (Set.Ici c) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t)))) :
    ∀ t ∈ Set.Ico (0:ℝ) c', HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s => if s ≤ c then f1 s else f2 s) (Set.Ici (0:ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((fun s => if s ≤ c then f1 s else f2 s) t))) := by
  intro t ht
  set g : ℝ → M := fun s => if s ≤ c then f1 s else f2 s with hg
  by_cases htc : t < c
  · have hval : g t = f1 t := by simp only [hg, if_pos (le_of_lt htc)]
    have heq : g =ᶠ[𝓝[Set.Ici (0:ℝ)] t] f1 := by
      have hmem : Set.Iio c ∈ 𝓝[Set.Ici (0:ℝ)] t :=
        nhdsWithin_le_nhds (Iio_mem_nhds htc)
      filter_upwards [hmem] with s hs
      simp only [hg, if_pos (le_of_lt (Set.mem_Iio.mp hs))]
    have hbase := hf1 t ⟨ht.1, htc⟩
    rw [show ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (g t)))
        = ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f1 t))) by rw [hval]]
    exact hbase.congr_of_eventuallyEq heq hval
  · rw [not_lt] at htc
    rcases eq_or_lt_of_le htc with htc_eq | htc_lt
    · have htval : t = c := htc_eq.symm
      have hgc_val : g c = f1 c := by simp only [hg, if_pos (le_refl c)]
      have heqL : g =ᶠ[𝓝[Set.Iic c] c] f1 := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [hg, if_pos (Set.mem_Iic.mp hs)]
      have hL : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Iic c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) :=
        hf1c.congr_of_eventuallyEq heqL hgc_val
      have heqR : g =ᶠ[𝓝[Set.Ici c] c] f2 := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with hsc | hsc
        · simp only [hg, ← hsc, if_pos (le_refl c), hagree]
        · simp only [hg, if_neg (not_le.mpr hsc)]
      have hgc_val2 : g c = f2 c := by rw [hgc_val, hagree]
      have hf2c := hf2 c ⟨le_refl c, hcc'⟩
      have hR : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Ici c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f2 c))) :=
        hf2c.congr_of_eventuallyEq heqR hgc_val2
      have hRval : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Ici c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) := by
        have : (X c (f2 c)) = (X c (f1 c)) := by rw [hagree]
        rw [this] at hR; exact hR
      have hunion : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Iic c ∪ Set.Ici c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) := hL.union hRval
      have huniv : Set.Iic c ∪ Set.Ici c = Set.univ := by
        ext s; simp
      rw [huniv] at hunion
      have hfull : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Ici (0:ℝ)) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) :=
        (hasMFDerivWithinAt_univ.mp hunion).hasMFDerivWithinAt
      rw [htval]
      have hgc2 : (X c (g c)) = (X c (f1 c)) := by rw [hgc_val]
      rw [hgc2]
      exact hfull
    · have hval : g t = f2 t := by simp only [hg, if_neg (not_le.mpr htc_lt)]
      have heq : g =ᶠ[𝓝[Set.Ici (0:ℝ)] t] f2 := by
        have hmem : Set.Ioi c ∈ 𝓝[Set.Ici (0:ℝ)] t :=
          nhdsWithin_le_nhds (Ioi_mem_nhds htc_lt)
        filter_upwards [hmem] with s hs
        simp only [hg, if_neg (not_le.mpr (Set.mem_Ioi.mp hs))]
      have hbase := hf2 t ⟨le_of_lt htc_lt, ht.2⟩
      have hmono : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f2 (Set.Ici (0:ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t))) := by
        apply hbase.mono_of_mem_nhdsWithin
        have : Set.Ioi c ∈ 𝓝[Set.Ici (0:ℝ)] t := nhdsWithin_le_nhds (Ioi_mem_nhds htc_lt)
        filter_upwards [this] with s hs using le_of_lt (Set.mem_Ioi.mp hs)
      rw [show ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (g t)))
          = ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t))) by rw [hval]]
      exact hmono.congr_of_eventuallyEq heq hval


omit [SigmaCompactSpace M] in
theorem exists_local_flow_anchored_at_interior_time
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0:ℝ) T) :
    ∃ (T' : ℝ) (W : M → ℝ → M), 0 < T' ∧ Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (0:ℝ) T ∧
      (∀ p, W p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => W q.2 q.1)
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ (Set.univ : Set M)) ∧
      (∀ p, ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => W p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (W p t)))) := by
  obtain ⟨lo, hlo0, hlot₀⟩ := exists_between ht₀.1
  obtain ⟨hi, ht₀hi, hhiT⟩ := exists_between ht₀.2
  obtain ⟨Xt, δ, hδ, hXt_eq, hXt_cont, hXt_auto⟩ :=
    interior_field_global_cutoff_extension_loc X T hint hlo0 (lt_trans hlot₀ ht₀hi) hhiT
  obtain ⟨Tg, hTg, Φ, hΦ_init, hΦ_smooth, hΦ_bare⟩ :=
    global_flow_jointContMDiffOn_on_closed_manifold Xt hXt_cont t₀
  set T' : ℝ := min (min Tg (t₀ - (lo - δ))) (min ((hi + δ) - t₀) (min t₀ (T - t₀))) with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]
    refine lt_min (lt_min hTg ?_) (lt_min ?_ (lt_min ht₀.1 ?_))
    · have : lo - δ < lo := by linarith
      linarith [hlot₀]
    · have : hi < hi + δ := by linarith
      linarith [ht₀hi]
    · linarith [ht₀.2]
  have hwin_aδ : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (lo - δ) (hi + δ) := by
    apply Set.Ioo_subset_Ioo
    · have : T' ≤ t₀ - (lo - δ) := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    · have : T' ≤ (hi + δ) - t₀ := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
  have hwin_Tg : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (t₀ - Tg) (t₀ + Tg) := by
    apply Set.Ioo_subset_Ioo <;>
      (have : T' ≤ Tg := le_trans (min_le_left _ _) (min_le_left _ _)) <;> linarith
  have hwin_0T : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (0:ℝ) T := by
    apply Set.Ioo_subset_Ioo
    · have : T' ≤ t₀ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have : T' ≤ T - t₀ :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
  have hXtX : ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'), ∀ p, Xt t p = X t p := by
    intro t ht p
    exact hXt_eq t (hwin_aδ ht) p
  refine ⟨T', Φ, hT'_pos, hwin_0T, hΦ_init, ?_, ?_⟩
  · exact (hΦ_smooth).mono (Set.prod_mono hwin_Tg (subset_refl _))
  · intro p t ht
    have hbare := hΦ_bare p t (hwin_Tg ht)
    have heq : Xt t (Φ p t) = X t (Φ p t) := hXtX t ht (Φ p t)
    rw [show ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))
        = ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ p t))) by rw [heq]]
    exact hbare


omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem integralCurves_eqOn_Icc_of_agree_at_left
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Φ Φ' : ℝ → M → M) (x x' : M) {a b : ℝ}
    (hab0 : 0 < a) (hab : a < b) (hbT : b < T)
    (hflow : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x'))))
    (hstart : Φ a x = Φ' a x') :
    ∀ t ∈ Set.Icc a b, Φ t x = Φ' t x' := by
  set lo : ℝ := a / 2 with hlo
  set hi : ℝ := (b + T) / 2 with hhi
  have hlo0 : 0 < lo := by rw [hlo]; linarith
  have hlohi : lo < hi := by rw [hlo, hhi]; linarith
  have hhiT : hi < T := by rw [hhi]; linarith
  obtain ⟨Xt, δ, hδ, hXt_eq, hXt_cont, hXt_auto⟩ :=
    interior_field_global_cutoff_extension_loc X T hint hlo0 hlohi hhiT
  have hlo_a : lo < a := by rw [hlo]; linarith
  have hb_hi : b < hi := by rw [hhi]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo (lo - δ) (hi + δ) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hflowXt : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x))) := by
    intro t ht
    rw [hXt_eq t (hsub ht) (Φ t x)]; exact hflow t ht
  have hflowXt' : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ' t x'))) := by
    intro t ht
    rw [hXt_eq t (hsub ht) (Φ' t x')]; exact hflow' t ht
  exact bare_forward_flow_eqOn_of_jointC1 Xt hXt_auto Φ Φ' x x' hflowXt hflowXt' hstart



omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_uniformRadius_local_flow_cover_of_compact_Icc
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ∃ r : ℝ, 0 < r ∧
      ∀ e ∈ Set.Icc a b, ∃ W : M → ℝ → M,
        Set.Ioo (e - r) (e + r) ⊆ Set.Ioo (0 : ℝ) T ∧
        (∀ p, W p e = p) ∧
        (∀ p, ∀ t ∈ Set.Ioo (e - r) (e + r),
          HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => W p s) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (W p t)))) := by
  classical
  obtain ⟨Xt, δc, hδc, hXt_eq, hXt_cont, _hXt_auto⟩ :=
    interior_field_global_cutoff_extension_loc X T hint (a := a / 2) (b := (b + T) / 2)
      (by linarith) (by linarith) (by linarith)
  set lo : ℝ := a / 2 with hlo_def
  set hi : ℝ := (b + T) / 2 with hhi_def
  have hlo_a : lo < a := by rw [hlo_def]; linarith
  have hb_hi : b < hi := by rw [hhi_def]; linarith
  set Xi : ℝ → ∀ p : ℝ × M, TangentSpace (𝓘(ℝ, ℝ).prod I) p :=
    fun _ p => autonomizedFlowVF Xt p with hXi_def
  have hXi' : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I))
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun q : ℝ × (ℝ × M) =>
        (TotalSpace.mk' (ℝ × E) q.2 (Xi q.1 q.2) :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    (autonomizedFlowVF_section_contMDiff Xt hXt_cont).comp contMDiff_snd
  have hper := fun p₀ : ℝ × M =>
    local_flow_jointSmooth_and_integralCurve (I := 𝓘(ℝ, ℝ).prod I) (M := ℝ × M)
      Xi hXi' 0 p₀
  choose U hUopen hUmem Tnb hTnb_pos Ψ hΨinit _hΨsm hΨbare using hper
  have hKcompact : IsCompact (Set.Icc a b ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  have hKcover : (Set.Icc a b ×ˢ (Set.univ : Set M)) ⊆ ⋃ p : ℝ × M, U p :=
    fun q _ => Set.mem_iUnion.mpr ⟨q, hUmem q⟩
  obtain ⟨S, hScover⟩ := hKcompact.elim_finite_subcover U hUopen hKcover
  set rcap : ℝ := min (min a (T - b)) (min (a - lo) (hi - b)) with hrcap_def
  have hrcap_pos : 0 < rcap := by
    rw [hrcap_def]
    exact lt_min (lt_min ha (by linarith))
      (lt_min (by linarith) (by linarith))
  have hrcap_le_a : rcap ≤ a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrcap_le_Tb : rcap ≤ T - b := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrcap_le_alo : rcap ≤ a - lo := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrcap_le_hib : rcap ≤ hi - b := le_trans (min_le_right _ _) (min_le_right _ _)
  by_cases hSne : S.Nonempty
  · set Tmin : ℝ := S.inf' hSne Tnb with hTmin_def
    have hTmin_pos : 0 < Tmin := by
      rw [hTmin_def, Finset.lt_inf'_iff]; exact fun p _ => hTnb_pos p
    have hTmin_le : ∀ p ∈ S, Tmin ≤ Tnb p := fun p hp => Finset.inf'_le _ hp
    set r : ℝ := min rcap Tmin with hr_def
    have hr_pos : 0 < r := lt_min hrcap_pos hTmin_pos
    have hr_le_cap : r ≤ rcap := min_le_left _ _
    have hr_le_Tmin : r ≤ Tmin := min_le_right _ _
    have hr_le_a : r ≤ a := le_trans hr_le_cap hrcap_le_a
    have hr_le_Tb : r ≤ T - b := le_trans hr_le_cap hrcap_le_Tb
    have hr_le_alo : r ≤ a - lo := le_trans hr_le_cap hrcap_le_alo
    have hr_le_hib : r ≤ hi - b := le_trans hr_le_cap hrcap_le_hib
    refine ⟨r, hr_pos, fun e he => ?_⟩
    have he_a : a ≤ e := he.1
    have he_b : e ≤ b := he.2
    have hsub0T : Set.Ioo (e - r) (e + r) ⊆ Set.Ioo (0 : ℝ) T := by
      apply Set.Ioo_subset_Ioo <;> · linarith
    have hsubAgree : Set.Ioo (e - r) (e + r) ⊆ Set.Ioo (lo - δc) (hi + δc) := by
      apply Set.Ioo_subset_Ioo <;> · linarith
    have hmem : ∀ q : M, ∃ p₀ ∈ S, ((e, q) : ℝ × M) ∈ U p₀ := by
      intro q
      have hmemK : ((e, q) : ℝ × M) ∈ Set.Icc a b ×ˢ (Set.univ : Set M) :=
        ⟨he, Set.mem_univ _⟩
      rcases Set.mem_iUnion₂.mp (hScover hmemK) with ⟨p₀, hp₀S, hp₀U⟩
      exact ⟨p₀, hp₀S, hp₀U⟩
    choose p0 hp0S hp0U using hmem
    set c : M → ℝ → (ℝ × M) := fun q s => Ψ (p0 q) (e, q) s with hc_def
    have hwin : ∀ q : M, ∀ τ ∈ Set.Ioo (-r) r,
        τ ∈ Set.Ioo (0 - Tnb (p0 q)) (0 + Tnb (p0 q)) := by
      intro q τ hτ
      have hle : r ≤ Tnb (p0 q) := le_trans hr_le_Tmin (hTmin_le _ (hp0S q))
      exact ⟨by simp only [zero_sub]; linarith [hτ.1],
        by simp only [zero_add]; linarith [hτ.2]⟩
    have hgbare : ∀ q : M, ∀ s ∈ Set.Ioo (-r) r,
        HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (c q) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF Xt (c q s))) := by
      intro q s hs
      exact hΨbare (p0 q) (e, q) (hp0U q) s (hwin q s hs)
    have htimeid : ∀ q : M, ∀ s ∈ Set.Ioo (-r) r, (c q s).1 = e + s := by
      intro q
      have hfst : ∀ s ∈ Set.Ioo (-r) r, HasDerivAt (fun u => (c q u).1) 1 s :=
        fun s hs => autonomizedFlow_fst_hasDerivAt Xt (c q) s (hgbare q s hs)
      have hval : (c q 0).1 = e := by
        simp only [hc_def]
        rw [hΨinit (p0 q) (e, q) (hp0U q)]
      have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr_pos⟩
      have hconst : ∀ s ∈ Set.Ioo (-r) r,
          HasDerivAt (fun u => (c q u).1 - u) (0 : ℝ) s := by
        intro u hu; simpa using (hfst u hu).sub (hasDerivAt_id u)
      intro s hs
      have hkey : (fun u => (c q u).1 - u) s = (fun u => (c q u).1 - u) 0 := by
        apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Ioo (-r) r)
          (f := fun u => (c q u).1 - u) (s := Set.Ioo (-r) r)
        · intro u hu; exact (hconst u hu).differentiableAt.differentiableWithinAt
        · intro u hu
          have huniq : UniqueDiffWithinAt ℝ (Set.Ioo (-r) r) u :=
            isOpen_Ioo.uniqueDiffWithinAt hu
          have hfd : HasFDerivWithinAt (fun u => (c q u).1 - u)
              (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : ℝ)) (Set.Ioo (-r) r) u :=
            ((hconst u hu).hasDerivWithinAt).hasFDerivWithinAt
          rw [hfd.fderivWithin huniq]; ext1; simp
        · exact hs
        · exact h0mem
      simp only at hkey; rw [hval] at hkey; linarith
    have hXtX : ∀ q : M, ∀ s ∈ Set.Ioo (e - r) (e + r), ∀ x : M, Xt s x = X s x :=
      fun q s hs x => hXt_eq s (hsubAgree hs) x
    refine ⟨fun q t => (c q (t - e)).2, hsub0T, ?_, ?_⟩
    · intro q
      simp only [hc_def, sub_self]
      exact congrArg Prod.snd (hΨinit (p0 q) (e, q) (hp0U q))
    · intro q t ht
      have hte : (t - e) ∈ Set.Ioo (-r) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hsnd := autonomizedFlow_snd_hasMFDerivAt Xt (c q) (t - e) (hgbare q (t - e) hte)
      have htime : (c q (t - e)).1 = t := by rw [htimeid q (t - e) hte]; ring
      rw [htime] at hsnd
      have hXeq : Xt t ((c q (t - e)).2) = X t ((c q (t - e)).2) :=
        hXtX q t ht ((c q (t - e)).2)
      rw [hXeq] at hsnd
      have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s - e) t (1 : ℝ →L[ℝ] ℝ) := by
        rw [hasMFDerivAt_iff_hasFDerivAt]
        have h2 := ((hasDerivAt_id t).sub_const e).hasFDerivAt
        have he1 : (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) = (1 : ℝ →L[ℝ] ℝ) := by
          ext1; simp
        rwa [he1] at h2
      have hcomp := hsnd.comp t hshift
      have hfun : ((fun s => (c q s).2) ∘ fun s : ℝ => s - e)
          = (fun s => (c q (s - e)).2) := rfl
      rw [hfun] at hcomp
      simpa using hcomp
  · refine ⟨rcap, hrcap_pos, fun e he => ?_⟩
    have hMempty : IsEmpty M := by
      rw [isEmpty_iff]
      intro q
      have hmemK : ((e, q) : ℝ × M) ∈ Set.Icc a b ×ˢ (Set.univ : Set M) :=
        ⟨he, Set.mem_univ _⟩
      rcases Set.mem_iUnion₂.mp (hScover hmemK) with ⟨p₀, hp₀S, _⟩
      exact hSne ⟨p₀, hp₀S⟩
    refine ⟨fun p _ => p, ?_, fun p => (hMempty.false p).elim,
      fun p => (hMempty.false p).elim⟩
    have he_a : a ≤ e := he.1
    have he_b : e ≤ b := he.2
    apply Set.Ioo_subset_Ioo <;> · linarith

private def existsForwardIntegralCurveUpTo (X : ℝ → ∀ x : M, TangentSpace I x) (x : M) (s : ℝ) : Prop :=
  ∃ c : ℝ → M, c 0 = x ∧
    ∀ t ∈ Set.Ico (0:ℝ) s,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (Set.Ici (0:ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (c t)))


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem existsForwardIntegralCurveUpTo_mono (X : ℝ → ∀ x : M, TangentSpace I x) (x : M) {s s' : ℝ}
    (hss : s' ≤ s) (h : existsForwardIntegralCurveUpTo X x s) : existsForwardIntegralCurveUpTo X x s' := by
  obtain ⟨c, hc0, hc⟩ := h
  exact ⟨c, hc0, fun t ht => hc t ⟨ht.1, lt_of_lt_of_le ht.2 hss⟩⟩


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem existsForwardIntegralCurveUpTo_extend
    (X : ℝ → ∀ x : M, TangentSpace I x) (x : M) {s e ρ : ℝ}
    (he0 : 0 < e) (hes : e < s) (hρ : 0 < ρ)
    (hR : existsForwardIntegralCurveUpTo X x s)
    (W : M → ℝ → M)
    (hW : ∀ p, ∀ t ∈ Set.Ioo (e - ρ) (e + ρ),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u => W p u) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (W p t))))
    (hWinit : ∀ p, W p e = p) :
    existsForwardIntegralCurveUpTo X x (e + ρ) := by
  classical
  obtain ⟨c, hc0, hc⟩ := hR
  set f2 : ℝ → M := fun u => W (c e) u with hf2def
  refine ⟨fun t => if t ≤ e then c t else f2 t, ?_, ?_⟩
  · simp only [if_pos (le_of_lt he0)]; exact hc0
  · have hf1 : ∀ t ∈ Set.Ico (0:ℝ) e, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (Set.Ici (0:ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (c t))) :=
      fun t ht => hc t ⟨ht.1, lt_trans ht.2 hes⟩
    have hce_two : HasMFDerivAt 𝓘(ℝ, ℝ) I c e ((1 : ℝ →L[ℝ] ℝ).smulRight (X e (c e))) :=
      (hc e ⟨le_of_lt he0, hes⟩).hasMFDerivAt (Ici_mem_nhds he0)
    have hf1c : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (Set.Iic e) e
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X e (c e))) := hce_two.hasMFDerivWithinAt
    have hf2 : ∀ t ∈ Set.Ico e (e + ρ), HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f2 (Set.Ici e) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t))) := by
      intro t ht
      have htw : t ∈ Set.Ioo (e - ρ) (e + ρ) := ⟨by linarith [ht.1], ht.2⟩
      exact (hW (c e) t htw).hasMFDerivWithinAt
    have hagree : c e = f2 e := by rw [hf2def]; exact (hWinit (c e)).symm
    exact hasMFDerivWithinAt_piecewise_of_agree_at_junction X c f2 (c := e) (c' := e + ρ)
      (by linarith) hagree hf1 hf1c hf2


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem existsForwardIntegralCurveUpTo_chain
    (X : ℝ → ∀ x : M, TangentSpace I x) (x : M)
    {δ β r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hRδ : existsForwardIntegralCurveUpTo X x δ)
    (hwin : ∀ e ∈ Set.Icc (δ/2) β, ∃ W : M → ℝ → M,
        (∀ p, W p e = p) ∧
        (∀ p, ∀ t ∈ Set.Ioo (e - r) (e + r),
          HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => W p s) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (W p t))))) :
    existsForwardIntegralCurveUpTo X x β := by
  classical
  set step : ℝ := r / 4 with hstep
  have hstep_pos : 0 < step := by rw [hstep]; positivity
  have key : ∀ n : ℕ, existsForwardIntegralCurveUpTo X x (min (δ + n * step) β) := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, add_zero]
        exact existsForwardIntegralCurveUpTo_mono X x (min_le_left _ _) hRδ
    | succ k ih =>
        set s : ℝ := min (δ + (k:ℝ) * step) β with hs
        by_cases hsβ : δ + (k:ℝ) * step < β
        · have hs_eq : s = δ + (k:ℝ) * step := by rw [hs, min_eq_left (le_of_lt hsβ)]
          have hs_lt_β : s < β := by rw [hs_eq]; exact hsβ
          have hs_ge_δ : δ ≤ s := by
            rw [hs_eq]
            have hk : (0:ℝ) ≤ (k:ℝ) * step := mul_nonneg (Nat.cast_nonneg k) hstep_pos.le
            linarith
          have hs_pos : 0 < s := lt_of_lt_of_le hδ hs_ge_δ
          set m : ℝ := min step (s/2) with hm
          have hm_pos : 0 < m := lt_min hstep_pos (by linarith)
          set e : ℝ := s - m with he
          have he0 : 0 < e := by
            rw [he]; have : m ≤ s/2 := min_le_right _ _; linarith
          have hes : e < s := by rw [he]; linarith
          have he_ge : δ/2 ≤ e := by
            have hms : m ≤ s/2 := min_le_right _ _
            have hhalf : s/2 ≤ e := by rw [he]; linarith
            have : δ/2 ≤ s/2 := by linarith
            linarith
          have he_le : e ≤ β := le_of_lt (lt_trans hes hs_lt_β)
          obtain ⟨W, hWinit, hWbare⟩ := hwin e ⟨he_ge, he_le⟩
          have hext : existsForwardIntegralCurveUpTo X x (e + r) :=
            existsForwardIntegralCurveUpTo_extend X x he0 hes hr ih W hWbare hWinit
          have hmr : m ≤ step := min_le_left _ _
          have hge : δ + ((k:ℝ)+1) * step ≤ e + r := by
            have hee : e + r = s - m + r := by rw [he]
            rw [hee, hs_eq]
            have : step ≤ r := by rw [hstep]; linarith
            nlinarith [hmr, hstep_pos.le, hr]
          have hbig : min (δ + ((k+1:ℕ):ℝ) * step) β ≤ e + r := by
            push_cast
            calc min (δ + ((k:ℝ)+1) * step) β ≤ δ + ((k:ℝ)+1) * step := min_le_left _ _
              _ ≤ e + r := hge
          exact existsForwardIntegralCurveUpTo_mono X x hbig hext
        · have hsβ' : β ≤ δ + (k:ℝ) * step := not_lt.mp hsβ
          have hs_eq : s = β := by rw [hs, min_eq_right hsβ']
          have h1 : β ≤ δ + ((k:ℝ)+1) * step := by nlinarith [hstep_pos.le]
          have heq2 : min (δ + ((k+1:ℕ):ℝ) * step) β = β := by
            rw [min_eq_right]; push_cast; nlinarith [hstep_pos.le, h1]
          rw [heq2]
          rw [hs_eq] at ih
          exact ih
  obtain ⟨n, hn⟩ := exists_nat_ge ((β - δ) / step)
  have hn' : β ≤ δ + (n:ℝ) * step := by
    rw [div_le_iff₀ hstep_pos] at hn
    nlinarith [hn]
  have hkey := key n
  rwa [min_eq_right hn'] at hkey
end DifferentialGeometry.PDE.RicciFlow.ODE
