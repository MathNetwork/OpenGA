import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantCommutationCurvature
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivAlong_locality
    (g : SmoothRiemannianMetric I M) (γ₁ γ₂ : ℝ → M)
    (V₁ : ∀ s, TangentSpace I (γ₁ s)) (V₂ : ∀ s, TangentSpace I (γ₂ s)) (t : ℝ)
    (hfoot : γ₁ t = γ₂ t)
    (hγ₁ : ContinuousAt γ₁ t)
    (htot : (fun s => (TotalSpace.mk' E (γ₁ s) (V₁ s) : TangentBundle I M)) =ᶠ[𝓝 t]
      (fun s => (TotalSpace.mk' E (γ₂ s) (V₂ s) : TangentBundle I M))) :
    covDerivAlong (I := I) g γ₁ V₁ t = covDerivAlong (I := I) g γ₂ V₂ t := by
  set α : M := γ₁ t with hα
  have hbase₀ : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hpre : γ₁ ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 t :=
    hγ₁.preimage_mem_nhds (hopen.mem_nhds hbase₀)

  have hcurve_eq : γ₁ =ᶠ[𝓝 t] γ₂ := by
    filter_upwards [htot] with s hs
    exact congrArg (fun p : TangentBundle I M => p.proj) hs
  have hcurve : chartCurve (I := I) α γ₁ =ᶠ[𝓝 t] chartCurve (I := I) α γ₂ := by
    filter_upwards [hcurve_eq] with s hs
    rw [chartCurve_def, chartCurve_def, hs]

  have hrep : chartRepAt (I := I) γ₁ V₁ t =ᶠ[𝓝 t] chartRepAt (I := I) γ₂ V₂ t := by
    have hpre₂ : γ₂ ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 t := by
      filter_upwards [hpre, hcurve_eq] with s hs hseq
      simp only [Set.mem_preimage] at hs ⊢; rwa [← hseq]
    filter_upwards [htot, hpre, hpre₂] with s hs hsmem hsmem₂
    simp only [Set.mem_preimage] at hsmem hsmem₂
    have h1 : chartRepAt (I := I) γ₁ V₁ t s
        = ((trivializationAt E (TangentSpace I) α) (TotalSpace.mk' E (γ₁ s) (V₁ s))).2 := by
      rw [chartRepAt_apply, ← hα,
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_apply (R := ℝ),
        (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hsmem]
    have h2 : chartRepAt (I := I) γ₂ V₂ t s
        = ((trivializationAt E (TangentSpace I) α) (TotalSpace.mk' E (γ₂ s) (V₂ s))).2 := by
      rw [chartRepAt_apply, ← hfoot,
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_apply (R := ℝ),
        (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hsmem₂]
    rw [h1, h2, hs]
  rw [covDerivAlong_def, covDerivAlong_def, chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [← hfoot, ← hα]
  congr 1
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hcurve.deriv_eq, hcurve.eq_of_nhds]

private noncomputable def flowTimeRetract (t δ w : ℝ) (s : ℝ) : ℝ :=
  t + (s - t) * (1 - Real.smoothTransition ((s - t - δ) / w))
    * (1 - Real.smoothTransition ((t - δ - s) / w))

private lemma flowTimeRetract_contDiff (t δ w : ℝ) :
    ContDiff ℝ ∞ (flowTimeRetract t δ w) := by
  unfold flowTimeRetract
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => (1 : ℝ) - Real.smoothTransition ((s - t - δ) / w)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  have h2 : ContDiff ℝ ∞ (fun s : ℝ => (1 : ℝ) - Real.smoothTransition ((t - δ - s) / w)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  exact contDiff_const.add (((contDiff_id.sub contDiff_const).mul h1).mul h2)

private lemma flowTimeRetract_eq_self (t δ w : ℝ) (hw : 0 < w) {s : ℝ}
    (hs : s ∈ Set.Icc (t - δ) (t + δ)) :
    flowTimeRetract t δ w s = s := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold flowTimeRetract
  have hL : Real.smoothTransition ((s - t - δ) / w) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)
  have hR : Real.smoothTransition ((t - δ - s) / w) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)
  rw [hL, hR]; ring

private lemma flowTimeRetract_abs_le (t δ w : ℝ) (hδ : 0 ≤ δ) (hw : 0 < w) (s : ℝ) :
    |flowTimeRetract t δ w s - t| ≤ δ + w := by
  unfold flowTimeRetract
  rw [add_sub_cancel_left]
  by_cases hin : s ∈ Set.Icc (t - δ - w) (t + δ + w)
  · obtain ⟨hin1, hin2⟩ := hin
    have hf1 : (1 : ℝ) - Real.smoothTransition ((s - t - δ) / w) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [Real.smoothTransition.le_one ((s - t - δ) / w)],
        by linarith [Real.smoothTransition.nonneg ((s - t - δ) / w)]⟩
    have hf2 : (1 : ℝ) - Real.smoothTransition ((t - δ - s) / w) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [Real.smoothTransition.le_one ((t - δ - s) / w)],
        by linarith [Real.smoothTransition.nonneg ((t - δ - s) / w)]⟩
    rw [abs_mul, abs_mul]
    have hb1 : |(1 : ℝ) - Real.smoothTransition ((s - t - δ) / w)| ≤ 1 := by
      rw [abs_of_nonneg hf1.1]; exact hf1.2
    have hb2 : |(1 : ℝ) - Real.smoothTransition ((t - δ - s) / w)| ≤ 1 := by
      rw [abs_of_nonneg hf2.1]; exact hf2.2
    have hsdt : |s - t| ≤ δ + w := by rw [abs_le]; constructor <;> linarith
    calc |s - t| * |(1 : ℝ) - Real.smoothTransition ((s - t - δ) / w)|
            * |(1 : ℝ) - Real.smoothTransition ((t - δ - s) / w)|
        ≤ (δ + w) * 1 * 1 := by
          apply mul_le_mul (mul_le_mul hsdt hb1 (abs_nonneg _) (by linarith)) hb2 (abs_nonneg _)
          positivity
      _ = δ + w := by ring
  · rw [Set.mem_Icc, not_and_or] at hin
    have hzero : (s - t) * (1 - Real.smoothTransition ((s - t - δ) / w))
        * (1 - Real.smoothTransition ((t - δ - s) / w)) = 0 := by
      rcases hin with h | h
      · have hlt : s < t - δ - w := lt_of_not_ge h
        have : Real.smoothTransition ((t - δ - s) / w) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [le_div_iff₀ hw]; linarith
        rw [this]; ring
      · have hlt : t + δ + w < s := lt_of_not_ge h
        have : Real.smoothTransition ((s - t - δ) / w) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [le_div_iff₀ hw]; linarith
        rw [this]; ring
    rw [hzero, abs_zero]; linarith

private lemma flowTimeRetract_mem_Ioo (t T δ w : ℝ) (hδ : 0 ≤ δ) (hw : 0 < w)
    (hlo : 0 < t - (δ + w)) (hhi : t + (δ + w) < T) (s : ℝ) :
    flowTimeRetract t δ w s ∈ Set.Ioo (0 : ℝ) T := by
  have h := flowTimeRetract_abs_le t δ w hδ hw s
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private noncomputable def chartLineCurve (x : M) (v : TangentSpace I x) (δ : ℝ) : ℝ → M :=
  fun r => (extChartAt I x).symm (extChartAt I x x + (reparam δ r) • (show E from v))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma exists_chartLineCurve_global
    (x : M) (v : TangentSpace I x) :
    ∃ δ : ℝ, 0 < δ ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ (chartLineCurve (I := I) x v δ) ∧
      chartLineCurve (I := I) x v δ 0 = x ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) I (chartLineCurve (I := I) x v δ) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  classical
  set φ : E := extChartAt I x x with hφ
  set vE : E := (show E from v) with hvE
  set L : ℝ → E := fun t : ℝ => φ + t • vE with hL
  have hLcont : Continuous L := by fun_prop
  have hL0 : L 0 = φ := by simp [hL]
  have htgt : (extChartAt I x).target ∈ 𝓝 φ := by
    rw [hφ]; exact extChartAt_target_mem_nhds x
  have hpre : L ⁻¹' (extChartAt I x).target ∈ 𝓝 (0 : ℝ) := by
    have := hLcont.continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, hL0] at this
    exact this htgt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · have hreparam : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r : ℝ => φ + (reparam ε r) • vE) := by
      rw [contMDiff_iff_contDiff]
      have : ContDiff ℝ ∞ (fun r : ℝ => φ + (reparam ε r) • vE) :=
        contDiff_const.add ((contDiff_reparam ε).smul contDiff_const)
      simpa using this
    have hmaps : ∀ r : ℝ, (fun r : ℝ => φ + (reparam ε r) • vE) r ∈ (extChartAt I x).target := by
      intro r
      have hin : (reparam ε r) ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact abs_reparam_lt ε hε r
      have := hball hin
      simpa [hL] using this
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (extChartAt I x).target :=
      contMDiffOn_extChartAt_symm (n := (∞ : WithTop ℕ∞)) x
    have hcomp := hsymm.comp_contMDiff hreparam hmaps
    simpa [chartLineCurve, Function.comp_def, hφ] using hcomp
  · simp [chartLineCurve, reparam_zero]
  · have hLine : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => φ + (reparam ε r) • vE) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight vE) := by
      rw [hasMFDerivAt_iff_hasFDerivAt]
      have hrd : HasDerivAt (reparam ε) 1 0 := hasDerivAt_reparam_zero ε hε
      have hsmul : HasDerivAt (fun r : ℝ => (reparam ε r) • vE) ((1 : ℝ) • vE) 0 := by
        have := hrd.smul_const vE
        simpa using this
      have hadd0 : HasDerivAt (fun r : ℝ => φ + (reparam ε r) • vE) (0 + (1 : ℝ) • vE) 0 :=
        (hasDerivAt_const (0 : ℝ) φ).add hsmul
      rw [zero_add, one_smul] at hadd0
      rw [hasDerivAt_iff_hasFDerivAt] at hadd0
      exact hadd0
    have hsymmD : HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I x).symm φ
        (ContinuousLinearMap.id ℝ E) := by
      have hmem : φ ∈ (extChartAt I x).target := by rw [hφ]; exact mem_extChartAt_target x
      have hdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ := by
        have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x) hmem
        rwa [I.range_eq_univ] at this
      have heq : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm univ φ
          = ContinuousLinearMap.id ℝ E := by
        rw [hφ, ← I.range_eq_univ]
        exact mfderivWithin_range_extChartAt_symm
      have hwd : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ
          (ContinuousLinearMap.id ℝ E) := heq ▸ hdiff.hasMFDerivWithinAt
      rw [← hasMFDerivWithinAt_univ]
      exact hwd
    have hLine0 : (fun r : ℝ => φ + (reparam ε r) • vE) 0 = φ := by
      simp [reparam_zero]
    have hcomp := (hLine0.symm ▸ hsymmD).comp 0 hLine
    rw [Function.comp_def] at hcomp
    have hcomp' : HasMFDerivAt 𝓘(ℝ, ℝ) I
        (fun r : ℝ => (extChartAt I x).symm (φ + (reparam ε r) • vE)) 0
        ((ContinuousLinearMap.id ℝ E).comp ((1 : ℝ →L[ℝ] ℝ).smulRight vE)) := hcomp
    rw [ContinuousLinearMap.id_comp] at hcomp'
    simpa [chartLineCurve, hφ] using hcomp'

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem conjugating_flow_covariant_variational_eq
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    covDerivAlong (I := I) (g_DT t) (fun s : ℝ => (Φ_fam s : M → M) x)
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) t =
      -((LeviCivita (I := I) (g_DT t))
        (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y) ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)) := by
  classical
  obtain ⟨ht0, htT⟩ := ht

  obtain ⟨δc, hδc, hcc_smooth, hcc0, hcc_vel⟩ := exists_chartLineCurve_global (I := I) x v
  set cc : ℝ → M := chartLineCurve (I := I) x v δc with hcc_def
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  have hcc_mderiv : mfderiv 𝓘(ℝ, ℝ) I cc 0 (1 : ℝ) = v := by
    rw [hcc_vel.mfderiv]
    change (1 : ℝ →L[ℝ] ℝ) 1 • v = v
    rw [ContinuousLinearMap.one_apply, one_smul]
  have hcc_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I cc 0 :=
    hcc_smooth.contMDiffAt.mdifferentiableAt (by simp)

  set η : ℝ := min t (T - t) / 4 with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]; have : 0 < min t (T - t) := lt_min ht0 (by linarith); positivity
  have hsum_lt : η + η < min t (T - t) := by
    rw [hη_def]; have : 0 < min t (T - t) := lt_min ht0 (by linarith); linarith
  have hlo : 0 < t - (η + η) := by
    have := lt_of_lt_of_le hsum_lt (min_le_left _ _); linarith
  have hhi : t + (η + η) < T := by
    have := lt_of_lt_of_le hsum_lt (min_le_right _ _); linarith
  set ρ : ℝ → ℝ := flowTimeRetract t η η with hρ_def
  have hρ_mem : ∀ s : ℝ, ρ s ∈ Set.Ioo (0 : ℝ) T := fun s =>
    flowTimeRetract_mem_Ioo t T η η (le_of_lt hη_pos) hη_pos hlo hhi s
  have hρ_eq : ∀ s ∈ Set.Icc (t - η) (t + η), ρ s = s := fun s hs =>
    flowTimeRetract_eq_self t η η hη_pos hs
  have hρt : ρ t = t := hρ_eq t ⟨by linarith, by linarith⟩
  have hρ_nhds : (fun s : ℝ => ρ s) =ᶠ[𝓝 t] (fun s : ℝ => s) := by
    have hmem : Set.Icc (t - η) (t + η) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with s hs using hρ_eq s hs
  have hρ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := by
    rw [contMDiff_iff_contDiff]; exact flowTimeRetract_contDiff t η η

  set Gg : ℝ → ℝ → M := fun s r => (Φ_fam (ρ s) : M → M) (cc r) with hGg_def

  have hGg_var : IsSmoothVariation (I := I) Gg := by
    have hρ8 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) ρ := hρ_smooth.of_le h8le
    have hcc8 : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) cc := hcc_smooth.of_le h8le
    have hinner : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun p : ℝ × ℝ => (ρ p.1, cc p.2)) :=
      (hρ8.comp contMDiff_fst).prodMk (hcc8.comp contMDiff_snd)
    have hmaps : ∀ p : ℝ × ℝ, (ρ p.1, cc p.2) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) :=
      fun p => ⟨hρ_mem p.1, Set.mem_univ _⟩
    have hjoint8 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
      hjoint.of_le h8le
    have hcomp := hjoint8.comp_contMDiff hinner hmaps
    exact (hcomp : ContMDiff _ _ _ _)

  have hchain : ∀ u : ℝ,
      mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam u : M → M) (cc w)) 0 (1 : ℝ)
        = mfderiv I I (Φ_fam u : M → M) x v := by
    intro u
    have hg : MDifferentiableAt I I (Φ_fam u : M → M) (cc 0) :=
      (((Φ_fam u).contMDiff).contMDiffAt).mdifferentiableAt (by simp)
    have hcompeq : (fun w : ℝ => (Φ_fam u : M → M) (cc w)) = (Φ_fam u : M → M) ∘ cc := rfl
    rw [hcompeq, mfderiv_comp 0 hg hcc_mdiff, ContinuousLinearMap.comp_apply, hcc_mderiv]
    rw [hcc0]

  have horbit_nhds : ∀ r : ℝ,
      (fun w : ℝ => Gg w r) =ᶠ[𝓝 t] (fun w : ℝ => (Φ_fam w : M → M) (cc r)) := by
    intro r
    filter_upwards [hρ_nhds] with w hw
    simp only [hGg_def]
    rw [hw]

  have hsec : ∀ r : ℝ,
      mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg w r) t (1 : ℝ)
        = -(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r))) := by
    intro r
    rw [(horbit_nhds r).mfderiv_eq]
    have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam w : M → M) (cc r)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r))))) :=
      (hΦode (cc r) t ⟨ht0, htT⟩).hasMFDerivAt (Ici_mem_nhds ht0)
    rw [hmf.mfderiv]
    change (1 : ℝ →L[ℝ] ℝ) 1 • (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r)))) = _
    rw [ContinuousLinearMap.one_apply, one_smul]

  have hGg0 : ∀ s : ℝ, Gg s 0 = (Φ_fam (ρ s) : M → M) x := by
    intro s; simp only [hGg_def]; rw [hcc0]

  have hbundle : ∀ u : ℝ,
      (TotalSpace.mk' E ((Φ_fam u : M → M) (cc 0))
          (mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam u : M → M) (cc w)) 0 (1 : ℝ))
          : TangentBundle I M)
        = TotalSpace.mk' E ((Φ_fam u : M → M) x) (mfderiv I I (Φ_fam u : M → M) x v) := by
    intro u
    have hbase : (Φ_fam u : M → M) (cc 0) = (Φ_fam u : M → M) x := by rw [hcc0]
    rw [hchain u, hbase]

  have hcomm := commute_ds_dt_intrinsic_shifted (I := I) (g_DT t) Gg hGg_var 0
  have hcomm_t := congrFun hcomm t

  have hfoot_t : Gg t 0 = (Φ_fam t : M → M) x := by rw [hGg0 t, hρt]

  have hL : covDerivAlong (I := I) (g_DT t) (fun s' : ℝ => Gg s' 0)
        (fun s' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg s' w) 0 (1 : ℝ)) t
      = covDerivAlong (I := I) (g_DT t) (fun s' : ℝ => (Φ_fam s' : M → M) x)
        (fun s' : ℝ => mfderiv I I (Φ_fam s' : M → M) x v) t := by
    refine covDerivAlong_locality (I := I) (g_DT t) (fun s' : ℝ => Gg s' 0)
      (fun s' : ℝ => (Φ_fam s' : M → M) x) _ _ t hfoot_t ?_ ?_
    · have hslice : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun s' : ℝ => Gg s' 0) :=
        (hGg_var : ContMDiff _ _ _ _).comp (contMDiff_id.prodMk contMDiff_const)
      exact hslice.continuous.continuousAt
    · filter_upwards [hρ_nhds] with s' hs'
      have hslice : (fun w : ℝ => Gg s' w) = (fun w : ℝ => (Φ_fam s' : M → M) (cc w)) := by
        funext w; simp only [hGg_def]; rw [hs']
      have hpt : Gg s' 0 = (Φ_fam s' : M → M) (cc 0) := by simp only [hGg_def, hs']
      calc (TotalSpace.mk' E (Gg s' 0)
              (mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg s' w) 0 (1 : ℝ)) : TangentBundle I M)
          = TotalSpace.mk' E ((Φ_fam s' : M → M) (cc 0))
              (mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam s' : M → M) (cc w)) 0 (1 : ℝ)) :=
            congrArg (fun g : ℝ → M =>
              (TotalSpace.mk' E (g 0) (mfderiv 𝓘(ℝ, ℝ) I g 0 (1 : ℝ)) : TangentBundle I M)) hslice
        _ = TotalSpace.mk' E ((Φ_fam s' : M → M) x) (mfderiv I I (Φ_fam s' : M → M) x v) :=
            hbundle s'

  have hR : covDerivAlong (I := I) (g_DT t) (fun r : ℝ => Gg t r)
        (fun r : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg w r) t (1 : ℝ)) 0
      = -((LeviCivita (I := I) (g_DT t))
        (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y) ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)) := by
    have hRb : ∀ r : ℝ, Gg t r = (Φ_fam t : M → M) (cc r) := by
      intro r; simp only [hGg_def, hρt]
    have hstep1 : covDerivAlong (I := I) (g_DT t) (fun r : ℝ => Gg t r)
          (fun r : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun w : ℝ => Gg w r) t (1 : ℝ)) 0
        = covDerivAlong (I := I) (g_DT t) (fun r : ℝ => (Φ_fam t : M → M) (cc r))
          (fun r : ℝ => -(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r)))) 0 := by
      refine covDerivAlong_locality (I := I) (g_DT t) (fun r : ℝ => Gg t r)
        (fun r : ℝ => (Φ_fam t : M → M) (cc r)) _ _ 0 (hRb 0) ?_ ?_
      · have hslice : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun r : ℝ => Gg t r) :=
          (hGg_var : ContMDiff _ _ _ _).comp (contMDiff_const.prodMk contMDiff_id)
        exact hslice.continuous.continuousAt
      · filter_upwards with r
        rw [hsec r, hRb r]
    rw [hstep1]
    have hneg : (fun r : ℝ => -(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r))))
        = (fun r : ℝ => (-1 : ℝ) • deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r))) := by
      funext r; rw [neg_one_smul]
    rw [hneg, covDerivAlong_smul]
    have hleaf5 : covDerivAlong (I := I) (g_DT t)
          (fun r : ℝ => (Φ_fam t : M → M) (cc r))
          (fun r : ℝ => deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) (cc r))) 0
        = (LeviCivita (I := I) (g_DT t))
          (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y)
          ((Φ_fam t : M → M) (cc 0))
          (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => (Φ_fam t : M → M) (cc r)) 0 (1 : ℝ)) := by
      have hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun r : ℝ => (Φ_fam t : M → M) (cc r)) :=
        ((Φ_fam t).contMDiff).comp hcc_smooth
      exact covDerivAlong_restrict_eq_leviCivita (I := I) (g_DT t)
        (fun r : ℝ => (Φ_fam t : M → M) (cc r))
        (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y) 0 hγsmooth
        (deTurckVF (I := I) (g_DT t) g_bg).mdifferentiableAt
    rw [hleaf5, hchain t, hcc0]
    rw [neg_one_smul]
  exact hL.symm.trans (hcomm_t.trans hR)

end DifferentialGeometry.PDE.RicciFlow

end
