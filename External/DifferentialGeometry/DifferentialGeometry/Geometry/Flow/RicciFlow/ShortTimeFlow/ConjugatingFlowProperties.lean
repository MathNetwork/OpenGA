import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.FlatVariationalIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.BasepointMotion
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.EvalFormChainRule
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciContinuityInMetricTime
import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.CutoffExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.FlowVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullback
import DifferentialGeometry.Bundle.PartialMfderiv
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem conjugating_flow_jointContMDiffOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  set Y : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => -(deTurckVF (I := I) (g_DT s) g_bg x) with hY_def
  have hint_Y : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    have hYeq : (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M))
        = (fun q : ℝ × M => (TotalSpace.mk' E q.2
            ((-1 : ℝ) • deTurckVF (I := I) (g_DT q.1) g_bg q.2) : TangentBundle I M)) := by
      funext q; simp only [hY_def, neg_one_smul]
    rw [hYeq]
    intro q hq
    exact CutoffExtensionAux.smul_tangentMap_cmdwa
      (fun s x => (deTurckVF (I := I) (g_DT s) g_bg x : TangentSpace I x)) (fun _ => (-1 : ℝ))
      contMDiffWithinAt_const (hfield_reg q hq)
  intro q₀ hq₀
  obtain ⟨ht₀_lo, ht₀_hi⟩ := hq₀.1
  obtain ⟨a, ha0, hat₀⟩ := exists_between ht₀_lo
  obtain ⟨b, ht₀b, hbT⟩ := exists_between ht₀_hi
  obtain ⟨Xt, δ, hδ, hXt_eq, hXt_cont, hXt_auto⟩ :=
    interior_field_global_cutoff_extension Y T hint_Y ha0 (lt_trans hat₀ ht₀b) hbT
  obtain ⟨T', hT', Φ, hΦ_init, hΦ_smooth, hΦ_bare⟩ :=
    global_flow_jointContMDiffOn_on_closed_manifold Xt hXt_cont q₀.1
  set c : ℝ := max (max (a - δ) (q₀.1 - T')) 0 with hc_def
  set d : ℝ := min (min (b + δ) (q₀.1 + T')) T with hd_def
  have hc_lt : c < q₀.1 := by
    rw [hc_def]
    refine max_lt (max_lt ?_ (by linarith)) ht₀_lo
    have : a - δ < a := by linarith
    linarith [hat₀]
  have hlt_d : q₀.1 < d := by
    rw [hd_def]
    refine lt_min (lt_min ?_ (by linarith)) ht₀_hi
    have : b < b + δ := by linarith
    linarith [ht₀b]
  have ht₀_cd : q₀.1 ∈ Set.Ioo c d := ⟨hc_lt, hlt_d⟩
  have hc_ge0 : 0 ≤ c := le_max_right _ _
  have hcd_aδ : Set.Ioo c d ⊆ Set.Ioo (a - δ) (b + δ) :=
    Set.Ioo_subset_Ioo (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcd_T' : Set.Ioo c d ⊆ Set.Ioo (q₀.1 - T') (q₀.1 + T') :=
    Set.Ioo_subset_Ioo (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcd_0T : Set.Ioo c d ⊆ Set.Ioo (0 : ℝ) T :=
    Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hcd_Ici : Set.Ioo c d ⊆ Set.Ici (0 : ℝ) := fun s hs => le_of_lt (lt_of_le_of_lt hc_ge0 hs.1)
  have hident : ∀ y : M, ∀ s ∈ Set.Ioo c d,
      (Φ_fam s : M → M) y = Φ ((Φ_fam q₀.1 : M → M) y) s := by
    intro y
    have hflow : ∀ s ∈ Set.Ioo c d,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y) (Set.Ioo c d) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt s ((Φ_fam s : M → M) y))) := by
      intro s hs
      have heq : Xt s ((Φ_fam s : M → M) y) = -(deTurckVF (I := I) (g_DT s) g_bg
          ((Φ_fam s : M → M) y)) := by
        rw [hXt_eq s (hcd_aδ hs) ((Φ_fam s : M → M) y)]
      rw [heq]
      exact (hΦode y s (hcd_0T hs)).mono hcd_Ici
    have hflow' : ∀ s ∈ Set.Ioo c d,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ ((Φ_fam q₀.1 : M → M) y) u)
          (Set.Ioo c d) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt s (Φ ((Φ_fam q₀.1 : M → M) y) s))) := fun s hs =>
      (hΦ_bare ((Φ_fam q₀.1 : M → M) y) s (hcd_T' hs)).hasMFDerivWithinAt.mono (subset_refl _)
    have hstart : (fun u : ℝ => (Φ_fam u : M → M) y) q₀.1
        = (fun u : ℝ => Φ ((Φ_fam q₀.1 : M → M) y) u) q₀.1 := by
      simp only [hΦ_init]
    exact bare_integral_flow_eqOn_of_jointC1 (a := c) (b := d) (t₀ := q₀.1)
      Xt hXt_auto (fun u : ℝ => (Φ_fam u : M → M))
      (fun u : ℝ => fun p : M => Φ p u) y ((Φ_fam q₀.1 : M → M) y) ht₀_cd hflow hflow' hstart
  set W : Set (ℝ × M) := Set.Ioo c d ×ˢ (Set.univ : Set M) with hW_def
  have hW_open : IsOpen W := isOpen_Ioo.prod isOpen_univ
  have hq₀_W : q₀ ∈ W := ⟨ht₀_cd, Set.mem_univ _⟩
  have hΦfam_t₀ : ContMDiff I I ∞ (Φ_fam q₀.1 : M → M) := Diffeomorph.mfderiv_contMDiff _
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1, (Φ_fam q₀.1 : M → M) q.2)) :=
    contMDiff_fst.prodMk (hΦfam_t₀.comp contMDiff_snd)
  have ht₀_T' : q₀.1 ∈ Set.Ioo (q₀.1 - T') (q₀.1 + T') := ⟨by linarith, by linarith⟩
  have hG_at : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.2 p.1)
      (Set.Ioo (q₀.1 - T') (q₀.1 + T') ×ˢ (Set.univ : Set M))
      ((fun q : ℝ × M => (q.1, (Φ_fam q₀.1 : M → M) q.2)) q₀) :=
    hΦ_smooth _ ⟨ht₀_T', Set.mem_univ _⟩
  have hmaps : Set.MapsTo (fun q : ℝ × M => (q.1, (Φ_fam q₀.1 : M → M) q.2))
      W (Set.Ioo (q₀.1 - T') (q₀.1 + T') ×ˢ (Set.univ : Set M)) := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    exact ⟨hcd_T' hs, Set.mem_univ _⟩
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Φ ((Φ_fam q₀.1 : M → M) q.2) q.1) W q₀ :=
    (hG_at.comp q₀ (hF.contMDiffAt.contMDiffWithinAt) hmaps)
  have hcongr_W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) W q₀ := by
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact hident q.2 q.1 hq.1
    · exact hident q₀.2 q₀.1 ht₀_cd
  have hW_nhds : W ∈ 𝓝[Set.Ioo (0 : ℝ) T ×ˢ Set.univ] q₀ :=
    mem_nhdsWithin_of_mem_nhds (hW_open.mem_nhds hq₀_W)
  exact hcongr_W.mono_of_mem_nhdsWithin hW_nhds

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private theorem spatial_pushforward_chartCoord_contMDiffAt
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (5 : ℕ)
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
          ((Φ_fam p.2 : M → M) x) (mfderiv I I (Φ_fam p.2 : M → M) x v)) (t, t) := by
  classical
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  set α : M := (Φ_fam t : M → M) x with hα
  have hflow_at : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I (8 : ℕ)
      (Function.uncurry (fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y)) ((t, t), x) := by
    have hcompfun : (Function.uncurry (fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y))
        = (fun r : ((ℝ × ℝ) × M) => (Φ_fam r.1.2 : M → M) r.2) := rfl
    rw [hcompfun]
    have hmaps : (fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)
        ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := ⟨ht, Set.mem_univ _⟩
    have hmem_nhds : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M)
        ∈ nhds ((fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds hmaps
    have hjoint_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
        ((fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)) :=
      ((hjoint.of_le h8le).contMDiffAt hmem_nhds)
    have hinner : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x) :=
      (contMDiffAt_fst.snd).prodMk contMDiffAt_snd
    exact hjoint_at.comp ((t, t), x) hinner
  have h_smooth_mfd := ContMDiffAt.mfderiv_apply
    (I := I) (I' := I)
    (f := fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y)
    (g := fun _ : ℝ × ℝ => x)
    (g₁ := id) (g₂ := fun _ : ℝ × ℝ => v)
    (x₀ := (t, t)) (n := (8 : ℕ)) (m := (5 : ℕ))
    (by simpa using hflow_at) contMDiffAt_const contMDiffAt_id contMDiffAt_const
    (by exact_mod_cast (by norm_num : (5 : ℕ) + 1 ≤ 8))
  refine h_smooth_mfd.congr_of_eventuallyEq ?_
  have hcontAt : ContinuousAt (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) (t, t) := by
    have hflowAt : ContinuousAt (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) := by
      have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
      exact (hjoint.continuousOn.continuousAt hmem)
    have hcomp : ContinuousAt (fun p : ℝ × ℝ => ((p.2, x) : ℝ × M)) (t, t) :=
      (continuous_snd.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (x := (t, t)) (by simpa using hflowAt) hcomp
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hpre : (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) ⁻¹' (chartAt H α).source ∈ nhds (t, t) :=
    hcontAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds (by rw [hα]; exact hαsrc))
  filter_upwards [hpre] with p hp
  have hxsrc : (id ((fun _ : ℝ × ℝ => x) p)) ∈ (chartAt H ((fun _ : ℝ × ℝ => x) (t, t))).source := by
    simp [mem_chart_source]
  have hysrc : ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p)
      ∈ (chartAt H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) (t, t))).source := by
    simpa [hα] using hp
  symm
  simp only [id_eq]
  rw [inTangentCoordinates_eq (I := I) (I' := I)
        (f := fun _ : ℝ × ℝ => x) (g := fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x)
        (ϕ := fun q : ℝ × ℝ => mfderiv I I (fun y : M => (Φ_fam q.2 : M → M) y) x) hxsrc hysrc]
  have htarget_eq : (tangentBundleCore I M).coordChange
        (achart H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p))
        (achart H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) (t, t)))
        ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p)
      = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x) := by
    change (tangentBundleCore I M).coordChange (achart H ((Φ_fam p.2 : M → M) x)) (achart H α)
        ((Φ_fam p.2 : M → M) x)
      = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
    have hsrcα : (Φ_fam p.2 : M → M) x ∈ (chartAt H α).source := hp
    exact (TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (b₀ := α) (b := (Φ_fam p.2 : M → M) x) hsrcα).symm
  rw [htarget_eq]
  simp only [ContinuousLinearMap.comp_apply]
  rw [show ((tangentBundleCore I M).coordChange (achart H x) (achart H x) x) v = v from
    (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private theorem flow_chartGram_contMDiffAt
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) (5 : ℕ)
      (fun p : ℝ × ℝ =>
        Integral.Measure.chartGramMatrix (I := I) (g_DT p.1)
          ((Φ_fam t : M → M) x) ((Φ_fam p.2 : M → M) x) i j) (t, t) := by
  classical
  set α : M := (Φ_fam t : M → M) x with hα
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  have hbase0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) (5 : ℕ)
      (fun p : ℝ × ℝ => (p.1, (Φ_fam p.2 : M → M) x)) (t, t) := by
    have hflowAt : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (5 : ℕ)
        (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) (t, t) := by
      have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
      have hflow_tx : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (5 : ℕ)
          (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) :=
        (hjoint.of_le h8le).contMDiffAt hmem |>.of_le
          (by exact_mod_cast (by norm_num : (5 : ℕ) ≤ (8 : ℕ)) : (5 : WithTop ℕ∞) ≤ (8 : ℕ))
      have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) (5 : ℕ)
          (fun p : ℝ × ℝ => ((p.2, x) : ℝ × M)) (t, t) :=
        contMDiffAt_snd.prodMk contMDiffAt_const
      exact ContMDiffAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
        (x := (t, t)) (by simpa using hflow_tx) hcomp
    exact contMDiffAt_fst.prodMk hflowAt
  have hmem_dom : ((t : ℝ), α) ∈ Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet :=
    ⟨ht, hbase0⟩
  have hdom_nhds : Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
      ∈ nhds ((t : ℝ), α) :=
    (isOpen_Ioo.prod (trivializationAt E (TangentSpace I) α).open_baseSet).mem_nhds hmem_dom
  have hgramAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (5 : ℕ)
      (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j) (t, α) :=
    ((hgram_DT α i j).of_le h8le).contMDiffAt hdom_nhds |>.of_le
      (by exact_mod_cast (by norm_num : (5 : ℕ) ≤ (8 : ℕ)) : (5 : WithTop ℕ∞) ≤ (8 : ℕ))
  exact ContMDiffAt.comp (x := (t, t))
    (g := fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j)
    (by simpa [hα] using hgramAt) hpair

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
open DifferentialGeometry.PDE.RicciFlow.Pullback in

omit [NeZero (Module.finrank ℝ E)] in
private theorem evalFormTwoVar_hasFDerivWithinAt
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    ∃ Q' : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
        ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t) := by
  classical
  set α : M := (Φ_fam t : M → M) x with hα
  set e := trivializationAt E (TangentSpace I) α with he
  have hsummand : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) (5 : ℕ)
        (fun p : ℝ × ℝ =>
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
              (mfderiv I I (Φ_fam p.2 : M → M) x v))) i *
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
              (mfderiv I I (Φ_fam p.2 : M → M) x w))) j *
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α ((Φ_fam p.2 : M → M) x) i j)
        (t, t) := by
    intro i j
    have hV := spatial_pushforward_chartCoord_contMDiffAt (I := I) T Φ_fam hjoint t ht x v
    have hW := spatial_pushforward_chartCoord_contMDiffAt (I := I) T Φ_fam hjoint t ht x w
    have hlinCLM : ∀ p : Fin (Module.finrank ℝ E),
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (5 : ℕ)
          (fun y : E => ((Integral.Measure.chartModelBasis E).repr y) p) := by
      intro p
      set L : E →ₗ[ℝ] ℝ :=
        (Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) p).comp
          (Integral.Measure.chartModelBasis E).repr.toLinearMap with hL
      set Lclm : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L with hLclm
      have hfun : (fun y : E => ((Integral.Measure.chartModelBasis E).repr y) p)
          = fun y : E => Lclm y := by funext y; rfl
      rw [hfun, contMDiff_iff_contDiff]
      exact Lclm.contDiff.of_le le_top
    have hVrepr : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) (5 : ℕ)
        (fun p : ℝ × ℝ => ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x v))) i) (t, t) :=
      (hlinCLM i).contMDiffAt.comp (t, t) hV
    have hWrepr : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) (5 : ℕ)
        (fun p : ℝ × ℝ => ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x w))) j) (t, t) :=
      (hlinCLM j).contMDiffAt.comp (t, t) hW
    have hG := flow_chartGram_contMDiffAt (I := I) g_DT T Φ_fam hjoint hgram_DT t ht x i j
    exact (hVrepr.mul hWrepr).mul (by simpa [hα] using hG)
  have hsum : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) (5 : ℕ)
      (fun p : ℝ × ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x v))) i *
        ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x w))) j *
        Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α ((Φ_fam p.2 : M → M) x) i j)
      (t, t) :=
    ContMDiffAt.sum (fun i _ => ContMDiffAt.sum (fun j _ => hsummand i j))
  have hcontAt : ContinuousAt (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) (t, t) := by
    have hflowAt : ContinuousAt (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) := by
      have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
      exact (hjoint.continuousOn.continuousAt hmem)
    exact ContinuousAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (x := (t, t)) (by simpa using hflowAt) ((continuous_snd.prodMk continuous_const).continuousAt)
  have hbase0 : α ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hsrc0 : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
  have hpre : (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) ⁻¹' (e.baseSet ∩ (extChartAt I α).source)
      ∈ nhds (t, t) := by
    refine hcontAt.preimage_mem_nhds ((IsOpen.inter e.open_baseSet
      (isOpen_extChartAt_source (I := I) α)).mem_nhds ?_)
    exact ⟨by rw [← hα]; exact hbase0, by rw [← hα]; exact hsrc0⟩
  have heq : (evalFormTwoVar (I := I) g_DT Φ_fam x v w) =ᶠ[nhds (t, t)]
      (fun p : ℝ × ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x v))) i *
        ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x w))) j *
        Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α ((Φ_fam p.2 : M → M) x) i j) := by
    filter_upwards [hpre] with p hp
    obtain ⟨hb, hsr⟩ := hp
    have hbE : (Φ_fam p.2 : M → M) x ∈ e.baseSet := hb
    have hexpand := g_inner_eq_chart_sum (I := I) (g_DT p.1) α (by rw [he] at hbE; exact hbE) hsr
      (mfderiv I I (Φ_fam p.2 : M → M) x v) (mfderiv I I (Φ_fam p.2 : M → M) x w)
    change evalFormTwoVar (I := I) g_DT Φ_fam x v w p = _
    unfold evalFormTwoVar
    rw [hexpand]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hgramEq : DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
          (I := I) (g_DT p.1) α i j (extChartAt I α ((Φ_fam p.2 : M → M) x))
        = Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α ((Φ_fam p.2 : M → M) x) i j := by
      unfold DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
      rw [(extChartAt I α).left_inv hsr]
    rw [hgramEq]
  have hevalAt : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) (5 : ℕ)
      (evalFormTwoVar (I := I) g_DT Φ_fam x v w) (t, t) :=
    hsum.congr_of_eventuallyEq heq
  have hdiff : DifferentiableAt ℝ (evalFormTwoVar (I := I) g_DT Φ_fam x v w) (t, t) := by
    have hcd : ContDiffAt ℝ (5 : ℕ) (evalFormTwoVar (I := I) g_DT Φ_fam x v w) (t, t) := by
      rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hevalAt
    exact hcd.differentiableAt (by norm_num)
  exact ⟨fderiv ℝ (evalFormTwoVar (I := I) g_DT Φ_fam x v w) (t, t),
    hdiff.hasFDerivAt.hasFDerivWithinAt⟩

open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Pullback in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem flow_pushforward_slot_hasDerivWithinAt
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      (- lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  classical
  set γ : ℝ → M := fun s : ℝ => (Φ_fam s : M → M) x with hγ
  set V : ∀ s : ℝ, TangentSpace I (γ s) := fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v with hV
  set W : ∀ s : ℝ, TangentSpace I (γ s) := fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x w with hW
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  have hchartRepDiff : ∀ u : TangentSpace I x,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x u) t) t := by
    intro u
    have hlin := spatial_pushforward_chartCoord_contMDiffAt (I := I) T Φ_fam hjoint t ht x u
    have hrestr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (5 : ℕ)
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t := by
      have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (5 : ℕ)
          (fun s : ℝ => (t, s)) t := contMDiffAt_const.prodMk contMDiffAt_id
      exact hlin.comp t hincl
    have hcd : ContDiffAt ℝ (5 : ℕ)
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t := by
      rw [← contMDiffAt_iff_contDiffAt]; exact hrestr
    have hdiffAt : DifferentiableAt ℝ
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t :=
      hcd.differentiableAt (by norm_num)
    have hfun : chartRepAt (I := I) γ (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x u) t
        = (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) := by
      funext s; rw [chartRepAt_apply]
    rw [hfun]; exact hdiffAt
  have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) γ t := by
    have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
    have hflow_tx : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) :=
      (hjoint.of_le h8le).contMDiffAt hmem
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun s : ℝ => ((s, x) : ℝ × M)) t := contMDiffAt_id.prodMk contMDiffAt_const
    exact ContMDiffAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (x := t)
      (by simpa using hflow_tx) hincl
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t) γ) t := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (8 : ℕ) ((extChartAt I (γ t)) ∘ γ) t := by
      have hφ : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I (γ t)) (γ t) :=
        (contMDiffAt_extChartAt (I := I) (x := γ t)).of_le h8le
      exact hφ.comp t hγ_at
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hmc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I)
    (g_DT t) γ V W t hγ_at.continuousAt hchartDeriv (hchartRepDiff v) (hchartRepDiff w)
  have hjointFV : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := hjoint
  have hG2v := conjugating_flow_covariant_variational_eq (I := I) g_DT g_bg T Φ_fam hΦode hjointFV
    t ht x v
  have hG2w := conjugating_flow_covariant_variational_eq (I := I) g_DT g_bg T Φ_fam hΦode hjointFV
    t ht x w
  have hAval : (g_DT t).inner (γ t) (covDerivAlong (I := I) (g_DT t) γ V t) (W t)
      = -(g_DT t).inner ((Φ_fam t : M → M) x)
          ((LeviCivita (I := I) (g_DT t))
            (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y) ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x v))
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hV, hG2v, map_neg]; rfl
  have hBval : (g_DT t).inner (γ t) (V t) (covDerivAlong (I := I) (g_DT t) γ W t)
      = -(g_DT t).inner ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          ((LeviCivita (I := I) (g_DT t))
            (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y) ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x w)) := by
    rw [hW, hG2w, map_neg]
  have hsumval : (g_DT t).inner (γ t) (covDerivAlong (I := I) (g_DT t) γ V t) (W t)
        + (g_DT t).inner (γ t) (V t) (covDerivAlong (I := I) (g_DT t) γ W t)
      = -lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hAval, hBval]
    exact lie_deriv_metric_neg_eq_pushforward_variation_sum (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) ((Φ_fam t : M → M) x)
      (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w) _ _ rfl rfl
  have hmc' : HasDerivAt (fun s : ℝ => (g_DT t).inner (γ s) (V s) (W s))
      (-lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)) t := by
    rw [← hsumval]; exact hmc
  exact hmc'.hasDerivWithinAt

theorem conjugating_flow_flat_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hDT_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
        (deTurckRicciRHS (I := I) g_bg (g_DT s) y a b) (Set.Ici 0) s)
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
        ((-2) * ricciTensor (I := I)
          (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  have hjoint := conjugating_flow_jointContMDiffOn (I := I) g_DT g_bg T Φ_fam hΦode hfield_reg
  intro t ht x v w
  have ht_Ico : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have h_metric : HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      ((-2 : ℝ) * ricciTensor (I := I) (g_DT t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
        + lieDerivMetric (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
    have h := hDT_deriv t ht_Ico ((Φ_fam t : M → M) x)
      (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
    rwa [deTurckRicciRHS_apply] at h
  have h_push := flow_pushforward_slot_hasDerivWithinAt (I := I) g_DT g_bg T Φ_fam hΦode hjoint
    t ht x v w
  obtain ⟨Q', hQ'⟩ := evalFormTwoVar_hasFDerivWithinAt (I := I) g_DT T Φ_fam hjoint hgram_DT
    t ht x v w
  have h_total := deTurck_evalForm_chain_hasDerivWithinAt (I := I) g_DT Φ_fam
    t (le_of_lt ht.1) x v w _ _ h_metric h_push hQ'
  exact deTurck_pullback_eval_value_hasDerivWithinAt (I := I) g_bg g_DT Φ_fam t x v w h_total

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem conjugating_flow_orbit_pushforward_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (_hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) :
    (∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T)) ∧
    (∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T)) := by
  have hjoint := conjugating_flow_jointContMDiffOn (I := I) g_DT g_bg T Φ_fam hΦode hfield_reg
  have horbit_interior : ∀ y : M, ∀ s₀ ∈ Set.Ioo (0 : ℝ) T,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T) s₀ := by
    intro y s₀ hs₀
    have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (s₀, y) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs₀, Set.mem_univ _⟩
    have hflow_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (s₀, y) :=
      hjoint.contMDiffAt hmem
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ => ((s, y) : ℝ × M)) s₀ := contMDiffAt_id.prodMk contMDiffAt_const
    have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun s : ℝ => (Φ_fam s : M → M) y) s₀ :=
      ContMDiffAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (x := s₀)
        (by simpa using hflow_at) hincl
    exact hcomp.continuousAt.continuousWithinAt
  have horbit : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T) := by
    intro y s₀ hs₀
    rcases eq_or_lt_of_le hs₀.1 with h0 | h0
    · subst h0
      exact (hΦorbit0 y).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset self_mem_nhdsWithin Set.Ico_subset_Ici_self)
    · exact horbit_interior y s₀ ⟨h0, hs₀.2⟩
  refine ⟨horbit, ?_⟩
  intro y u s₀ hs₀
  rcases eq_or_lt_of_le hs₀.1 with h0 | h0
  · subst h0
    exact (hΦmfderiv0 y u).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset self_mem_nhdsWithin Set.Ico_subset_Ici_self)
  · have hs₀_ioo : s₀ ∈ Set.Ioo (0 : ℝ) T := ⟨h0, hs₀.2⟩
    have hchartRepDiff : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun s : ℝ => (Φ_fam s : M → M) y)
          (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) y u) s₀) s₀ := by
      have hlin := spatial_pushforward_chartCoord_contMDiffAt (I := I) T Φ_fam hjoint s₀ hs₀_ioo y u
      have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (5 : ℕ)
          (fun s : ℝ => (s₀, s)) s₀ := contMDiffAt_const.prodMk contMDiffAt_id
      have hrestr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (5 : ℕ)
          (fun s : ℝ =>
            (trivializationAt E (TangentSpace I) ((Φ_fam s₀ : M → M) y)).continuousLinearMapAt ℝ
              ((Φ_fam s : M → M) y) (mfderiv I I (Φ_fam s : M → M) y u)) s₀ :=
        hlin.comp s₀ hincl
      have hcd : ContDiffAt ℝ (5 : ℕ)
          (fun s : ℝ =>
            (trivializationAt E (TangentSpace I) ((Φ_fam s₀ : M → M) y)).continuousLinearMapAt ℝ
              ((Φ_fam s : M → M) y) (mfderiv I I (Φ_fam s : M → M) y u)) s₀ := by
        rw [← contMDiffAt_iff_contDiffAt]; exact hrestr
      have hfun : chartRepAt (I := I) (fun s : ℝ => (Φ_fam s : M → M) y)
            (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) y u) s₀
          = (fun s : ℝ =>
            (trivializationAt E (TangentSpace I) ((Φ_fam s₀ : M → M) y)).continuousLinearMapAt ℝ
              ((Φ_fam s : M → M) y) (mfderiv I I (Φ_fam s : M → M) y u)) := by
        funext s; rw [chartRepAt_apply]
      rw [hfun]; exact hcd.differentiableAt (by norm_num)
    exact sectionAlongCurve_continuousWithinAt_totalSpace (I := I)
      (fun s : ℝ => (Φ_fam s : M → M) y) (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) y u)
      ⟨hs₀.1, hs₀.2⟩ (horbit y |>.continuousWithinAt hs₀) hchartRepDiff


omit [CompactSpace M] in
theorem conjugating_flow_t0_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (_hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (_hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (_hDT_init : g_DT 0 = g_bg)
    (hg_joint : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
            (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ (chartAt H α).source))
    (hC2 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α))
    (hΦ_orbit : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ_total : ∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T))
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w) (Set.Ico 0 T) ∧
      ContinuousWithinAt
        (fun s : ℝ => (-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 := by
  refine ⟨gfam_inner_continuous_on (I := I) g_DT T hT Φ_fam x v w hg_joint hΦ_orbit hΦ_total, ?_⟩
  have hric : ContinuousOn
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ico 0 T) :=
    ricci_gfam_continuous_on (I := I) g_DT T hT Φ_fam x v w hC2 hΦ_orbit hΦ_total
  have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hcwa_Ioo : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioo 0 T) 0 :=
    (hric.continuousWithinAt h0mem).mono Set.Ioo_subset_Ico_self
  have hcwa_Ioi : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 :=
    hcwa_Ioo.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hT)
  exact hcwa_Ioi.const_mul (-2 : ℝ)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in

private theorem flow_pushforward_chartBasisVec_section_cmwa
    (J : Set ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (J ×ˢ Set.univ))
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (m : ℕ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ J) (b₀ : M)
    (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) (m : ℕ)
      (fun p : ℝ × M =>
        (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2
            (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
          : TangentBundle I M))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (t₀, b₀) := by
  classical
  set S : Set (ℝ × M) := J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
    with hS
  have hS_sub : S ⊆ J ×ˢ (Set.univ : Set M) := by
    rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
  have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
  have hm1top : (((m : ℕ) + 1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (((m : ℕ) + 1 : ℕ) : ℕ∞) ≤ ⊤)
  have hmtop : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤)
  set f : (ℝ × M) → M → M := fun q y => (Φ_fam q.1 : M → M) y with hf_def
  have hf_uncurry_eq : Function.uncurry f
      = (fun r : (ℝ × M) × M => (Φ_fam r.1.1 : M → M) r.2) := rfl
  have hf : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod I) I ((m : ℕ) + 1 : ℕ)
      (Function.uncurry f) (S ×ˢ (Set.univ : Set M)) ((t₀, b₀), b₀) := by
    rw [hf_uncurry_eq]
    have hjointN : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ((m : ℕ) + 1 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (J ×ˢ Set.univ) :=
      hjoint.of_le hm1top
    have hpre : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod I) (𝓘(ℝ, ℝ).prod I) ((m : ℕ) + 1 : ℕ)
        (fun r : (ℝ × M) × M => ((r.1.1, r.2) : ℝ × M)) (S ×ˢ (Set.univ : Set M)) ((t₀, b₀), b₀) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun r : (ℝ × M) × M => ((r.1.1, r.2) : ℝ × M))
        (S ×ˢ (Set.univ : Set M)) (J ×ˢ (Set.univ : Set M)) := by
      rintro ⟨⟨t, b⟩, y⟩ ⟨hq, -⟩
      exact ⟨(hS_sub hq).1, Set.mem_univ _⟩
    have hmem' : ((fun r : (ℝ × M) × M => ((r.1.1, r.2) : ℝ × M)) ((t₀, b₀), b₀))
        ∈ J ×ˢ (Set.univ : Set M) := ⟨ht₀, Set.mem_univ _⟩
    exact (hjointN _ hmem').comp ((t₀, b₀), b₀) hpre hmaps
  have hg : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (m : ℕ)
      (fun q : ℝ × M => q.2) S (t₀, b₀) := contMDiffWithinAt_snd
  have hu : Set.MapsTo (fun q : ℝ × M => q.2) S (Set.univ : Set M) := fun _ _ => Set.mem_univ _
  have hϕ := ContMDiffWithinAt.mfderivWithin
    (I := I) (I' := I) (n := ((m : ℕ) + 1 : ℕ)) (m := (m : ℕ))
    (f := f) (g := fun q : ℝ × M => q.2) (t := S) (u := (Set.univ : Set M))
    (x₀ := (t₀, b₀))
    hf hg ht₀b₀ hu le_rfl uniqueMDiffOn_univ
  have hv : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) (m : ℕ)
      (fun q : ℝ × M => (Integral.Measure.chartBasisVec (I := I) x₀ i q.2 : TangentBundle I M))
      S (t₀, b₀) := by
    have hcb : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (m : ℕ)
        (Integral.Measure.chartBasisVec (I := I) x₀ i)
        (trivializationAt E (TangentSpace I) x₀).baseSet b₀ :=
      (Integral.Measure.chartBasisVec_contMDiffOn (I := I) x₀ i b₀ hb₀).of_le hmtop
    have hsnd : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (m : ℕ)
        (fun q : ℝ × M => q.2) S (t₀, b₀) := contMDiffWithinAt_snd
    have hmaps2 : Set.MapsTo (fun q : ℝ × M => q.2) S
        (trivializationAt E (TangentSpace I) x₀).baseSet := fun q hq => hq.2
    exact hcb.comp (t₀, b₀) hsnd hmaps2
  have hb₂ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (m : ℕ)
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) S (t₀, b₀) :=
    ((hjoint.of_le hmtop) _ (hS_sub ht₀b₀)).mono hS_sub
  have hkey := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := I) (IB₂ := I) (F₁ := E) (F₂ := E)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (b₁ := fun q : ℝ × M => q.2) (b₂ := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
    (ϕ := fun q : ℝ × M => mfderiv I I (Φ_fam q.1 : M → M) q.2)
    (v := fun q : ℝ × M => Integral.Measure.chartBasisVecFiber (I := I) x₀ i q.2)
    (m₀ := (t₀, b₀)) (s := S) (n := (m : ℕ))
    ?_ hv hb₂
  · convert hkey using 2
  · have hrw : (fun q : ℝ × M =>
          ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E (TangentSpace I (M := M))
          ((fun q : ℝ × M => q.2) (t₀, b₀)) ((fun q : ℝ × M => q.2) q)
          ((fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t₀, b₀))
          ((fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) q)
          ((fun q : ℝ × M => mfderiv I I (Φ_fam q.1 : M → M) q.2) q))
        = (fun q : ℝ × M => inTangentCoordinates I I (fun q : ℝ × M => q.2)
            (fun x => f x ((fun q : ℝ × M => q.2) x))
            (fun x => mfderivWithin I I (f x) (Set.univ) ((fun q : ℝ × M => q.2) x))
            (t₀, b₀) q) := by
      funext q
      rw [inTangentCoordinates, mfderivWithin_univ]
    rw [hrw]
    exact hϕ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in

private theorem flow_pushforward_chartCoord_cmwa
    (J : Set ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (J ×ˢ Set.univ))
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (m : ℕ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ J) (b₀ : M)
    (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) (m : ℕ)
      (fun p : ℝ × M =>
        (trivializationAt E (TangentSpace I) ((Φ_fam t₀ : M → M) b₀)).continuousLinearMapAt ℝ
          ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2
            (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (t₀, b₀) := by
  classical
  set α : M := (Φ_fam t₀ : M → M) b₀ with hα
  set e := trivializationAt E (TangentSpace I) α with he
  set S : Set (ℝ × M) := J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
    with hS
  set F : (ℝ × M) → TangentBundle I M := fun p : ℝ × M =>
    (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
      (mfderiv I I (Φ_fam p.1 : M → M) p.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
      : TangentBundle I M) with hF
  have hsection := flow_pushforward_chartBasisVec_section_cmwa
    (I := I) J Φ_fam hjoint x₀ i m t₀ ht₀ b₀ hb₀
  rw [Bundle.contMDiffWithinAt_totalSpace] at hsection
  obtain ⟨hsec_proj, hsec_fib⟩ := hsection
  have hbase0 : α ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hS_sub : S ⊆ J ×ˢ (Set.univ : Set M) := by
    rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
  have horbit_cwa : ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) S (t₀, b₀) :=
    ((hjoint.continuousOn).mono hS_sub).continuousWithinAt ⟨ht₀, hb₀⟩
  have hbnhds : e.baseSet ∈ nhds ((Φ_fam t₀ : M → M) b₀) := by
    rw [← hα]; exact e.open_baseSet.mem_nhds hbase0
  have hpb : (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) ⁻¹' e.baseSet ∈ nhdsWithin (t₀, b₀) S :=
    horbit_cwa.preimage_mem_nhdsWithin hbnhds
  refine hsec_fib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpb] with p hp
    change e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
      = (e (F p)).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hp,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hp]
  · change e.continuousLinearMapAt ℝ ((Φ_fam t₀ : M → M) b₀)
        (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ i b₀))
      = (e (F (t₀, b₀))).2
    have hb0 : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet := by rw [← hα]; exact hbase0
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hb0,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hb0]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private theorem chartModelBasis_repr_cmwa {n : ℕ}
    {S : Set (ℝ × M)} {p₀ : ℝ × M} {f : (ℝ × M) → E}
    (hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) (n : ℕ) f S p₀)
    (p : Fin (Module.finrank ℝ E)) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
      (fun q : ℝ × M => ((Integral.Measure.chartModelBasis E).repr (f q)) p) S p₀ := by
  set L : E →ₗ[ℝ] ℝ :=
    (Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) p).comp
      (Integral.Measure.chartModelBasis E).repr.toLinearMap with hL
  set Lclm : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L with hLclm
  have hlin : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (n : ℕ) (fun y : E => Lclm y) := by
    rw [contMDiff_iff_contDiff]; exact Lclm.contDiff.of_le le_top
  exact hlin.contMDiffAt.comp_contMDiffWithinAt p₀ hf

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in

private theorem flow_chartGramMatrix_alpha_cmwa
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (J J_g : Set ℝ) (hJJ : J ⊆ J_g) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (J ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (J_g ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (α : M) (p q : Fin (Module.finrank ℝ E)) (n : ℕ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ J) (b₀ : M) (x₀ : M)
    (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hαbase : (Φ_fam t₀ : M → M) b₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
      (fun r : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (t₀, b₀) := by
  classical
  set S : Set (ℝ × M) := J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
    with hS
  set eα := trivializationAt E (TangentSpace I) α with heα
  have hntop : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)
  have hS_sub : S ⊆ J ×ˢ (Set.univ : Set M) := by
    rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
  have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
  have horbit_cwa : ContinuousWithinAt (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
    ((hjoint.continuousOn).mono hS_sub).continuousWithinAt ht₀b₀
  set S' : Set (ℝ × M) := S ∩ ((fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) ⁻¹' eα.baseSet)
    with hS'
  have hS'_mem : S' ∈ nhdsWithin (t₀, b₀) S := by
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    have hbnhds : eα.baseSet ∈ nhds ((Φ_fam t₀ : M → M) b₀) := eα.open_baseSet.mem_nhds hαbase
    exact horbit_cwa.preimage_mem_nhdsWithin hbnhds
  have hpair : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (n : ℕ)
      (fun r : ℝ × M => (r.1, (Φ_fam r.1 : M → M) r.2)) S' (t₀, b₀) := by
    have hfst : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (n : ℕ)
        (fun r : ℝ × M => r.1) S' (t₀, b₀) := contMDiffWithinAt_fst
    have hb₂S : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (n : ℕ)
        (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
      ((hjoint.of_le hntop) _ (hS_sub ht₀b₀)).mono hS_sub
    exact hfst.prodMk (hb₂S.mono Set.inter_subset_left)
  have hmaps : Set.MapsTo (fun r : ℝ × M => (r.1, (Φ_fam r.1 : M → M) r.2))
      S' (J_g ×ˢ eα.baseSet) := by
    rintro r ⟨hrS, hrpre⟩
    exact ⟨hJJ (hS_sub hrS).1, hrpre⟩
  have hgramAt : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
      (fun s : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_DT s.1) α s.2 p q)
      (J_g ×ˢ eα.baseSet) (t₀, (Φ_fam t₀ : M → M) b₀) :=
    ((hgram_DT α p q).of_le hntop) _ ⟨hJJ ht₀, hαbase⟩
  have hcompS' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
      (fun r : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
      S' (t₀, b₀) :=
    hgramAt.comp (t₀, b₀) hpair hmaps
  exact hcompS'.mono_of_mem_nhdsWithin hS'_mem

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in

private theorem flow_pushforward_chartCoord_continuousWithinAt
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (hΦsection_joint : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
        : TangentBundle I M))
      (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hΦorbit_joint : ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ico 0 T ×ˢ Set.univ))
    (α : M) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ico 0 T) (b₀ : M)
    (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hαbase : (Φ_fam t₀ : M → M) b₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousWithinAt (fun p : ℝ × M =>
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
          ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2
            (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)))
      (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (t₀, b₀) := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he
  set S : Set (ℝ × M) := Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet with hS
  set F : (ℝ × M) → TangentBundle I M := fun p : ℝ × M =>
    (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
      (mfderiv I I (Φ_fam p.1 : M → M) p.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
      : TangentBundle I M) with hF
  have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
  have hsec_cwa : ContinuousWithinAt F S (t₀, b₀) := hΦsection_joint.continuousWithinAt ht₀b₀
  have hsrc0 : F (t₀, b₀) ∈ e.source := by
    rw [hF, he, Bundle.Trivialization.mem_source]; exact hαbase
  have hcontTriv : ContinuousWithinAt (fun r : TangentBundle I M => (e r).2) e.source (F (t₀, b₀)) :=
    (e.continuousOn.continuousWithinAt hsrc0).snd
  have hpre : F ⁻¹' e.source ∈ nhdsWithin (t₀, b₀) S :=
    hsec_cwa.preimage_mem_nhdsWithin (e.open_source.mem_nhds hsrc0)
  have hcomp : ContinuousWithinAt (fun p : ℝ × M => (e (F p)).2) S (t₀, b₀) :=
    hcontTriv.comp_of_preimage_mem_nhdsWithin hsec_cwa hpre
  have horbit_cwa : ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) S (t₀, b₀) := by
    have hS_sub : S ⊆ Set.Ico 0 T ×ˢ (Set.univ : Set M) := by
      rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
    exact (hΦorbit_joint.mono hS_sub).continuousWithinAt ht₀b₀
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbnhds : e.baseSet ∈ nhds ((Φ_fam t₀ : M → M) b₀) := e.open_baseSet.mem_nhds hαbase
    have hpb : (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) ⁻¹' e.baseSet ∈ nhdsWithin (t₀, b₀) S :=
      horbit_cwa.preimage_mem_nhdsWithin hbnhds
    filter_upwards [hpb] with p hp
    change e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
      = (e (F p)).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hp,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hp]
  · change e.continuousLinearMapAt ℝ ((Φ_fam t₀ : M → M) b₀)
        (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ i b₀))
      = (e (F (t₀, b₀))).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hαbase,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hαbase]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private theorem chartModelBasis_repr_continuousWithinAt
    {S : Set (ℝ × M)} {p₀ : ℝ × M} {f : (ℝ × M) → E}
    (hf : ContinuousWithinAt f S p₀) (p : Fin (Module.finrank ℝ E)) :
    ContinuousWithinAt (fun q : ℝ × M => ((Integral.Measure.chartModelBasis E).repr (f q)) p)
      S p₀ := by
  have hlin : Continuous (fun y : E => ((Integral.Measure.chartModelBasis E).repr y) p) :=
    ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) p).comp
      (Integral.Measure.chartModelBasis E).repr.toLinearMap).continuous_of_finiteDimensional
  exact hlin.continuousWithinAt.comp hf (Set.mapsTo_univ _ _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private theorem cwa_finset_sum {ι : Type*} {N : Type*} [AddCommMonoid N] [TopologicalSpace N]
    [ContinuousAdd N] {f : ι → (ℝ × M) → N} (s : Finset ι) {t : Set (ℝ × M)} {x : ℝ × M}
    (h : ∀ i ∈ s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a : ℝ × M => ∑ i ∈ s, f i a) t x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousWithinAt_const
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in

private theorem flow_chartGramMatrix_alpha_continuousWithinAt
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦorbit_joint : ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ico 0 T ×ˢ Set.univ))
    (hgram0_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (α : M) (p q : Fin (Module.finrank ℝ E))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ico 0 T) (b₀ : M) (x₀ : M)
    (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hαbase : (Φ_fam t₀ : M → M) b₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousWithinAt
      (fun r : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
      (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (t₀, b₀) := by
  classical
  set S : Set (ℝ × M) := Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
    with hS
  set eα := trivializationAt E (TangentSpace I) α with heα
  have hS_sub : S ⊆ Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
    rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
  have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
  have horbit_cwa : ContinuousWithinAt (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
    (hΦorbit_joint.mono hS_sub).continuousWithinAt ht₀b₀
  set S' : Set (ℝ × M) := S ∩ ((fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) ⁻¹' eα.baseSet)
    with hS'
  have hS'_mem : S' ∈ nhdsWithin (t₀, b₀) S := by
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    have hbnhds : eα.baseSet ∈ nhds ((Φ_fam t₀ : M → M) b₀) := eα.open_baseSet.mem_nhds hαbase
    exact horbit_cwa.preimage_mem_nhdsWithin hbnhds
  have hpair : ContinuousWithinAt (fun r : ℝ × M => (r.1, (Φ_fam r.1 : M → M) r.2)) S' (t₀, b₀) := by
    have hfst : ContinuousWithinAt (fun r : ℝ × M => r.1) S' (t₀, b₀) :=
      continuous_fst.continuousWithinAt
    have hb₂S : ContinuousWithinAt (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
      horbit_cwa
    exact hfst.prodMk (hb₂S.mono Set.inter_subset_left)
  have hmaps : Set.MapsTo (fun r : ℝ × M => (r.1, (Φ_fam r.1 : M → M) r.2))
      S' (Set.Ico (0 : ℝ) T ×ˢ eα.baseSet) := by
    rintro r ⟨hrS, hrpre⟩
    exact ⟨(hS_sub hrS).1, hrpre⟩
  have hgramAt : ContinuousWithinAt
      (fun s : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g_DT s.1) α s.2 p q)
      (Set.Ico (0 : ℝ) T ×ˢ eα.baseSet) (t₀, (Φ_fam t₀ : M → M) b₀) :=
    (hgram0_DT α p q).continuousWithinAt ⟨ht₀, hαbase⟩
  have hcompS' :
      ContinuousWithinAt ((fun s : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT s.1) α s.2 p q) ∘
        (fun r : ℝ × M => (r.1, (Φ_fam r.1 : M → M) r.2))) S' (t₀, b₀) :=
    ContinuousWithinAt.comp_of_eq hgramAt hpair hmaps rfl
  have hcompS'' : ContinuousWithinAt
      (fun r : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
      S' (t₀, b₀) := by
    simpa only [Function.comp_def] using hcompS'
  exact hcompS''.mono_of_mem_nhdsWithin hS'_mem

omit [NeZero (Module.finrank ℝ E)] in
theorem conjugating_flow_pullback_jointGram_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram0_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hΦorbit_joint : ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ico 0 T ×ˢ Set.univ))
    (hΦsection_joint : ∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × M =>
        (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2
            (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)) : TangentBundle I M))
        (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
    (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) := by
  classical
  have hjoint := conjugating_flow_jointContMDiffOn (I := I) g_DT g_bg T Φ_fam hΦode hfield_reg
  constructor
  · intro x₀ i j
    rw [contMDiffOn_infty]
    intro n p₀ hp₀
    obtain ⟨ht₀, hb₀⟩ := hp₀
    set t₀ : ℝ := p₀.1
    set b₀ : M := p₀.2
    set α : M := (Φ_fam t₀ : M → M) b₀ with hα
    set e := trivializationAt E (TangentSpace I) α with he
    set S : Set (ℝ × M) := Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
      with hS
    have hp₀eq : p₀ = (t₀, b₀) := rfl
    have hS_sub : S ⊆ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
      rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
    have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
    have hbase0 : α ∈ e.baseSet := by
      rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
    have hαbase' : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet := by rw [← hα]; exact hbase0
    have hsummand : ∀ p q : Fin (Module.finrank ℝ E),
        ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
          (fun r : ℝ × M =>
            ((Integral.Measure.chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
                (mfderiv I I (Φ_fam r.1 : M → M) r.2
                  (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2)))) p *
            ((Integral.Measure.chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
                (mfderiv I I (Φ_fam r.1 : M → M) r.2
                  (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2)))) q *
            Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
          S (t₀, b₀) := by
      intro p q
      have hVi := flow_pushforward_chartCoord_cmwa (I := I) (Set.Ioo (0 : ℝ) T) Φ_fam hjoint
        x₀ i n t₀ ht₀ b₀ hb₀
      have hVj := flow_pushforward_chartCoord_cmwa (I := I) (Set.Ioo (0 : ℝ) T) Φ_fam hjoint
        x₀ j n t₀ ht₀ b₀ hb₀
      have hri := chartModelBasis_repr_cmwa (n := n) (S := S) (p₀ := (t₀, b₀)) hVi p
      have hrj := chartModelBasis_repr_cmwa (n := n) (S := S) (p₀ := (t₀, b₀)) hVj q
      have hG := flow_chartGramMatrix_alpha_cmwa (I := I) g_DT (Set.Ioo (0 : ℝ) T)
        (Set.Ioo (0 : ℝ) T) (subset_refl _) Φ_fam hjoint hgram_DT
        α p q n t₀ ht₀ b₀ x₀ hb₀ hαbase'
      exact (hri.mul hrj).mul hG
    have hsum : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
        (fun r : ℝ × M => ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
              (mfderiv I I (Φ_fam r.1 : M → M) r.2
                (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2)))) p *
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
              (mfderiv I I (Φ_fam r.1 : M → M) r.2
                (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2)))) q *
          Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
        S (t₀, b₀) :=
      ContMDiffWithinAt.sum (fun p _ => ContMDiffWithinAt.sum (fun q _ => hsummand p q))
    have horbit_cwa : ContinuousWithinAt (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
      ((hjoint.continuousOn).mono hS_sub).continuousWithinAt ht₀b₀
    have hsrc0 : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
    have hpre : (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) ⁻¹'
        (e.baseSet ∩ (extChartAt I α).source) ∈ nhdsWithin (t₀, b₀) S := by
      refine horbit_cwa.preimage_mem_nhdsWithin ((IsOpen.inter e.open_baseSet
        (isOpen_extChartAt_source (I := I) α)).mem_nhds ?_)
      exact ⟨hαbase', by rw [← hα]; exact hsrc0⟩
    refine hsum.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hpre] with r hr
      obtain ⟨hbE, hsr⟩ := hr
      rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
      have hexpand := g_inner_eq_chart_sum (I := I) (g_DT r.1) α hbE hsr
        (mfderiv I I (Φ_fam r.1 : M → M) r.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2))
        (mfderiv I I (Φ_fam r.1 : M → M) r.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2))
      rw [hexpand]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      have hgramEq : Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT r.1) α p q
            (extChartAt I α ((Φ_fam r.1 : M → M) r.2))
          = Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q := by
        unfold Integral.DivergenceTheorem.chartGramOnE
        rw [(extChartAt I α).left_inv hsr]
      rw [hgramEq]
    · obtain ⟨hbE0, hsr0⟩ : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet ∧
          (Φ_fam t₀ : M → M) b₀ ∈ (extChartAt I α).source := ⟨hαbase', by rw [← hα]; exact hsrc0⟩
      rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
      have hexpand := g_inner_eq_chart_sum (I := I) (g_DT t₀) α hbE0 hsr0
        (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ i b₀))
        (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ j b₀))
      rw [hexpand]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      have hgramEq : Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t₀) α p q
            (extChartAt I α ((Φ_fam t₀ : M → M) b₀))
          = Integral.Measure.chartGramMatrix (I := I) (g_DT t₀) α ((Φ_fam t₀ : M → M) b₀) p q := by
        unfold Integral.DivergenceTheorem.chartGramOnE
        rw [(extChartAt I α).left_inv hsr0]
      rw [hgramEq]
  · intro x₀ i j p₀ hp₀
    obtain ⟨ht₀, hb₀⟩ := hp₀
    set t₀ : ℝ := p₀.1
    set b₀ : M := p₀.2
    set α : M := (Φ_fam t₀ : M → M) b₀ with hα
    set e := trivializationAt E (TangentSpace I) α with he
    set S : Set (ℝ × M) := Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
      with hS
    have hS_sub : S ⊆ Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
      rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
    have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
    have hbase0 : α ∈ e.baseSet := by
      rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
    have hαbase' : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet := by rw [← hα]; exact hbase0
    have hsummand : ∀ p q : Fin (Module.finrank ℝ E),
        ContinuousWithinAt
          (fun r : ℝ × M =>
            ((Integral.Measure.chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
                (mfderiv I I (Φ_fam r.1 : M → M) r.2
                  (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2)))) p *
            ((Integral.Measure.chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
                (mfderiv I I (Φ_fam r.1 : M → M) r.2
                  (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2)))) q *
            Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
          S (t₀, b₀) := by
      intro p q
      have hVi := flow_pushforward_chartCoord_continuousWithinAt (I := I) T Φ_fam x₀ i
        (hΦsection_joint x₀ i) hΦorbit_joint α t₀ ht₀ b₀ hb₀ hαbase'
      have hVj := flow_pushforward_chartCoord_continuousWithinAt (I := I) T Φ_fam x₀ j
        (hΦsection_joint x₀ j) hΦorbit_joint α t₀ ht₀ b₀ hb₀ hαbase'
      have hri := chartModelBasis_repr_continuousWithinAt (S := S) (p₀ := (t₀, b₀)) hVi p
      have hrj := chartModelBasis_repr_continuousWithinAt (S := S) (p₀ := (t₀, b₀)) hVj q
      have hG := flow_chartGramMatrix_alpha_continuousWithinAt (I := I) g_DT T Φ_fam
        hΦorbit_joint hgram0_DT α p q t₀ ht₀ b₀ x₀ hb₀ hαbase'
      exact (hri.mul hrj).mul hG
    have hsum : ContinuousWithinAt
        (fun r : ℝ × M => ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
              (mfderiv I I (Φ_fam r.1 : M → M) r.2
                (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2)))) p *
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
              (mfderiv I I (Φ_fam r.1 : M → M) r.2
                (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2)))) q *
          Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
        S (t₀, b₀) := by
      refine cwa_finset_sum _ (fun p _ => ?_)
      exact cwa_finset_sum _ (fun q _ => hsummand p q)
    have horbit_cwa : ContinuousWithinAt (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
      (hΦorbit_joint.mono hS_sub).continuousWithinAt ht₀b₀
    have hsrc0 : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
    have hpre : (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) ⁻¹'
        (e.baseSet ∩ (extChartAt I α).source) ∈ nhdsWithin (t₀, b₀) S := by
      refine horbit_cwa.preimage_mem_nhdsWithin ((IsOpen.inter e.open_baseSet
        (isOpen_extChartAt_source (I := I) α)).mem_nhds ?_)
      exact ⟨hαbase', by rw [← hα]; exact hsrc0⟩
    refine hsum.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hpre] with r hr
      obtain ⟨hbE, hsr⟩ := hr
      rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
      have hexpand := g_inner_eq_chart_sum (I := I) (g_DT r.1) α hbE hsr
        (mfderiv I I (Φ_fam r.1 : M → M) r.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2))
        (mfderiv I I (Φ_fam r.1 : M → M) r.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2))
      rw [hexpand]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      have hgramEq : Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT r.1) α p q
            (extChartAt I α ((Φ_fam r.1 : M → M) r.2))
          = Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q := by
        unfold Integral.DivergenceTheorem.chartGramOnE
        rw [(extChartAt I α).left_inv hsr]
      rw [hgramEq]
    · obtain ⟨hbE0, hsr0⟩ : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet ∧
          (Φ_fam t₀ : M → M) b₀ ∈ (extChartAt I α).source := ⟨hαbase', by rw [← hα]; exact hsrc0⟩
      rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
      have hexpand := g_inner_eq_chart_sum (I := I) (g_DT t₀) α hbE0 hsr0
        (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ i b₀))
        (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ j b₀))
      rw [hexpand]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      have hgramEq : Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t₀) α p q
            (extChartAt I α ((Φ_fam t₀ : M → M) b₀))
          = Integral.Measure.chartGramMatrix (I := I) (g_DT t₀) α ((Φ_fam t₀ : M → M) b₀) p q := by
        unfold Integral.DivergenceTheorem.chartGramOnE
        rw [(extChartAt I α).left_inv hsr0]
      rw [hgramEq]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem conjugating_flow_pullback_jointGram_onesided
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  intro x₀ i j
  rw [contMDiffOn_infty]
  intro n p₀ hp₀
  obtain ⟨ht₀, hb₀⟩ := hp₀
  set t₀ : ℝ := p₀.1
  set b₀ : M := p₀.2
  set α : M := (Φ_fam t₀ : M → M) b₀ with hα
  set e := trivializationAt E (TangentSpace I) α with he
  set S : Set (ℝ × M) := Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
    with hS
  have hS_sub : S ⊆ Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
    rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
  have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
  have hbase0 : α ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hαbase' : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet := by rw [← hα]; exact hbase0
  have hsummand : ∀ p q : Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
        (fun r : ℝ × M =>
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
              (mfderiv I I (Φ_fam r.1 : M → M) r.2
                (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2)))) p *
          ((Integral.Measure.chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
              (mfderiv I I (Φ_fam r.1 : M → M) r.2
                (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2)))) q *
          Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
        S (t₀, b₀) := by
    intro p q
    have hVi := flow_pushforward_chartCoord_cmwa (I := I) (Set.Ico (0 : ℝ) T) Φ_fam hjoint
      x₀ i n t₀ ht₀ b₀ hb₀
    have hVj := flow_pushforward_chartCoord_cmwa (I := I) (Set.Ico (0 : ℝ) T) Φ_fam hjoint
      x₀ j n t₀ ht₀ b₀ hb₀
    have hri := chartModelBasis_repr_cmwa (n := n) (S := S) (p₀ := (t₀, b₀)) hVi p
    have hrj := chartModelBasis_repr_cmwa (n := n) (S := S) (p₀ := (t₀, b₀)) hVj q
    have hG := flow_chartGramMatrix_alpha_cmwa (I := I) g_DT (Set.Ico (0 : ℝ) T)
      (Set.Icc (0 : ℝ) T) Set.Ico_subset_Icc_self Φ_fam hjoint hgram_DT
      α p q n t₀ ht₀ b₀ x₀ hb₀ hαbase'
    exact (hri.mul hrj).mul hG
  have hsum : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (n : ℕ)
      (fun r : ℝ × M => ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
            (mfderiv I I (Φ_fam r.1 : M → M) r.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2)))) p *
        ((Integral.Measure.chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam r.1 : M → M) r.2)
            (mfderiv I I (Φ_fam r.1 : M → M) r.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2)))) q *
        Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q)
      S (t₀, b₀) :=
    ContMDiffWithinAt.sum (fun p _ => ContMDiffWithinAt.sum (fun q _ => hsummand p q))
  have horbit_cwa : ContinuousWithinAt (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) S (t₀, b₀) :=
    ((hjoint.continuousOn).mono hS_sub).continuousWithinAt ht₀b₀
  have hsrc0 : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
  have hpre : (fun r : ℝ × M => (Φ_fam r.1 : M → M) r.2) ⁻¹'
      (e.baseSet ∩ (extChartAt I α).source) ∈ nhdsWithin (t₀, b₀) S := by
    refine horbit_cwa.preimage_mem_nhdsWithin ((IsOpen.inter e.open_baseSet
      (isOpen_extChartAt_source (I := I) α)).mem_nhds ?_)
    exact ⟨hαbase', by rw [← hα]; exact hsrc0⟩
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with r hr
    obtain ⟨hbE, hsr⟩ := hr
    rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
    have hexpand := g_inner_eq_chart_sum (I := I) (g_DT r.1) α hbE hsr
      (mfderiv I I (Φ_fam r.1 : M → M) r.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ i r.2))
      (mfderiv I I (Φ_fam r.1 : M → M) r.2 (Integral.Measure.chartBasisVecFiber (I := I) x₀ j r.2))
    rw [hexpand]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    have hgramEq : Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT r.1) α p q
          (extChartAt I α ((Φ_fam r.1 : M → M) r.2))
        = Integral.Measure.chartGramMatrix (I := I) (g_DT r.1) α ((Φ_fam r.1 : M → M) r.2) p q := by
      unfold Integral.DivergenceTheorem.chartGramOnE
      rw [(extChartAt I α).left_inv hsr]
    rw [hgramEq]
  · obtain ⟨hbE0, hsr0⟩ : (Φ_fam t₀ : M → M) b₀ ∈ e.baseSet ∧
        (Φ_fam t₀ : M → M) b₀ ∈ (extChartAt I α).source := ⟨hαbase', by rw [← hα]; exact hsrc0⟩
    rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
    have hexpand := g_inner_eq_chart_sum (I := I) (g_DT t₀) α hbE0 hsr0
      (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ i b₀))
      (mfderiv I I (Φ_fam t₀ : M → M) b₀ (Integral.Measure.chartBasisVecFiber (I := I) x₀ j b₀))
    rw [hexpand]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    have hgramEq : Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t₀) α p q
          (extChartAt I α ((Φ_fam t₀ : M → M) b₀))
        = Integral.Measure.chartGramMatrix (I := I) (g_DT t₀) α ((Φ_fam t₀ : M → M) b₀) p q := by
      unfold Integral.DivergenceTheorem.chartGramOnE
      rw [(extChartAt I α).left_inv hsr0]
    rw [hgramEq]

end DifferentialGeometry.PDE.RicciFlow
