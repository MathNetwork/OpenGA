import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.CorrectedChartSpatialC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.CorrectedChartPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.CorrectedBareVelocity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Bijective.UniformBijective
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus















namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle MeasureTheory
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in




private lemma intervalIntegrable_chartTrivRepr_along_orbit
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (g : ℝ → E) (Tα C s : ℝ)
    (hs0 : 0 ≤ s) (hsT : s ≤ Tα)
    (hderiv : ∀ u ∈ Set.Icc (0 : ℝ) Tα,
      HasDerivWithinAt g (chartTrivRepr (I := I) α (X u) (g u)) (Set.Icc (0 : ℝ) Tα) u)
    (hbd : ∀ u ∈ Set.Icc (0 : ℝ) Tα, ‖chartTrivRepr (I := I) α (X u) (g u)‖ ≤ C) :
    IntervalIntegrable (fun u : ℝ => chartTrivRepr (I := I) α (X u) (g u)) volume 0 s := by
  set φ : ℝ → E := fun u => chartTrivRepr (I := I) α (X u) (g u) with hφ
  have hφ_eq : ∀ u ∈ Set.Ioo (0 : ℝ) s, derivWithin g (Set.Ici u) u = φ u := by
    intro u hu
    have huT : u ∈ Set.Icc (0 : ℝ) Tα := ⟨hu.1.le, (lt_of_lt_of_le hu.2 hsT).le⟩
    have hmem : Set.Icc (0 : ℝ) Tα ∈ 𝓝[Set.Ici u] u := by
      refine Filter.mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le hu.2 hsT)) ?_
      exact Set.Icc_subset_Icc_left hu.1.le
    have hdIci : HasDerivWithinAt g (φ u) (Set.Ici u) u :=
      (hderiv u huT).mono_of_mem_nhdsWithin hmem
    exact hdIci.derivWithin (uniqueDiffWithinAt_Ici u)
  have hrestrict : volume.restrict (Set.Ioc (0 : ℝ) s) = volume.restrict (Set.Ioo (0 : ℝ) s) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hbd_ae : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) s)),
      ‖derivWithin g (Set.Ici u) u‖ ≤ C := by
    rw [hrestrict]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun u hu => ?_)
    rw [hφ_eq u hu]
    exact hbd u ⟨hu.1.le, (lt_of_lt_of_le hu.2 hsT).le⟩
  have hII_deriv : IntervalIntegrable (fun u : ℝ => derivWithin g (Set.Ici u) u) volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs0]
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_derivWithin_Ici g).aestronglyMeasurable hbd_ae
  refine hII_deriv.congr_ae ?_
  rw [Set.uIoc_of_le hs0, hrestrict]
  exact ae_restrict_of_forall_mem measurableSet_Ioo (fun u hu => hφ_eq u hu)






omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem corrected_chart_anchor_flow_build
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hCont : ContinuousOn (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2)) (Set.univ : Set (ℝ × M)))
    (hgrad : ∀ α : M, ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartTrivRepr (I := I) α (X q.1) z) (extChartAt I α q.2)) (Set.univ : Set (ℝ × M)))
    (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ (σ : ℝ) (_ : 0 < σ) (Φ0 : ℝ → M → M),
      (∀ x : M, Φ0 0 x = x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) σ, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ0 s x) (Set.Ioo (0 : ℝ) σ) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ0 t x)))) ∧
      (∀ x : M, ∃ α : M, ∃ δ : ℝ, ∃ C : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
        ∀ s ∈ Set.Ico (0 : ℝ) (min δ σ), Φ0 s x ∈ (chartAt H α).source ∧
          (extChartAt I α (Φ0 s x) = extChartAt I α x + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X r) (extChartAt I α (Φ0 r x)))
          ∧ ‖chartTrivRepr (I := I) α (X s) (extChartAt I α (Φ0 s x))‖ ≤ C) ∧
      (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ0 s x) (Set.Ici (0 : ℝ)) 0) := by
  classical
  set center : M → E := fun α => I ((chartAt H α) α) with hcenter



  have hper : ∀ α : M, ∃ (Tα rα r'α Cα : ℝ),
      0 < Tα ∧ 0 < rα ∧ 0 < r'α ∧ 0 ≤ Cα ∧
      Metric.closedBall (center α) rα ⊆ (extChartAt I α).target ∧
      ∃ flowα : E → ℝ → E,
        ∀ y ∈ Metric.closedBall (center α) r'α,
          flowα y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) Tα,
            HasDerivWithinAt (flowα y) (chartTrivRepr (I := I) α (X t) (flowα y t)) (Set.Icc (0 : ℝ) Tα) t ∧
            flowα y t ∈ Metric.closedBall (center α) rα ∧
            ‖chartTrivRepr (I := I) α (X t) (flowα y t)‖ ≤ Cα := by
    intro α
    obtain ⟨L, K, rα, hL, hrα, hK, hContBall, hLipBall, hsub⟩ :=
      corrected_chart_field_lipschitz_of_data (I := I) X α T hT hCont (hgrad α) hint
    obtain ⟨Tα, hTα, r'α, hr'α, Cα, hCα, flowα, hflowα⟩ :=
      corrected_chart_local_picard_from_zero (I := I) X α rα hrα hCont ⟨L, K, hL, hK, hContBall, hLipBall⟩
    exact ⟨Tα, rα, r'α, Cα, hTα, hrα, hr'α, hCα, hsub, flowα, hflowα⟩
  choose! Tα rα r'α Cα hTα hrα hr'α hCα hsub flowα hflowα using hper


  set U : M → Set M := fun α =>
    (chartAt H α).source ∩ ((chartAt H α) ⁻¹' (I ⁻¹' Metric.ball (center α) (r'α α))) with hU
  have hU_open : ∀ α : M, IsOpen (U α) := by
    intro α
    refine (((chartAt H α).continuousOn).isOpen_inter_preimage (chartAt H α).open_source ?_)
    exact Metric.isOpen_ball.preimage I.continuous_toFun
  have hU_mem : ∀ α : M, α ∈ U α := fun α =>
    ⟨mem_chart_source H α, Metric.mem_ball_self (hr'α α)⟩
  have hU_initial : ∀ α : M, ∀ x ∈ U α,
      extChartAt I α x ∈ Metric.closedBall (center α) (r'α α) := by
    intro α x hx
    rw [extChartAt_coe]
    exact Metric.ball_subset_closedBall hx.2

  have hCover : (Set.univ : Set M) ⊆ ⋃ α : M, U α := fun x _ =>
    Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hU_open hCover
  have hMem : ∀ x : M, ∃ α ∈ S, x ∈ U α := by
    intro x
    rcases Set.mem_iUnion₂.mp (hS (Set.mem_univ x)) with ⟨α, hαS, hxU⟩
    exact ⟨α, hαS, hxU⟩
  set αRep : M → M := fun x => (hMem x).choose with hαRep
  have hαRep_U : ∀ x : M, x ∈ U (αRep x) := fun x => (hMem x).choose_spec.2
  have hαRep_S : ∀ x : M, αRep x ∈ S := fun x => (hMem x).choose_spec.1

  obtain ⟨σ, hσ_pos, hσ_le⟩ :
      ∃ σ : ℝ, 0 < σ ∧ ∀ x : M, σ ≤ Tα (αRep x) := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · refine ⟨1, one_pos, fun x => ?_⟩
      exact absurd (hαRep_S x) (by rw [hSe]; exact Finset.notMem_empty _)
    · refine ⟨(S.image Tα).min' (by rw [Finset.image_nonempty]; exact hSne), ?_, fun x => ?_⟩
      · obtain ⟨α₀, _, hα₀⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image Tα) _)
        rw [← hα₀]; exact hTα α₀
      · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨αRep x, hαRep_S x, rfl⟩)

  set Φ0 : ℝ → M → M := fun s x =>
    (extChartAt I (αRep x)).symm (flowα (αRep x) (extChartAt I (αRep x) x) s) with hΦ0


  have hxsrc : ∀ x : M, x ∈ (chartAt H (αRep x)).source := fun x => (hαRep_U x).1
  have hxinit : ∀ x : M,
      extChartAt I (αRep x) x ∈ Metric.closedBall (center (αRep x)) (r'α (αRep x)) :=
    fun x => hU_initial (αRep x) x (hαRep_U x)
  have hspec : ∀ x : M,
      flowα (αRep x) (extChartAt I (αRep x) x) 0 = extChartAt I (αRep x) x ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (Tα (αRep x)),
        HasDerivWithinAt (flowα (αRep x) (extChartAt I (αRep x) x))
          (chartTrivRepr (I := I) (αRep x) (X t) (flowα (αRep x) (extChartAt I (αRep x) x) t))
          (Set.Icc (0 : ℝ) (Tα (αRep x))) t ∧
        flowα (αRep x) (extChartAt I (αRep x) x) t ∈ Metric.closedBall (center (αRep x)) (rα (αRep x)) ∧
        ‖chartTrivRepr (I := I) (αRep x) (X t) (flowα (αRep x) (extChartAt I (αRep x) x) t)‖ ≤ Cα (αRep x) :=
    fun x => hflowα (αRep x) (extChartAt I (αRep x) x) (hxinit x)

  have hxsrc_ext : ∀ x : M, x ∈ (extChartAt I (αRep x)).source := by
    intro x; rw [extChartAt_source]; exact hxsrc x
  have hΦ0_init : ∀ x : M, Φ0 0 x = x := by
    intro x
    change (extChartAt I (αRep x)).symm (flowα (αRep x) (extChartAt I (αRep x) x) 0) = x
    rw [(hspec x).1]
    exact (extChartAt I (αRep x)).left_inv (hxsrc_ext x)

  have hconf : ∀ x : M, ∀ t ∈ Set.Icc (0 : ℝ) (Tα (αRep x)),
      flowα (αRep x) (extChartAt I (αRep x) x) t ∈ (extChartAt I (αRep x)).target := by
    intro x t ht
    exact hsub (αRep x) ((hspec x).2 t ht).2.1


  have horbit_cont : ∀ x : M,
      ContinuousWithinAt (fun s : ℝ => Φ0 s x) (Set.Ici (0 : ℝ)) 0 := by
    intro x
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Tα (αRep x)) := ⟨le_refl 0, (hTα (αRep x)).le⟩
    have hg_cont : ContinuousWithinAt (flowα (αRep x) (extChartAt I (αRep x) x))
        (Set.Icc (0 : ℝ) (Tα (αRep x))) 0 :=
      (((hspec x).2 0 h0mem).1).continuousWithinAt
    have hg0_target : flowα (αRep x) (extChartAt I (αRep x) x) 0 ∈ (extChartAt I (αRep x)).target := by
      rw [(hspec x).1]; exact (extChartAt I (αRep x)).map_source (hxsrc_ext x)
    have hsymm_cont : ContinuousAt (extChartAt I (αRep x)).symm
        (flowα (αRep x) (extChartAt I (αRep x) x) 0) :=
      continuousAt_extChartAt_symm'' hg0_target
    have hcomp : ContinuousWithinAt
        (fun s : ℝ => (extChartAt I (αRep x)).symm (flowα (αRep x) (extChartAt I (αRep x) x) s))
        (Set.Icc (0 : ℝ) (Tα (αRep x))) 0 :=
      hsymm_cont.comp_continuousWithinAt hg_cont
    refine hcomp.mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Ico_mem_nhdsGE (hTα (αRep x))) Set.Ico_subset_Icc_self
  refine ⟨σ, hσ_pos, Φ0, hΦ0_init, ?_, ?_, horbit_cont⟩
  ·


    intro t ht x
    have hIoo_sub : Set.Ioo (0 : ℝ) σ ⊆ Set.Icc (0 : ℝ) (Tα (αRep x)) := fun s hs =>
      ⟨hs.1.le, (lt_of_lt_of_le hs.2 (hσ_le x)).le⟩
    have hconf' : ∀ u ∈ Set.Ioo (0 : ℝ) σ,
        flowα (αRep x) (extChartAt I (αRep x) x) u ∈ (extChartAt I (αRep x)).target := fun u hu =>
      hconf x u (hIoo_sub hu)
    have hode' : ∀ u ∈ Set.Ioo (0 : ℝ) σ,
        HasDerivWithinAt (flowα (αRep x) (extChartAt I (αRep x) x))
          (chartTrivRepr (I := I) (αRep x) (X u) (flowα (αRep x) (extChartAt I (αRep x) x) u))
          (Set.Ioo (0 : ℝ) σ) u := fun u hu =>
      (((hspec x).2 u (hIoo_sub hu)).1).mono hIoo_sub
    exact corrected_chartflow_eq_bareflow (I := I) X (αRep x)
      (flowα (αRep x)) (extChartAt I (αRep x) x) hconf' hode' t ht
  ·



    intro x
    set α := αRep x with hαdef
    set ext := extChartAt I α with hextdef
    set g : ℝ → E := flowα α (ext x) with hgdef
    refine ⟨α, Tα α, Cα α, hTα α, hxsrc x, fun s hs => ?_⟩
    obtain ⟨hs0, hsmin⟩ := hs
    rw [lt_min_iff] at hsmin
    obtain ⟨hsTα, hsσ⟩ := hsmin
    have hsIcc : s ∈ Set.Icc (0 : ℝ) (Tα α) := ⟨hs0, hsTα.le⟩

    have hgs_target : g s ∈ ext.target := hconf x s hsIcc
    have hext_round : ∀ u ∈ Set.Icc (0 : ℝ) (Tα α), ext ((ext).symm (g u)) = g u := fun u hu =>
      (ext).right_inv (hconf x u hu)
    have hΦ0_eq : ∀ u : ℝ, Φ0 u x = (ext).symm (g u) := fun u => rfl

    have hΦ0s_src : Φ0 s x ∈ (chartAt H α).source := by
      rw [hΦ0_eq s, ← extChartAt_source (I := I) α]
      exact (ext).map_target hgs_target
    refine ⟨hΦ0s_src, ?_, ?_⟩
    ·
      have hg'_full : ∀ u ∈ Set.Icc (0 : ℝ) (Tα α),
          HasDerivWithinAt g (chartTrivRepr (I := I) α (X u) (g u)) (Set.Icc (0 : ℝ) (Tα α)) u :=
        fun u hu => ((hspec x).2 u hu).1
      have hbd_full : ∀ u ∈ Set.Icc (0 : ℝ) (Tα α),
          ‖chartTrivRepr (I := I) α (X u) (g u)‖ ≤ Cα α := fun u hu => ((hspec x).2 u hu).2.2
      have hsub_s : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) (Tα α) :=
        Set.Icc_subset_Icc_right hsTα.le
      have hcont_g : ContinuousOn g (Set.Icc (0 : ℝ) s) :=
        HasDerivWithinAt.continuousOn (fun u hu => (hg'_full u (hsub_s hu)).mono hsub_s)
      have hderiv_Ioi : ∀ u ∈ Set.Ioo (0 : ℝ) s,
          HasDerivWithinAt g (chartTrivRepr (I := I) α (X u) (g u)) (Set.Ioi u) u := by
        intro u hu
        have huIcc : u ∈ Set.Icc (0 : ℝ) (Tα α) := ⟨hu.1.le, (lt_trans hu.2 hsTα).le⟩
        have hmem : Set.Icc (0 : ℝ) (Tα α) ∈ 𝓝[Set.Ici u] u :=
          Filter.mem_of_superset (Icc_mem_nhdsGE (lt_trans hu.2 hsTα))
            (Set.Icc_subset_Icc_left hu.1.le)
        exact ((hg'_full u huIcc).mono_of_mem_nhdsWithin hmem).Ioi_of_Ici
      have hint_g : IntervalIntegrable
          (fun u : ℝ => chartTrivRepr (I := I) α (X u) (g u)) volume 0 s :=
        intervalIntegrable_chartTrivRepr_along_orbit (I := I) X α g (Tα α) (Cα α) s hs0 hsTα.le
          hg'_full hbd_full
      have hFTC : (∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X r) (g r)) = g s - g 0 :=
        intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs0 hcont_g hderiv_Ioi hint_g
      have hg0 : g 0 = ext x := (hspec x).1
      have hcongr_integrand : Set.EqOn
          (fun r => chartTrivRepr (I := I) α (X r) (ext (Φ0 r x)))
          (fun r => chartTrivRepr (I := I) α (X r) (g r))
          (Set.uIcc (0 : ℝ) s) := by
        intro r hr
        rw [Set.uIcc_of_le hs0, Set.mem_Icc] at hr
        simp only [hΦ0_eq r, hext_round r ⟨hr.1, hr.2.trans hsTα.le⟩]
      calc ext (Φ0 s x)
          = g s := by rw [hΦ0_eq s, hext_round s hsIcc]
        _ = ext x + (g s - g 0) := by rw [hg0]; abel
        _ = ext x + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X r) (g r) := by rw [hFTC]
        _ = ext x + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X r) (ext (Φ0 r x)) := by
            rw [intervalIntegral.integral_congr hcongr_integrand]
    ·
      rw [hΦ0_eq s, hext_round s hsIcc]
      exact ((hspec x).2 s hsIcc).2.2

end DifferentialGeometry.PDE.RicciFlow.ODE
