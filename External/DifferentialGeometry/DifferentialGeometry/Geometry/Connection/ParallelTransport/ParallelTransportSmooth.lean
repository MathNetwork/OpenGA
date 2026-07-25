import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic


def parallelTransportVF (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (s : ℝ) (y : E) : E :=
  - chartChristoffelContraction (I := I) g α
      (deriv (chartCurve (I := I) α γ) s) y (chartCurve (I := I) α γ s)


omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportVF_contDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {W : Set ℝ}
    (hW : IsOpen W)
    (hu_cd : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) W)
    (hu_int : ∀ s ∈ W,
      chartCurve (I := I) α γ s ∈ interior (extChartAt I α).target) :
    ContDiffOn ℝ ∞
      (Function.uncurry (parallelTransportVF (I := I) g α γ))
      (W ×ˢ (Set.univ : Set E)) := by
  classical
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hderiv_cd : ContDiffOn ℝ ∞ (deriv u) W :=
    hu_cd.deriv_of_isOpen hW (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
  have huncurry :
      Function.uncurry (parallelTransportVF (I := I) g α γ) =
        fun z : ℝ × E =>
          - ∑ k : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α i j k (u z.1) *
                    chartCoord (E := E) i (deriv u z.1) *
                    chartCoord (E := E) j z.2) •
                chartModelBasis E k := by
    funext z
    rfl
  rw [huncurry]
  refine ContDiffOn.neg ?_
  refine ContDiffOn.sum (fun k _ => ?_)
  refine ContDiffOn.smul ?_ contDiffOn_const
  refine ContDiffOn.sum (fun i _ => ?_)
  refine ContDiffOn.sum (fun j _ => ?_)
  have hΓ : ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartChristoffel (I := I) g α i j k (u z.1))
      (W ×ˢ (Set.univ : Set E)) := by
    have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α i j k
    have hcomp : ContDiffOn ℝ ∞ (fun z : ℝ × E => u z.1) (W ×ˢ (Set.univ : Set E)) :=
      hu_cd.comp contDiffOn_fst (fun z hz => hz.1)
    have hmaps : MapsTo (fun z : ℝ × E => u z.1) (W ×ˢ (Set.univ : Set E))
        (interior (extChartAt I α).target) :=
      fun z hz => hu_int z.1 hz.1
    exact hbase.comp hcomp hmaps
  have hvi : ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartCoord (E := E) i (deriv u z.1))
      (W ×ˢ (Set.univ : Set E)) := by
    have hCLM : ContDiff ℝ ∞ (((chartModelBasis E).coord i).toContinuousLinearMap) :=
      ((chartModelBasis E).coord i).toContinuousLinearMap.contDiff
    have hcomp : ContDiffOn ℝ ∞ (fun z : ℝ × E => deriv u z.1)
        (W ×ˢ (Set.univ : Set E)) :=
      hderiv_cd.comp contDiffOn_fst (fun z hz => hz.1)
    have hci : ContDiffOn ℝ ∞
        (fun z : ℝ × E => (((chartModelBasis E).coord i).toContinuousLinearMap)
          (deriv u z.1)) (W ×ˢ (Set.univ : Set E)) :=
      hCLM.comp_contDiffOn hcomp
    exact hci
  have hwj : ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartCoord (E := E) j z.2)
      (W ×ˢ (Set.univ : Set E)) := by
    have hCLM : ContDiff ℝ ∞ (((chartModelBasis E).coord j).toContinuousLinearMap) :=
      ((chartModelBasis E).coord j).toContinuousLinearMap.contDiff
    have hsnd : ContDiff ℝ ∞ (Prod.snd : ℝ × E → E) := contDiff_snd
    exact (hCLM.comp hsnd).contDiffOn
  exact (hΓ.mul hvi).mul hwj

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [InnerProductSpace ℝ E] in
theorem parallelTransport_section_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) L, covDerivAlong (I := I) g γ V t = 0) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t))
        (Set.Icc 0 L) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨V, hV0, hVdiff, hVpar⟩ :=
    exists_parallel_transport_on_Icc (I := I) g γ (N := 2) le_rfl
      (hγ.of_le (by exact_mod_cast le_top)) hL v₀
  refine ⟨V, hV0, hVdiff, hVpar, ?_⟩
  intro t₀ ht₀
  set α : M := γ t₀ with hα_def
  set Y : ℝ → E := chartRepAtBase (I := I) α γ V with hY_def
  set W₀ : Set ℝ := γ ⁻¹' (chartAt H α).source with hW₀_def
  have hW₀_open : IsOpen W₀ := (chartAt H α).open_source.preimage hγ.continuous
  have ht₀_W₀ : t₀ ∈ W₀ := by
    rw [hW₀_def, mem_preimage]; exact mem_chart_source H α
  obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hW₀_open t₀ ht₀_W₀
  set W : Set ℝ := Set.Ioo (t₀ - ε) (t₀ + ε) with hW_def
  have hW_open : IsOpen W := isOpen_Ioo
  have hW_sub_W₀ : W ⊆ W₀ := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht₀_W : t₀ ∈ W := ⟨by linarith, by linarith⟩
  set a : ℝ := max 0 (t₀ - ε / 2) with ha_def
  set b : ℝ := min L (t₀ + ε / 2) with hb_def
  have ht₀_lo : a ≤ t₀ := max_le ht₀.1 (by linarith)
  have ht₀_hi : t₀ ≤ b := le_min ht₀.2 (by linarith)
  have hab : a ≤ b := le_trans ht₀_lo ht₀_hi
  have hIcc_sub_Icc0L : Set.Icc a b ⊆ Set.Icc (0:ℝ) L := by
    intro s hs
    exact ⟨le_trans (le_max_left _ _) hs.1, le_trans hs.2 (min_le_left _ _)⟩
  have hIcc_sub_W : Set.Icc a b ⊆ W := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have : t₀ - ε / 2 ≤ s := le_trans (le_max_right _ _) hs.1
      linarith
    · have : s ≤ t₀ + ε / 2 := le_trans hs.2 (min_le_right _ _)
      linarith
  have hIcc_src : ∀ s ∈ Set.Icc a b, γ s ∈ (chartAt H α).source :=
    fun s hs => hW_sub_W₀ (hIcc_sub_W hs)
  have ht₀_mem_Icc : t₀ ∈ Set.Icc a b := ⟨ht₀_lo, ht₀_hi⟩
  have hIcc_eq : Set.Icc a b =
      Set.Icc (0:ℝ) L ∩ Set.Icc (t₀ - ε / 2) (t₀ + ε / 2) := by
    rw [ha_def, hb_def, Set.Icc_inter_Icc]
  have hIcc_nhdsWithin : Set.Icc a b ∈ 𝓝[Set.Icc (0:ℝ) L] t₀ := by
    rw [hIcc_eq]
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
  have hu_cd : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) W := by
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) W := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      exact hφ.comp hγ.contMDiffOn (fun s hs => hW_sub_W₀ hs)
    have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
    rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have hu_int : ∀ s ∈ W,
      chartCurve (I := I) α γ s ∈ interior (extChartAt I α).target := by
    intro s hs
    have hs_src : γ s ∈ (chartAt H α).source := hW_sub_W₀ hs
    have hs_ext_src : γ s ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hs_src
    have hur : chartCurve (I := I) α γ s = extChartAt I α (γ s) := by
      rw [chartCurve_def]
    rw [hur]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hs_ext_src)
  have hVF_cd : ContDiffOn ℝ ∞
      (Function.uncurry (parallelTransportVF (I := I) g α γ))
      (W ×ˢ (Set.univ : Set E)) :=
    parallelTransportVF_contDiffOn (I := I) g α γ hW_open hu_cd hu_int
  have hY_ode_at : ∀ s ∈ Set.Icc a b,
      HasDerivAt Y (parallelTransportVF (I := I) g α γ s (Y s)) s := by
    intro s hs
    have hs0L : s ∈ Set.Icc (0:ℝ) L := hIcc_sub_Icc0L hs
    have hs_src : γ s ∈ (chartAt H α).source := hIcc_src s hs
    have hVdiff_s : DifferentiableAt ℝ (chartRepAt (I := I) γ V s) s := hVdiff s hs0L
    have hY_diff_s : DifferentiableAt ℝ Y s := by
      rw [hY_def]
      exact chartRepAtBase_differentiableAt (I := I) (n := ∞) (by simp) g γ V s α hγ
        hs_src hVdiff_s
    have hY_hd : HasDerivAt Y (deriv Y s) s := hY_diff_s.hasDerivAt
    have hfoot :
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
            (chartCovDerivAlong (I := I) g α γ Y s) = 0 := by
      have hinv := covDerivAlong_chart_foot_invariance (I := I) (n := ∞) (by simp) g γ V s α
        hγ hs_src hVdiff_s
      rw [hY_def]
      rw [hinv]
      exact hVpar s hs0L
    have hbase : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hs_src
    have hchart_zero : chartCovDerivAlong (I := I) g α γ Y s = 0 := by
      have := congrArg
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s)) hfoot
      rw [(trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL
        (R := ℝ) hbase, map_zero] at this
      exact this
    rw [chartCovDerivAlong_def] at hchart_zero
    have hderiv_eq : deriv Y s = parallelTransportVF (I := I) g α γ s (Y s) := by
      rw [parallelTransportVF]
      exact eq_neg_of_add_eq_zero_left hchart_zero
    rw [hderiv_eq] at hY_hd
    exact hY_hd
  have hY_ode : ∀ s ∈ Set.Icc a b,
      HasDerivWithinAt Y (parallelTransportVF (I := I) g α γ s (Y s)) (Set.Icc a b) s :=
    fun s hs => (hY_ode_at s hs).hasDerivWithinAt
  have hY_smooth : ContDiffOn ℝ ∞ Y (Set.Icc a b) := by
    refine ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := parallelTransportVF (I := I) g α γ)
      (u := (Set.univ : Set E)) (n := (⊤ : ℕ∞)) ?_ ?_ ?_
    · exact hVF_cd.mono (Set.prod_mono hIcc_sub_W (le_refl _))
    · exact hY_ode
    · exact fun s _ => Set.mem_univ _
  have hY_cdwa : ContDiffWithinAt ℝ ∞ Y (Set.Icc (0:ℝ) L) t₀ :=
    (hY_smooth.contDiffWithinAt ht₀_mem_Icc).mono_of_mem_nhdsWithin hIcc_nhdsWithin
  have hY_cmwa : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Y (Set.Icc (0:ℝ) L) t₀ :=
    hY_cdwa.contMDiffWithinAt
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨(hγ t₀).contMDiffWithinAt, ?_⟩
  have hbase₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀)
  have hopen₀ : IsOpen (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
    (trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet
  have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t₀)).baseSet ∈ 𝓝[Set.Icc (0:ℝ) L] t₀ :=
    (hγ.continuous.continuousWithinAt).preimage_mem_nhdsWithin (hopen₀.mem_nhds hbase₀)
  have heq :
      (fun s => ((trivializationAt E (TangentSpace I) (γ t₀))
          (TotalSpace.mk' E (γ s) (V s))).2)
        =ᶠ[𝓝[Set.Icc (0:ℝ) L] t₀] Y := by
    filter_upwards [hpre] with s hs
    rw [hY_def, chartRepAtBase_apply]
    rw [(trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt_apply (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ t₀)).coe_linearMapAt_of_mem hs]
  exact hY_cmwa.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin ht₀)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [InnerProductSpace ℝ E] in
theorem parallelTransport_section_contMDiffOn_Ioo [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∃ (δ : ℝ) (_ : 0 < δ) (V : ∀ t, TangentSpace I (γ t)),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Ioo (-δ) (L + δ), DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo (-δ) (L + δ), covDerivAlong (I := I) g γ V t = 0) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t))
        (Set.Ioo (-δ) (L + δ)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨δ, hδ_pos, V, hV0, hVdiff, hVpar⟩ :=
    exists_global_parallel_transport_on_Ioo (I := I) g γ (N := 2) le_rfl
      (hγ.of_le (by exact_mod_cast le_top)) hL v₀
  refine ⟨δ, hδ_pos, V, hV0, hVdiff, hVpar, ?_⟩
  set Ω : Set ℝ := Set.Ioo (-δ) (L + δ) with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_Ioo
  intro t₀ ht₀
  have hmdat : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)) t₀ := by
    set α : M := γ t₀ with hα_def
    set Y : ℝ → E := chartRepAtBase (I := I) α γ V with hY_def
    set W₀ : Set ℝ := γ ⁻¹' (chartAt H α).source with hW₀_def
    have hW₀_open : IsOpen W₀ := (chartAt H α).open_source.preimage hγ.continuous
    have ht₀_W₀ : t₀ ∈ W₀ := by
      rw [hW₀_def, mem_preimage]; exact mem_chart_source H α
    have ht₀_inter : t₀ ∈ W₀ ∩ Ω := ⟨ht₀_W₀, ht₀⟩
    have hinter_open : IsOpen (W₀ ∩ Ω) := hW₀_open.inter hΩ_open
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hinter_open t₀ ht₀_inter
    set a : ℝ := t₀ - ε / 2 with ha_def
    set b : ℝ := t₀ + ε / 2 with hb_def
    have ht₀_lo : a ≤ t₀ := by rw [ha_def]; linarith
    have ht₀_hi : t₀ ≤ b := by rw [hb_def]; linarith
    have hab : a ≤ b := le_trans ht₀_lo ht₀_hi
    have hIcc_sub_inter : Set.Icc a b ⊆ W₀ ∩ Ω := by
      intro s hs
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      refine ⟨by rw [ha_def] at hs; linarith [hs.1], by rw [hb_def] at hs; linarith [hs.2]⟩
    have hIcc_sub_W₀ : Set.Icc a b ⊆ W₀ := fun s hs => (hIcc_sub_inter hs).1
    have hIcc_sub_Ω : Set.Icc a b ⊆ Ω := fun s hs => (hIcc_sub_inter hs).2
    have hIcc_src : ∀ s ∈ Set.Icc a b, γ s ∈ (chartAt H α).source :=
      fun s hs => hIcc_sub_W₀ hs
    have ht₀_mem_Icc : t₀ ∈ Set.Icc a b := ⟨ht₀_lo, ht₀_hi⟩
    have hIcc_nhds : Set.Icc a b ∈ 𝓝 t₀ :=
      Icc_mem_nhds (by rw [ha_def]; linarith) (by rw [hb_def]; linarith)
    set W : Set ℝ := Set.Ioo (t₀ - ε) (t₀ + ε) with hW_def
    have hW_open : IsOpen W := isOpen_Ioo
    have hW_sub_inter : W ⊆ W₀ ∩ Ω := by
      intro s hs
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by rw [hW_def] at hs; linarith [hs.1], by rw [hW_def] at hs; linarith [hs.2]⟩
    have hW_sub_W₀ : W ⊆ W₀ := fun s hs => (hW_sub_inter hs).1
    have ht₀_W : t₀ ∈ W := ⟨by linarith, by linarith⟩
    have hIcc_sub_W : Set.Icc a b ⊆ W := by
      intro s hs
      rw [hW_def]
      refine ⟨?_, ?_⟩
      · rw [ha_def] at hs; linarith [hs.1]
      · rw [hb_def] at hs; linarith [hs.2]
    have hu_cd : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) W := by
      have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) W := by
        have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
        exact hφ.comp hγ.contMDiffOn (fun s hs => hW_sub_W₀ hs)
      have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
      rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
    have hu_int : ∀ s ∈ W,
        chartCurve (I := I) α γ s ∈ interior (extChartAt I α).target := by
      intro s hs
      have hs_src : γ s ∈ (chartAt H α).source := hW_sub_W₀ hs
      have hs_ext_src : γ s ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact hs_src
      have hur : chartCurve (I := I) α γ s = extChartAt I α (γ s) := by
        rw [chartCurve_def]
      rw [hur]
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source hs_ext_src)
    have hVF_cd : ContDiffOn ℝ ∞
        (Function.uncurry (parallelTransportVF (I := I) g α γ))
        (W ×ˢ (Set.univ : Set E)) :=
      parallelTransportVF_contDiffOn (I := I) g α γ hW_open hu_cd hu_int
    have hY_ode_at : ∀ s ∈ Set.Icc a b,
        HasDerivAt Y (parallelTransportVF (I := I) g α γ s (Y s)) s := by
      intro s hs
      have hsΩ : s ∈ Ω := hIcc_sub_Ω hs
      have hs_src : γ s ∈ (chartAt H α).source := hIcc_src s hs
      have hVdiff_s : DifferentiableAt ℝ (chartRepAt (I := I) γ V s) s := hVdiff s hsΩ
      have hY_diff_s : DifferentiableAt ℝ Y s := by
        rw [hY_def]
        exact chartRepAtBase_differentiableAt (I := I) (n := ∞) (by simp) g γ V s α hγ
          hs_src hVdiff_s
      have hY_hd : HasDerivAt Y (deriv Y s) s := hY_diff_s.hasDerivAt
      have hfoot :
          (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
              (chartCovDerivAlong (I := I) g α γ Y s) = 0 := by
        have hinv := covDerivAlong_chart_foot_invariance (I := I) (n := ∞) (by simp) g γ V s α
          hγ hs_src hVdiff_s
        rw [hY_def]
        rw [hinv]
        exact hVpar s hsΩ
      have hbase : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hs_src
      have hchart_zero : chartCovDerivAlong (I := I) g α γ Y s = 0 := by
        have := congrArg
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s)) hfoot
        rw [(trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL
          (R := ℝ) hbase, map_zero] at this
        exact this
      rw [chartCovDerivAlong_def] at hchart_zero
      have hderiv_eq : deriv Y s = parallelTransportVF (I := I) g α γ s (Y s) := by
        rw [parallelTransportVF]
        exact eq_neg_of_add_eq_zero_left hchart_zero
      rw [hderiv_eq] at hY_hd
      exact hY_hd
    have hY_ode : ∀ s ∈ Set.Icc a b,
        HasDerivWithinAt Y (parallelTransportVF (I := I) g α γ s (Y s)) (Set.Icc a b) s :=
      fun s hs => (hY_ode_at s hs).hasDerivWithinAt
    have hY_smooth : ContDiffOn ℝ ∞ Y (Set.Icc a b) := by
      refine ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
        (f := parallelTransportVF (I := I) g α γ)
        (u := (Set.univ : Set E)) (n := (⊤ : ℕ∞)) ?_ ?_ ?_
      · exact hVF_cd.mono (Set.prod_mono hIcc_sub_W (le_refl _))
      · exact hY_ode
      · exact fun s _ => Set.mem_univ _
    have hY_cdat : ContDiffAt ℝ ∞ Y t₀ :=
      (hY_smooth.contDiffWithinAt ht₀_mem_Icc).contDiffAt hIcc_nhds
    have hY_cmat : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Y t₀ :=
      hY_cdat.contMDiffAt
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨hγ t₀, ?_⟩
    have hbase₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀)
    have hopen₀ : IsOpen (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
      (trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet
    have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t₀)).baseSet ∈ 𝓝 t₀ :=
      (hγ.continuous.continuousAt).preimage_mem_nhds (hopen₀.mem_nhds hbase₀)
    have heq :
        (fun s => ((trivializationAt E (TangentSpace I) (γ t₀))
            (TotalSpace.mk' E (γ s) (V s))).2)
          =ᶠ[𝓝 t₀] Y := by
      filter_upwards [hpre] with s hs
      rw [hY_def, chartRepAtBase_apply]
      rw [(trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt_apply (R := ℝ)]
      rw [(trivializationAt E (TangentSpace I) (γ t₀)).coe_linearMapAt_of_mem hs]
    exact hY_cmat.congr_of_eventuallyEq heq
  exact hmdat.contMDiffWithinAt

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
