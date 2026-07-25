import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBound
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.Transition
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

namespace Euclidean

private lemma indicator_eq_indicator_of_tsupport_subset
    {α : Type*} [Zero α]
    {X : Type*} [TopologicalSpace X] {f : X → α}
    {Ω Ω' : Set X} (hΩΩ' : Ω' ⊆ Ω)
    (hf_supp : tsupport f ⊆ Ω') :
    Ω.indicator f = Ω'.indicator f := by
  funext x
  by_cases hxΩ' : x ∈ Ω'
  · simp [Set.indicator_of_mem hxΩ', Set.indicator_of_mem (hΩΩ' hxΩ')]
  · simp only [Set.indicator_of_notMem hxΩ']
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
      have hx_off : x ∉ tsupport f := fun h => hxΩ' (hf_supp h)
      exact image_eq_zero_of_notMem_tsupport hx_off
    · simp [Set.indicator_of_notMem hxΩ]

private lemma eLpNorm_restrict_eq_of_tsupport_subset
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}
    {α : Type*} [NormedAddCommGroup α] {p : ℝ≥0∞}
    {f : X → α}
    {Ω Ω' : Set X} (hΩ_meas : MeasurableSet Ω) (hΩ'_meas : MeasurableSet Ω')
    (hΩΩ' : Ω' ⊆ Ω) (hf_supp : tsupport f ⊆ Ω') :
    eLpNorm f p (μ.restrict Ω) = eLpNorm f p (μ.restrict Ω') := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hΩ'_meas]
  rw [indicator_eq_indicator_of_tsupport_subset hΩΩ' hf_supp]

lemma wkpNorm_eq_of_compactSupport_smooth_subset
    {d : ℕ} [NeZero d]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) 1 p ψ Ω = iteratedWeakSobolevNorm (d := d) 1 p ψ Ω' := by
  classical
  have hψ_mem_Ω : MemWkp (d := d) 1 p ψ Ω :=
    MemWkp_of_smooth_compactSupport_pub
      (d := d) hΩ hψ_smooth hψ_cpt (hψ_supp.trans hΩΩ') hp_one 1
  have hψ_mem_Ω' : MemWkp (d := d) 1 p ψ Ω' :=
    MemWkp_of_smooth_compactSupport_pub
      (d := d) hΩ' hψ_smooth hψ_cpt hψ_supp hp_one 1
  have h_partial_classical_Ω : ∀ i : Fin d,
      chosenWeakPartial' (d := d) p i ψ Ω =ᵐ[volume.restrict Ω]
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
    intro i
    have hψ_W1p_Ω : DeGiorgi.MemW1p p ψ Ω := by
      have h := hψ_mem_Ω
      rw [MemWkp_succ] at h
      exact h.1
    have h_chosen := chosenWeakPartial'_isWeakPartial_of_mem hψ_W1p_Ω i
    have h_classical :
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ψ Ω :=
      DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ
        (hψ_smooth.of_le (by norm_cast))
    have h_chosen_loc : LocallyIntegrable
        (chosenWeakPartial' (d := d) p i ψ Ω) (volume.restrict Ω) := by
      have hmem : MeasureTheory.MemLp
          (chosenWeakPartial' (d := d) p i ψ Ω) p (volume.restrict Ω) :=
        chosenWeakPartial'_memLp_of_mem hψ_W1p_Ω i
      exact hmem.locallyIntegrable hp_one
    have h_classical_loc : LocallyIntegrable
        (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have h_cont : Continuous
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
      exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ h_chosen h_classical
      h_chosen_loc h_classical_loc
  have h_partial_classical_Ω' : ∀ i : Fin d,
      chosenWeakPartial' (d := d) p i ψ Ω' =ᵐ[volume.restrict Ω']
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
    intro i
    have hψ_W1p_Ω' : DeGiorgi.MemW1p p ψ Ω' := by
      have h := hψ_mem_Ω'
      rw [MemWkp_succ] at h
      exact h.1
    have h_chosen := chosenWeakPartial'_isWeakPartial_of_mem hψ_W1p_Ω' i
    have h_classical :
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ψ Ω' :=
      DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ'
        (hψ_smooth.of_le (by norm_cast))
    have h_chosen_loc : LocallyIntegrable
        (chosenWeakPartial' (d := d) p i ψ Ω') (volume.restrict Ω') := by
      have hmem : MeasureTheory.MemLp
          (chosenWeakPartial' (d := d) p i ψ Ω') p (volume.restrict Ω') :=
        chosenWeakPartial'_memLp_of_mem hψ_W1p_Ω' i
      exact hmem.locallyIntegrable hp_one
    have h_classical_loc : LocallyIntegrable
        (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω') := by
      have h_cont : Continuous
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
      exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ' h_chosen h_classical
      h_chosen_loc h_classical_loc
  have h_classical_cpt : ∀ i : Fin d, HasCompactSupport
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
    intro i
    exact hψ_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_classical_supp : ∀ i : Fin d,
      tsupport (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ⊆ Ω' := by
    intro i
    refine subset_trans ?_ hψ_supp
    exact tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_ψ_eLp : eLpNorm ψ p (volume.restrict Ω) = eLpNorm ψ p (volume.restrict Ω') :=
    eLpNorm_restrict_eq_of_tsupport_subset hΩ_meas hΩ'_meas hΩΩ' hψ_supp
  have h_partial_eLp : ∀ i : Fin d,
      eLpNorm (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
          p (volume.restrict Ω) =
      eLpNorm (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
          p (volume.restrict Ω') := by
    intro i
    exact eLpNorm_restrict_eq_of_tsupport_subset hΩ_meas hΩ'_meas hΩΩ'
      (h_classical_supp i)
  let _ := h_classical_cpt
  unfold iteratedWeakSobolevNorm
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
    fun α => by funext i; exact i.elim0
  haveI : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (h0_unique α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α ψ Ω) p (volume.restrict Ω))]
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α ψ Ω') p (volume.restrict Ω'))]
  simp only [iterWeakPartial_zero]
  rw [h_ψ_eLp]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro α _
  have h_iter1_Ω :
      iterWeakPartial (d := d) p 1 α ψ Ω =
      chosenWeakPartial' (d := d) p (α 0) ψ Ω := by
    rw [iterWeakPartial_succ]; rfl
  have h_iter1_Ω' :
      iterWeakPartial (d := d) p 1 α ψ Ω' =
      chosenWeakPartial' (d := d) p (α 0) ψ Ω' := by
    rw [iterWeakPartial_succ]; rfl
  rw [h_iter1_Ω, h_iter1_Ω']
  rw [eLpNorm_congr_ae (h_partial_classical_Ω (α 0))]
  rw [eLpNorm_congr_ae (h_partial_classical_Ω' (α 0))]
  exact h_partial_eLp (α 0)

end Euclidean

namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma crossChartK_isCompact
    [T2Space M] [SigmaCompactSpace M]
    (γ : M) {K_α : Set M} (hK_compact : IsCompact K_α) :
    IsCompact (K_α ∩ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  hK_compact.inter_right (isClosed_tsupport _)

private lemma crossChartK_subset_chartα_source
    [T2Space M] [SigmaCompactSpace M]
    (γ α : M) {K_α : Set M}
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    K_α ∩ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source := by
  intro x hx
  exact hK_α_in_α hx.1

private lemma crossChartK_subset_chartγ_source
    [T2Space M] [SigmaCompactSpace M]
    (γ : M) {K_α : Set M} :
    K_α ∩ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H γ).source := by
  intro x hx
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ hx.2

theorem chartTransition_smoothDiffeoBoundedAtOrder_strict
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (γ α : M)
    {K : Set M} (hK_compact : IsCompact K)
    (hK_γ : K ⊆ (chartAt H γ).source)
    (hK_α : K ⊆ (chartAt H α).source)
    (kmax : ℕ) :
    ∃ (Ω_γα Ω_αγ : Set EuclN) (_hΩ_γα : IsOpen Ω_γα) (_hΩ_αγ : IsOpen Ω_αγ)
      (_hΩ_γα_subset_target : Ω_γα ⊆ chartTargetEuclid (I := I) (M := M) γ)
      (_hΩ_αγ_subset_target : Ω_αγ ⊆ chartTargetEuclid (I := I) (M := M) α)
      (_hΩ_γα_subset_overlap : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α)
      (_hΩ_αγ_subset_overlap : Ω_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ),
      ((toEuclidean : E ≃L[ℝ] _) ∘ extChartAt I γ) '' K ⊆ Ω_γα ∧
      ∃ (Φ : DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder
          (Module.finrank ℝ E) Ω_γα Ω_αγ kmax),
        (∀ y ∈ Ω_γα,
          Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y) ∧
        (∀ y ∈ Ω_αγ,
          Φ.invFun y = chartTransitionEuclid (I := I) (M := M) α γ y) := by
  classical
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    kEuclid_compact (I := I) (M := M) γ hK_compact hK_γ
  have hKEγ_subset_overlap_γα : K_E_γ ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
    kEuclid_subset_overlap (I := I) (M := M) γ α hK_γ hK_α
  have hOverlap_γα_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have hKEα_compact : IsCompact K_E_α :=
    kEuclid_compact (I := I) (M := M) α hK_compact hK_α
  have hKEα_subset_overlap_αγ : K_E_α ⊆ chartOverlapEuclid (I := I) (M := M) α γ :=
    kEuclid_subset_overlap (I := I) (M := M) α γ hK_α hK_γ
  have hOverlap_αγ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) α γ) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) α γ
  obtain ⟨δ_γ, η_γ, hδ_γ_pos, hδγ_subset, hη_γ_smooth, hη_γ_cpt, _hη_γ_range,
      hη_γ_one, hη_γ_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      hKEγ_compact hOverlap_γα_open hKEγ_subset_overlap_γα
  have hδ_γ_half_pos : 0 < δ_γ / 2 := by linarith
  set Ω_γα : Set EuclN := Metric.thickening (δ_γ / 2) K_E_γ with hΩγα_def
  have hΩγα_open : IsOpen Ω_γα := Metric.isOpen_thickening
  have hKEγ_subset_Ωγα : K_E_γ ⊆ Ω_γα := Metric.self_subset_thickening hδ_γ_half_pos K_E_γ
  have hΩγα_closure_subset_cthick_half :
      closure Ω_γα ⊆ Metric.cthickening (δ_γ / 2) K_E_γ :=
    Metric.closure_thickening_subset_cthickening (δ_γ / 2) K_E_γ
  have hcthick_half_subset_full :
      Metric.cthickening (δ_γ / 2) K_E_γ ⊆ Metric.cthickening δ_γ K_E_γ :=
    Metric.cthickening_mono (by linarith : δ_γ / 2 ≤ δ_γ) K_E_γ
  have hΩγα_closure_subset_cthick :
      closure Ω_γα ⊆ Metric.cthickening δ_γ K_E_γ :=
    hΩγα_closure_subset_cthick_half.trans hcthick_half_subset_full
  have hΩγα_closure_subset_overlap : closure Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
    hΩγα_closure_subset_cthick.trans hδγ_subset
  have hcthick_compact : IsCompact (Metric.cthickening (δ_γ / 2) K_E_γ) :=
    hKEγ_compact.cthickening
  have hΩγα_closure_compact : IsCompact (closure Ω_γα) :=
    hcthick_compact.of_isClosed_subset isClosed_closure hΩγα_closure_subset_cthick_half
  have hΩγα_subset_cthick : Ω_γα ⊆ Metric.cthickening δ_γ K_E_γ := by
    refine subset_trans (Metric.thickening_subset_cthickening (δ_γ / 2) K_E_γ) ?_
    exact hcthick_half_subset_full
  have hΩγα_subset_target : Ω_γα ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
      have : y ∈ closure Ω_γα := subset_closure hy
      exact hΩγα_closure_subset_overlap this
    exact chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ α hy_overlap
  set c_γ : EuclN := chartCenterEuclid (I := I) (M := M) α with hcγ_def
  set T_γα : EuclN → EuclN :=
    chartTransitionExtended (I := I) (M := M) γ α η_γ c_γ with hTγα_def
  have hT_γα_smooth : ContDiff ℝ (⊤ : ℕ∞) T_γα :=
    chartTransitionExtended_contDiff (I := I) (M := M) γ α
      hη_γ_smooth hη_γ_supp c_γ
  have hT_γα_eq_on_Ωγα : ∀ y ∈ Ω_γα,
      T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y := by
    intro y hy
    have hy_cthick : y ∈ Metric.cthickening δ_γ K_E_γ := hΩγα_subset_cthick hy
    have hηy : η_γ y = 1 := hη_γ_one y hy_cthick
    exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
      (I := I) (M := M) γ α c_γ hηy
  set Ω_αγ : Set EuclN :=
    (chartTransitionEuclid (I := I) (M := M) γ α) '' Ω_γα with hΩαγ_def
  have hΩαγ_subset_overlap_αγ : Ω_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ := by
    intro z hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
      have : y ∈ closure Ω_γα := subset_closure hy_Ωγα
      exact hΩγα_closure_subset_overlap this
    rw [← hyz]
    exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy_overlap
  have hΩαγ_subset_target : Ω_αγ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    refine hΩαγ_subset_overlap_αγ.trans ?_
    exact chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α γ
  have hΩαγ_eq_preimage :
      Ω_αγ = (chartTransitionEuclid (I := I) (M := M) α γ ⁻¹' Ω_γα) ∩
              chartOverlapEuclid (I := I) (M := M) α γ := by
    ext z
    refine ⟨?_, ?_⟩
    · intro hz
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
        have hy_cl : y ∈ closure Ω_γα := subset_closure hy_Ωγα
        exact hΩγα_closure_subset_overlap hy_cl
      have hz_overlap : z ∈ chartOverlapEuclid (I := I) (M := M) α γ := by
        rw [← hyz]
        exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy_overlap
      refine ⟨?_, hz_overlap⟩
      have h_inv : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
        rw [← hyz]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
      simp only [Set.mem_preimage, h_inv]
      exact hy_Ωγα
    · rintro ⟨hz_pre, hz_overlap⟩
      simp only [Set.mem_preimage] at hz_pre
      have h_T_αγ_z_overlap : chartTransitionEuclid (I := I) (M := M) α γ z ∈
          chartOverlapEuclid (I := I) (M := M) γ α := by
        have : chartTransitionEuclid (I := I) (M := M) α γ z ∈ closure Ω_γα :=
          subset_closure hz_pre
        exact hΩγα_closure_subset_overlap this
      have h_left_inv :
          chartTransitionEuclid (I := I) (M := M) γ α
            (chartTransitionEuclid (I := I) (M := M) α γ z) = z :=
        chartTransitionEuclid_left_inv (I := I) (M := M) α γ hz_overlap
      refine ⟨chartTransitionEuclid (I := I) (M := M) α γ z, hz_pre, h_left_inv⟩
  have hT_αγ_continuousOn :
      ContinuousOn (chartTransitionEuclid (I := I) (M := M) α γ)
        (chartOverlapEuclid (I := I) (M := M) α γ) :=
    (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) α γ).continuousOn
  have hΩαγ_open : IsOpen Ω_αγ := by
    rw [hΩαγ_eq_preimage]
    rw [Set.inter_comm]
    exact hT_αγ_continuousOn.isOpen_inter_preimage hOverlap_αγ_open hΩγα_open
  set L_αγ : Set EuclN :=
    (chartTransitionEuclid (I := I) (M := M) γ α) '' (closure Ω_γα) with hLαγ_def
  have hL_αγ_compact : IsCompact L_αγ :=
    hΩγα_closure_compact.image_of_continuousOn
      ((chartTransitionEuclid_contDiffOn_overlap
          (I := I) (M := M) γ α).continuousOn.mono hΩγα_closure_subset_overlap)
  have hL_αγ_subset_overlap_αγ : L_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ := by
    intro z hz
    rcases hz with ⟨y, hy_cl, hyz⟩
    rw [← hyz]
    exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α
      (hΩγα_closure_subset_overlap hy_cl)
  have hΩαγ_subset_Lαγ : Ω_αγ ⊆ L_αγ := by
    intro z hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    refine ⟨y, subset_closure hy_Ωγα, hyz⟩
  obtain ⟨δ_α, η_α, hδ_α_pos, hδα_subset, hη_α_smooth, hη_α_cpt, _hη_α_range,
      hη_α_one, hη_α_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      hL_αγ_compact hOverlap_αγ_open hL_αγ_subset_overlap_αγ
  have hL_αγ_subset_cthick_α : L_αγ ⊆ Metric.cthickening δ_α L_αγ :=
    Metric.self_subset_cthickening L_αγ
  have hΩαγ_subset_cthick_α : Ω_αγ ⊆ Metric.cthickening δ_α L_αγ :=
    hΩαγ_subset_Lαγ.trans hL_αγ_subset_cthick_α
  set c_α : EuclN := chartCenterEuclid (I := I) (M := M) γ with hcα_def
  set T_αγ : EuclN → EuclN :=
    chartTransitionExtended (I := I) (M := M) α γ η_α c_α with hTαγ_def
  have hT_αγ_smooth : ContDiff ℝ (⊤ : ℕ∞) T_αγ :=
    chartTransitionExtended_contDiff (I := I) (M := M) α γ
      hη_α_smooth hη_α_supp c_α
  have hT_αγ_eq_on_Ωαγ : ∀ z ∈ Ω_αγ,
      T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z := by
    intro z hz
    have hz_cthick : z ∈ Metric.cthickening δ_α L_αγ := hΩαγ_subset_cthick_α hz
    have hηz : η_α z = 1 := hη_α_one z hz_cthick
    exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
      (I := I) (M := M) α γ c_α hηz
  have hBijOn_T_γα : Set.BijOn T_γα Ω_γα Ω_αγ := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [hT_γα_eq_on_Ωγα y hy]
      exact ⟨y, hy, rfl⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [hT_γα_eq_on_Ωγα y₁ hy₁, hT_γα_eq_on_Ωγα y₂ hy₂] at heq
      have hy₁_overlap : y₁ ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy₁)
      have hy₂_overlap : y₂ ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy₂)
      exact chartTransitionEuclid_injOn_overlap (I := I) (M := M) γ α
        hy₁_overlap hy₂_overlap heq
    · intro z hz
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      refine ⟨y, hy_Ωγα, ?_⟩
      rw [hT_γα_eq_on_Ωγα y hy_Ωγα]; exact hyz
  have hBijOn_T_αγ : Set.BijOn T_αγ Ω_αγ Ω_γα := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [hT_αγ_eq_on_Ωαγ z hz]
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
      have h_inv : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
        rw [← hyz]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
      rw [h_inv]; exact hy_Ωγα
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [hT_αγ_eq_on_Ωαγ z₁ hz₁, hT_αγ_eq_on_Ωαγ z₂ hz₂] at heq
      have hz₁_overlap : z₁ ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
        hΩαγ_subset_overlap_αγ hz₁
      have hz₂_overlap : z₂ ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
        hΩαγ_subset_overlap_αγ hz₂
      exact chartTransitionEuclid_injOn_overlap (I := I) (M := M) α γ
        hz₁_overlap hz₂_overlap heq
    · intro y hy_Ωγα
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
      refine ⟨chartTransitionEuclid (I := I) (M := M) γ α y, ?_, ?_⟩
      · exact ⟨y, hy_Ωγα, rfl⟩
      · have h_z_in_Ωαγ : chartTransitionEuclid (I := I) (M := M) γ α y ∈ Ω_αγ :=
          ⟨y, hy_Ωγα, rfl⟩
        rw [hT_αγ_eq_on_Ωαγ _ h_z_in_Ωαγ]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
  have hLeft_inv : Set.LeftInvOn T_αγ T_γα Ω_γα := by
    intro y hy
    rw [hT_γα_eq_on_Ωγα y hy]
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
      hΩγα_closure_subset_overlap (subset_closure hy)
    have h_T_γα_y_in_Ωαγ : chartTransitionEuclid (I := I) (M := M) γ α y ∈ Ω_αγ :=
      ⟨y, hy, rfl⟩
    rw [hT_αγ_eq_on_Ωαγ _ h_T_γα_y_in_Ωαγ]
    exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
  have hRight_inv : Set.RightInvOn T_αγ T_γα Ω_αγ := by
    intro z hz
    have hz_orig : z ∈ Ω_αγ := hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
      hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
    rw [hT_αγ_eq_on_Ωαγ _ hz_orig]
    have h_T_αγ_z_eq_y : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
      rw [← hyz]
      exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
    rw [h_T_αγ_z_eq_y]
    rw [hT_γα_eq_on_Ωγα y hy_Ωγα]
    exact hyz
  obtain ⟨B_γ, hBγ_pos, hBγ_bound⟩ :=
    chartTransitionExtended_iter_deriv_bound (I := I) (M := M) γ α
      hη_γ_smooth hη_γ_cpt hη_γ_supp c_γ kmax
  obtain ⟨B_α, hBα_pos, hBα_bound⟩ :=
    chartTransitionExtended_iter_deriv_bound (I := I) (M := M) α γ
      hη_α_smooth hη_α_cpt hη_α_supp c_α kmax
  set B : ℝ := max B_γ B_α with hB_def
  have hB_pos : 0 < B := lt_of_lt_of_le hBγ_pos (le_max_left _ _)
  have hB_γ_bound : ∀ i, i ≤ kmax → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ i T_γα x‖ ≤ B := fun i hi x =>
    (hBγ_bound i hi x).trans (le_max_left _ _)
  have hB_α_bound : ∀ i, i ≤ kmax → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ i T_αγ x‖ ≤ B := fun i hi x =>
    (hBα_bound i hi x).trans (le_max_right _ _)
  by_cases hΩγα_empty : Ω_γα = ∅
  · have hKEγ_empty : K_E_γ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have : y ∈ Ω_γα := hKEγ_subset_Ωγα hy
      rw [hΩγα_empty] at this
      exact Set.notMem_empty y this
    have hΩαγ_empty : Ω_αγ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rcases hz with ⟨y, hy, _⟩
      rw [hΩγα_empty] at hy
      exact Set.notMem_empty y hy
    have hΩγα_subset_overlap : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α := by
      intro y hy
      have : y ∈ closure Ω_γα := subset_closure hy
      exact hΩγα_closure_subset_overlap this
    refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
      hΩγα_subset_overlap, hΩαγ_subset_overlap_αγ, ?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hxK, hxy⟩
      simp only [Function.comp_apply] at hxy
      have hxK_E_γ : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hxK, rfl⟩
      have : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
        hKEγ_subset_Ωγα hxK_E_γ
      rw [hxy] at this
      exact this
    refine ⟨{
      toFun := T_γα,
      invFun := T_αγ,
      toFun_smooth := hT_γα_smooth,
      invFun_smooth := hT_αγ_smooth,
      bijOn := hBijOn_T_γα,
      invFun_bijOn := hBijOn_T_αγ,
      left_inv := hLeft_inv,
      right_inv := hRight_inv,
      deriv_bound := B,
      deriv_bound_pos := hB_pos,
      iter_deriv_bounded_at := hB_γ_bound,
      iter_deriv_invFun_bounded_at := hB_α_bound,
      jacobian_lower_bound := 1,
      jacobian_lower_bound_pos := one_pos,
      jacobian_lower := ?_
    }, ?_, ?_⟩
    · intro x hx
      rw [hΩγα_empty] at hx
      exact (Set.notMem_empty x hx).elim
    · intro y hy
      change T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y
      exact hT_γα_eq_on_Ωγα y hy
    · intro z hz
      change T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z
      exact hT_αγ_eq_on_Ωαγ z hz
  · have hΩγα_nonempty : Ω_γα.Nonempty := Set.nonempty_iff_ne_empty.mpr hΩγα_empty
    have hclosure_nonempty : (closure Ω_γα).Nonempty := hΩγα_nonempty.mono subset_closure
    have h_abs_det_pos_on_overlap : ∀ y ∈ chartOverlapEuclid (I := I) (M := M) γ α,
        0 < |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
      intro y hy
      have hT_γα_chart : DifferentiableAt ℝ
          (chartTransitionEuclid (I := I) (M := M) γ α) y := by
        have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
          hOverlap_γα_open
        have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
            (chartTransitionEuclid (I := I) (M := M) γ α)
            (chartOverlapEuclid (I := I) (M := M) γ α) :=
          chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
        have h_diffOn : DifferentiableOn ℝ
            (chartTransitionEuclid (I := I) (M := M) γ α)
            (chartOverlapEuclid (I := I) (M := M) γ α) :=
          h_smooth.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
        exact (h_diffOn y hy).differentiableAt (h_open.mem_nhds hy)
      have hT_αγ_at : DifferentiableAt ℝ
          (chartTransitionEuclid (I := I) (M := M) α γ)
          (chartTransitionEuclid (I := I) (M := M) γ α y) := by
        have hy_α : chartTransitionEuclid (I := I) (M := M) γ α y ∈
            chartOverlapEuclid (I := I) (M := M) α γ :=
          chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy
        have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) α γ) :=
          hOverlap_αγ_open
        have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
            (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartOverlapEuclid (I := I) (M := M) α γ) :=
          chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) α γ
        have h_diffOn : DifferentiableOn ℝ
            (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartOverlapEuclid (I := I) (M := M) α γ) :=
          h_smooth.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
        exact (h_diffOn _ hy_α).differentiableAt (h_open.mem_nhds hy_α)
      have h_evt : (fun z => chartTransitionEuclid (I := I) (M := M) α γ
            (chartTransitionEuclid (I := I) (M := M) γ α z))
          =ᶠ[𝓝 y] (fun z : EuclN => z) := by
        refine Filter.eventually_of_mem (hOverlap_γα_open.mem_nhds hy) ?_
        intro z hz
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hz
      have h_fderiv_id :
          fderiv ℝ (fun z => chartTransitionEuclid (I := I) (M := M) α γ
              (chartTransitionEuclid (I := I) (M := M) γ α z)) y =
            ContinuousLinearMap.id ℝ EuclN := by
        rw [h_evt.fderiv_eq]; exact fderiv_id'
      have h_fderiv_comp :
          fderiv ℝ (fun z => chartTransitionEuclid (I := I) (M := M) α γ
              (chartTransitionEuclid (I := I) (M := M) γ α z)) y =
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
              (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :=
        fderiv_comp y hT_αγ_at hT_γα_chart
      have h_comp_eq :
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) =
          ContinuousLinearMap.id ℝ EuclN := by
        rw [← h_fderiv_comp]; exact h_fderiv_id
      have h_det_eq :
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)).det *
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det = 1 := by
        have h_lin :
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
              (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                EuclN →ₗ[ℝ] EuclN) =
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                (chartTransitionEuclid (I := I) (M := M) γ α y) :
                  EuclN →ₗ[ℝ] EuclN)).comp
              ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                  EuclN →ₗ[ℝ] EuclN) := rfl
        have h_det_id :
            ((ContinuousLinearMap.id ℝ EuclN) : EuclN →ₗ[ℝ] EuclN).det = 1 := by
          change LinearMap.det (LinearMap.id : EuclN →ₗ[ℝ] EuclN) = 1
          exact LinearMap.det_id
        have h_det_comp_lin :
            LinearMap.det
              (((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                  (chartTransitionEuclid (I := I) (M := M) γ α y)) :
                    EuclN →ₗ[ℝ] EuclN).comp
                ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                    EuclN →ₗ[ℝ] EuclN)) =
              LinearMap.det
                ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                  (chartTransitionEuclid (I := I) (M := M) γ α y)) :
                    EuclN →ₗ[ℝ] EuclN) *
              LinearMap.det
                ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                    EuclN →ₗ[ℝ] EuclN) := LinearMap.det_comp _ _
        have hcomp_det :
            LinearMap.det
              (((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                  (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
                (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y)) :
                  EuclN →ₗ[ℝ] EuclN) =
              LinearMap.det ((ContinuousLinearMap.id ℝ EuclN) : EuclN →ₗ[ℝ] EuclN) := by
          rw [h_comp_eq]
        rw [h_lin, h_det_comp_lin, h_det_id] at hcomp_det
        change (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartTransitionEuclid (I := I) (M := M) γ α y)).det *
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det = 1
        exact hcomp_det
      have h_ne_zero : (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det ≠ 0 := by
        intro h_zero
        rw [h_zero, mul_zero] at h_det_eq
        exact zero_ne_one h_det_eq
      exact abs_pos.mpr h_ne_zero
    have h_abs_det_continuousOn :
        ContinuousOn
          (fun y => |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det|)
          (closure Ω_γα) := by
      have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
          (chartTransitionEuclid (I := I) (M := M) γ α)
          (chartOverlapEuclid (I := I) (M := M) γ α) :=
        chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
      have h_cont_fderiv : ContinuousOn
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α))
          (chartOverlapEuclid (I := I) (M := M) γ α) :=
        h_smooth.continuousOn_fderiv_of_isOpen hOverlap_γα_open
          (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      have h_cont_det : Continuous (fun A : EuclN →L[ℝ] EuclN => A.det) :=
        ContinuousLinearMap.continuous_det
      have h_cont_abs : Continuous (fun r : ℝ => |r|) := continuous_abs
      exact ((h_cont_abs.comp h_cont_det).continuousOn.comp h_cont_fderiv
        (Set.mapsTo_univ _ _)).mono hΩγα_closure_subset_overlap
    have h_abs_det_pos_on_closure : ∀ y ∈ closure Ω_γα,
        0 < |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
      intro y hy
      exact h_abs_det_pos_on_overlap y (hΩγα_closure_subset_overlap hy)
    obtain ⟨y₀, hy₀_cl, hy₀_min⟩ :=
      hΩγα_closure_compact.exists_isMinOn hclosure_nonempty h_abs_det_continuousOn
    set J : ℝ := |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y₀).det| with hJ_def
    have hJ_pos : 0 < J := h_abs_det_pos_on_closure y₀ hy₀_cl
    have hη_γ_eq_one_on_thick : ∀ y ∈ Metric.thickening δ_γ K_E_γ, η_γ y = 1 := by
      intro y hy
      have hy_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
        Metric.thickening_subset_cthickening δ_γ K_E_γ hy
      exact hη_γ_one y hy_cthick
    have hΩγα_subset_thick_γ : Ω_γα ⊆ Metric.thickening δ_γ K_E_γ := by
      refine subset_trans ?_ (Metric.thickening_mono (by linarith : δ_γ / 2 ≤ δ_γ) K_E_γ)
      rfl
    have hT_γα_fderiv_eq : ∀ y ∈ Ω_γα,
        fderiv ℝ T_γα y = fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y := by
      intro y hy
      have h_evt : T_γα =ᶠ[𝓝 y] (chartTransitionEuclid (I := I) (M := M) γ α) := by
        have h_open_thick : IsOpen (Metric.thickening δ_γ K_E_γ) := Metric.isOpen_thickening
        have hy_thick : y ∈ Metric.thickening δ_γ K_E_γ := hΩγα_subset_thick_γ hy
        refine Filter.eventually_of_mem (h_open_thick.mem_nhds hy_thick) ?_
        intro y' hy'
        have hηy' : η_γ y' = 1 := hη_γ_eq_one_on_thick y' hy'
        exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
          (I := I) (M := M) γ α c_γ hηy'
      exact h_evt.fderiv_eq
    have hJ_lower : ∀ y ∈ Ω_γα, J ≤ |(fderiv ℝ T_γα y).det| := by
      intro y hy
      rw [hT_γα_fderiv_eq y hy]
      exact hy₀_min (subset_closure hy)
    have hΩγα_subset_overlap : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α := by
      intro y hy
      have : y ∈ closure Ω_γα := subset_closure hy
      exact hΩγα_closure_subset_overlap this
    refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
      hΩγα_subset_overlap, hΩαγ_subset_overlap_αγ, ?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hxK, hxy⟩
      simp only [Function.comp_apply] at hxy
      have hxK_E_γ : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hxK, rfl⟩
      have : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
        hKEγ_subset_Ωγα hxK_E_γ
      rw [hxy] at this
      exact this
    refine ⟨{
      toFun := T_γα,
      invFun := T_αγ,
      toFun_smooth := hT_γα_smooth,
      invFun_smooth := hT_αγ_smooth,
      bijOn := hBijOn_T_γα,
      invFun_bijOn := hBijOn_T_αγ,
      left_inv := hLeft_inv,
      right_inv := hRight_inv,
      deriv_bound := B,
      deriv_bound_pos := hB_pos,
      iter_deriv_bounded_at := hB_γ_bound,
      iter_deriv_invFun_bounded_at := hB_α_bound,
      jacobian_lower_bound := J,
      jacobian_lower_bound_pos := hJ_pos,
      jacobian_lower := hJ_lower
    }, ?_, ?_⟩
    · intro y hy
      change T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y
      exact hT_γα_eq_on_Ωγα y hy
    · intro z hz
      change T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z
      exact hT_αγ_eq_on_Ωαγ z hz

lemma chartPushed_chartPullback_zero_of_K_M_empty
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (γ α : M) {K_α : Set M}
    (hK_α_in_α : K_α ⊆ (chartAt H α).source)
    (hKM_empty : K_α ∩ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) = ∅)
    {χ : EuclN → ℝ}
    (hχ_supp : tsupport χ ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
        (chartPullback I α χ) =
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  funext y
  unfold chartPushed
  set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
  by_cases hρ_zero : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) z = 0
  · rw [hρ_zero]; ring
  · have hz_in_supp_γ : z ∈ tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_in : z ∈ Function.support
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        simp only [Function.mem_support, ne_eq]; exact hρ_zero
      exact subset_tsupport _ h_in
    by_cases hpb_zero : chartPullback I α χ z = 0
    · rw [hpb_zero]; ring
    · exfalso
      have hz_chartα : z ∈ (chartAt H α).source := by
        by_contra hcontra
        apply hpb_zero
        exact chartPullback_apply_of_notMem (I := I) (M := M) α χ hcontra
      rw [chartPullback_apply_of_mem (I := I) (M := M) α χ hz_chartα] at hpb_zero
      have h_arg_in_tsupp_χ : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport χ := by
        have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support χ := by
          simp only [Function.mem_support, ne_eq]; exact hpb_zero
        exact subset_tsupport _ this
      have h_arg_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
        hχ_supp h_arg_in_tsupp_χ
      obtain ⟨x', hx'_in_K_α, hx'_eq⟩ := h_arg_in_image_K_α
      have hx'_chartα : x' ∈ (chartAt H α).source := hK_α_in_α hx'_in_K_α
      have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
        have : (toEuclidean (E := E)) (extChartAt I α x') =
            (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
        exact (toEuclidean (E := E)).injective this
      have hz_eq_x' : z = x' := by
        have hz_extChart_source : z ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hz_chartα
        have hx'_extChart_source : x' ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hx'_chartα
        have h_inj := (extChartAt I α).injOn hx'_extChart_source hz_extChart_source
          h_eq_chart_α
        exact h_inj.symm
      have hz_in_K_α : z ∈ K_α := by rw [hz_eq_x']; exact hx'_in_K_α
      have hz_in_K_M : z ∈ K_α ∩ tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := ⟨hz_in_K_α, hz_in_supp_γ⟩
      rw [hKM_empty] at hz_in_K_M
      exact Set.notMem_empty z hz_in_K_M

theorem cross_chart_bound_strict_strong
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {χ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ},
        ContDiff ℝ (⊤ : ℕ∞) χ →
        HasCompactSupport χ →
        tsupport χ ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
            (chartPullback I α χ))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
        ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p χ
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  let _ := g
  set K_M : Set M := K_α ∩ tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKM_def
  have hKM_compact : IsCompact K_M := crossChartK_isCompact (I := I) (M := M) γ hK_compact
  have hKM_in_α : K_M ⊆ (chartAt H α).source :=
    crossChartK_subset_chartα_source (I := I) (M := M) γ α hK_α_in_α
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source :=
    crossChartK_subset_chartγ_source (I := I) (M := M) γ
  by_cases hKM_empty : K_M = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro χ _hχ_smooth _hχ_cpt hχ_supp
    have h_pushed_zero := chartPushed_chartPullback_zero_of_K_M_empty
      (I := I) (M := M) γ α hK_α_in_α hKM_empty hχ_supp
    rw [h_pushed_zero]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) γ)]
    exact zero_le _
  obtain ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
    hΩγα_subset_overlap, _hΩαγ_subset_overlap, hKM_image_in_Ωγα, Φ,
    hΦ_eq_on_Ωγα, _hΦ_inv_eq_on_Ωαγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      γ α hKM_compact hKM_in_γ hKM_in_α 1
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M
    with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M
    with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEα_compact : IsCompact K_E_α :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKM_compact hKM_in_α
  have hKEγ_subset_target : K_E_γ ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  have hKEα_subset_target : K_E_α ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H α).source := hKM_in_α hxK
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I α x, h_target, rfl⟩
  have hΦ_eq_KM : ∀ x ∈ K_M, Φ.toFun ((toEuclidean (E := E)) (extChartAt I γ x)) =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    intro x hxK
    set y := (toEuclidean (E := E)) (extChartAt I γ x) with hy_def
    have hy_in_KEγ : y ∈ K_E_γ := ⟨x, hxK, rfl⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy_in_KEγ
    have h1 : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
      hΦ_eq_on_Ωγα y hy_in_Ωγα
    rw [h1]
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    rw [hy_def]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_chart
  have hKEα_eq_Φ_image : K_E_α = Φ.toFun '' K_E_γ := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hxK, hxz⟩
      refine ⟨(toEuclidean (E := E)) (extChartAt I γ x), ?_, ?_⟩
      · exact ⟨x, hxK, rfl⟩
      · have := hΦ_eq_KM x hxK
        rw [this]; exact hxz
    · rintro ⟨y, hy, hyz⟩
      rcases hy with ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      have := hΦ_eq_KM x hxK
      rw [← hyz, ← hxy, this]
  have hKEα_in_Ωαγ : K_E_α ⊆ Ω_αγ := by
    rw [hKEα_eq_Φ_image]
    intro z hz
    rcases hz with ⟨y, hy, hyz⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy
    rw [← hyz]; exact Φ.bijOn.mapsTo hy_in_Ωγα
  set Uγ : Set EuclN := Ω_γα ∩ chartTargetEuclid (I := I) (M := M) γ with hUγ_def
  have hUγ_open : IsOpen Uγ :=
    hΩγα_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) γ)
  have hKEγ_in_Uγ : K_E_γ ⊆ Uγ :=
    Set.subset_inter hKM_image_in_Ωγα hKEγ_subset_target
  obtain ⟨δ_γ, η_γ_loc, hδ_γ_pos, _hδγ_subset, hη_γ_loc_smooth, hη_γ_loc_cpt,
    hη_γ_loc_range, hη_γ_loc_one, hη_γ_loc_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEγ_compact hUγ_open hKEγ_in_Uγ
  have hη_γ_loc_supp_Ωγα : tsupport η_γ_loc ⊆ Ω_γα :=
    fun y hy => (hη_γ_loc_supp hy).1
  have hη_γ_loc_supp_target : tsupport η_γ_loc ⊆ chartTargetEuclid (I := I) (M := M) γ :=
    fun y hy => (hη_γ_loc_supp hy).2
  set Uα : Set EuclN := Ω_αγ ∩ chartTargetEuclid (I := I) (M := M) α with hUα_def
  have hUα_open : IsOpen Uα :=
    hΩαγ_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) α)
  have hKEα_in_Uα : K_E_α ⊆ Uα :=
    Set.subset_inter hKEα_in_Ωαγ hKEα_subset_target
  obtain ⟨δ_α, η_α_loc, hδ_α_pos, _hδα_subset, hη_α_loc_smooth, hη_α_loc_cpt,
    hη_α_loc_range, hη_α_loc_one, hη_α_loc_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEα_compact hUα_open hKEα_in_Uα
  have hη_α_loc_supp_Ωαγ : tsupport η_α_loc ⊆ Ω_αγ :=
    fun y hy => (hη_α_loc_supp hy).1
  have hη_α_loc_supp_target : tsupport η_α_loc ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hη_α_loc_supp hy).2
  set ρ_γ_M : M → ℝ :=
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_γ_M_def
  have hρ_γ_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ρ_γ_M :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hρ_γ_M_supp_in_chart : tsupport ρ_γ_M ⊆ (chartAt H γ).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ
  have hρ_γ_M_cpt : HasCompactSupport ρ_γ_M :=
    (isClosed_tsupport _).isCompact
  have hρ_γ_M_range : Set.range ρ_γ_M ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro v ⟨x, hx⟩
    rw [← hx]
    refine ⟨?_, ?_⟩
    · exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg γ x
    · exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one γ x
  set ργE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) γ ρ_γ_M with hργE_def
  have hργE_smooth : ContDiff ℝ (⊤ : ℕ∞) ργE :=
    contDiff_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth hρ_γ_M_cpt
      hρ_γ_M_supp_in_chart
  have hργE_cpt : HasCompactSupport ργE :=
    hasCompactSupport_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_cpt
      hρ_γ_M_supp_in_chart
  have hργE_range : Set.range ργE ⊆ Set.Icc (0 : ℝ) 1 :=
    etaEuclid_range_Icc (I := I) (M := M) γ ρ_γ_M hρ_γ_M_range
  have hργE_norm_one : ∀ y : EuclN, ‖ργE y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hργE_range
  obtain ⟨C_ργE_grad, _hC_ργE_pos, hC_ργE_grad⟩ :=
    exists_grad_bound_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth
      hρ_γ_M_cpt hρ_γ_M_supp_in_chart
  have hη_γ_loc_norm_one : ∀ y : EuclN, ‖η_γ_loc y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_γ_loc_range
  obtain ⟨C_η_γ_grad, _hC_η_γ_pos, hC_η_γ_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_γ_loc_smooth hη_γ_loc_cpt
  have hη_α_loc_norm_one : ∀ y : EuclN, ‖η_α_loc y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_α_loc_range
  obtain ⟨C_η_α_grad, _hC_η_α_pos, hC_η_α_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_α_loc_smooth hη_α_loc_cpt
  set η_combined : EuclN → ℝ := fun y => η_γ_loc y * ργE y with hη_combined_def
  have hη_combined_smooth : ContDiff ℝ (⊤ : ℕ∞) η_combined :=
    hη_γ_loc_smooth.mul hργE_smooth
  have hη_combined_bound : ∀ y : EuclN, ‖η_combined y‖ ≤ 1 := by
    intro y
    have h := mul_le_mul (a := ‖η_γ_loc y‖) (b := 1) (c := ‖ργE y‖) (d := 1)
      (hη_γ_loc_norm_one y) (hργE_norm_one y) (norm_nonneg _) zero_le_one
    rw [show η_combined y = η_γ_loc y * ργE y from rfl, norm_mul, mul_one] at *
    exact h
  set C_combined_grad : ℝ := C_η_γ_grad + C_ργE_grad with hC_combined_grad_def
  have hC_combined_grad_bound : ∀ y : EuclN, ‖fderiv ℝ η_combined y‖ ≤ C_combined_grad := by
    intro y
    have h_eq :
        η_combined = fun y => η_γ_loc y * ργE y := rfl
    have hη_γ_loc_diff : DifferentiableAt ℝ η_γ_loc y :=
      (hη_γ_loc_smooth.differentiable (by simp)).differentiableAt
    have hργE_diff : DifferentiableAt ℝ ργE y :=
      (hργE_smooth.differentiable (by simp)).differentiableAt
    rw [h_eq]
    rw [fderiv_fun_mul hη_γ_loc_diff hργE_diff]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖η_γ_loc y • fderiv ℝ ργE y‖ ≤ C_ργE_grad := by
      rw [norm_smul]
      have : ‖η_γ_loc y‖ * ‖fderiv ℝ ργE y‖ ≤ 1 * C_ργE_grad :=
        mul_le_mul (hη_γ_loc_norm_one y) (hC_ργE_grad y) (norm_nonneg _) zero_le_one
      simpa using this
    have h2 : ‖ργE y • fderiv ℝ η_γ_loc y‖ ≤ C_η_γ_grad := by
      rw [norm_smul]
      have : ‖ργE y‖ * ‖fderiv ℝ η_γ_loc y‖ ≤ 1 * C_η_γ_grad :=
        mul_le_mul (hργE_norm_one y) (hC_η_γ_grad y) (norm_nonneg _) zero_le_one
      simpa using this
    linarith [h1, h2]
  set Cmax_combined : ℝ := max 1 C_combined_grad with hCmax_combined_def
  have hCmax_combined_norm : ∀ y : EuclN, ‖η_combined y‖ ≤ Cmax_combined :=
    fun y => (hη_combined_bound y).trans (le_max_left _ _)
  have hCmax_combined_grad : ∀ y : EuclN, ‖fderiv ℝ η_combined y‖ ≤ Cmax_combined :=
    fun y => (hC_combined_grad_bound y).trans (le_max_right _ _)
  set Cmax_η_α : ℝ := max 1 C_η_α_grad with hCmax_η_α_def
  have hCmax_η_α_norm : ∀ y : EuclN, ‖η_α_loc y‖ ≤ Cmax_η_α :=
    fun y => (hη_α_loc_norm_one y).trans (le_max_left _ _)
  have hCmax_η_α_grad : ∀ y : EuclN, ‖fderiv ℝ η_α_loc y‖ ≤ Cmax_η_α :=
    fun y => (hC_η_α_grad y).trans (le_max_right _ _)
  set Ωγ_target : Set EuclN := chartTargetEuclid (I := I) (M := M) γ with hΩγ_target_def
  set Ωα_target : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩα_target_def
  have hΩγ_target_open : IsOpen Ωγ_target := chartTargetEuclid_isOpen (I := I) (M := M) γ
  have hΩα_target_open : IsOpen Ωα_target := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hCmax_combined_nonneg : 0 ≤ Cmax_combined :=
    le_trans zero_le_one (le_max_left _ _)
  have hη_combined_iter_bound :
      ∀ j ≤ 1, ∀ y ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined y‖ ≤ Cmax_combined := by
    intro j hj y _
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact hCmax_combined_norm y
    · rw [norm_iteratedFDeriv_one]; exact hCmax_combined_grad y
  obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      1 (le_refl _) (d := Module.finrank ℝ E) hp_one hp_top hΩγα_open hη_combined_smooth
      hCmax_combined_nonneg hη_combined_iter_bound
  have hCmax_η_α_nonneg : 0 ≤ Cmax_η_α :=
    le_trans zero_le_one (le_max_left _ _)
  have hη_α_loc_iter_bound :
      ∀ j ≤ 1, ∀ y ∈ Ωα_target, ‖iteratedFDeriv ℝ j η_α_loc y‖ ≤ Cmax_η_α := by
    intro j hj y _
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact hCmax_η_α_norm y
    · rw [norm_iteratedFDeriv_one]; exact hCmax_η_α_grad y
  obtain ⟨K_leib_α, hK_leib_α_pos, hK_leib_α_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      1 (le_refl _) (d := Module.finrank ℝ E) hp_one hp_top hΩα_target_open hη_α_loc_smooth
      hCmax_η_α_nonneg hη_α_loc_iter_bound
  set K_chain : ℝ := Φ.wkpComp_const' 1 p with hK_chain_def
  have hK_chain_pos : 0 < K_chain := by
    have hp_zero : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one
      exact absurd hp_one (by norm_num)
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
    have hjLB_pos : 0 < Φ.jacobian_lower_bound := Φ.jacobian_lower_bound_pos
    have hjLB_inv_pos : 0 < 1 / Φ.jacobian_lower_bound := by positivity
    have hKchg_pos : 0 < (1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal) :=
      Real.rpow_pos_of_pos hjLB_inv_pos _
    rw [hK_chain_def]
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpComp_const'
    have h_zero_in : (0 : ℕ) ∈ Finset.range (1 + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_card_pos : 0 < (Finset.range (1 + 1)).sum
        (fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ)) := by
      have h_le := Finset.single_le_sum (s := Finset.range (1 + 1))
        (f := fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ))
        (fun j _ => by positivity) h_zero_in
      rw [show ((fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ)) 0 : ℝ) =
          (Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) : ℝ) from rfl] at h_le
      rw [h_at_zero] at h_le
      linarith
    have h_kfact_D_pos : 0 < ((1 : ℕ).factorial : ℝ) * Φ.derivBoundMaxOne ^ 1 := by
      refine mul_pos ?_ ?_
      · exact_mod_cast Nat.factorial_pos 1
      · exact pow_pos Φ.derivBoundMaxOne_pos 1
    have h_k1_pos : (0 : ℝ) < ((1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ 1
    positivity
  set K : ℝ := K_leib * K_chain * K_leib_α with hK_def
  have hK_pos : 0 < K := mul_pos (mul_pos hK_leib_pos hK_chain_pos) hK_leib_α_pos
  refine ⟨K, hK_pos, ?_⟩
  intro χ hχ_smooth hχ_cpt hχ_supp
  set χ_loc : EuclN → ℝ := fun y => η_α_loc y * χ y with hχ_loc_def
  have hχ_loc_smooth : ContDiff ℝ (⊤ : ℕ∞) χ_loc := hη_α_loc_smooth.mul hχ_smooth
  have hχ_loc_supp_in_η_α : tsupport χ_loc ⊆ tsupport η_α_loc := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_α_loc y ≠ 0 := by
      intro h0
      apply hy
      change η_α_loc y * χ y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hχ_loc_supp_in_Ωαγ : tsupport χ_loc ⊆ Ω_αγ :=
    hχ_loc_supp_in_η_α.trans hη_α_loc_supp_Ωαγ
  have hχ_loc_supp_in_target : tsupport χ_loc ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    hχ_loc_supp_in_η_α.trans hη_α_loc_supp_target
  have hχ_loc_cpt : HasCompactSupport χ_loc :=
    hη_α_loc_cpt.of_isClosed_subset (isClosed_tsupport _) hχ_loc_supp_in_η_α
  have hχ_loc_mem_Ωαγ : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p χ_loc Ω_αγ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
        (d := Module.finrank ℝ E) hΩαγ_open hχ_loc_smooth hχ_loc_cpt
        hχ_loc_supp_in_Ωαγ hp_one 1
  set ψ_total : EuclN → ℝ := fun y => η_combined y * χ_loc (Φ.toFun y) with hψ_total_def
  have hψ_total_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_total :=
    hη_combined_smooth.mul (hχ_loc_smooth.comp Φ.toFun_smooth)
  have hψ_total_supp_in_η_combined : tsupport ψ_total ⊆ tsupport η_combined := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_combined y ≠ 0 := by
      intro h0
      apply hy
      change η_combined y * χ_loc (Φ.toFun y) = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hη_combined_supp_in_η_γ : tsupport η_combined ⊆ tsupport η_γ_loc := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_γ_ne : η_γ_loc y ≠ 0 := by
      intro h0
      apply hy
      change η_γ_loc y * ργE y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_γ_ne
  have hψ_total_supp_in_Ωγα : tsupport ψ_total ⊆ Ω_γα :=
    (hψ_total_supp_in_η_combined.trans hη_combined_supp_in_η_γ).trans hη_γ_loc_supp_Ωγα
  have hψ_total_supp_in_target : tsupport ψ_total ⊆
      chartTargetEuclid (I := I) (M := M) γ :=
    (hψ_total_supp_in_η_combined.trans hη_combined_supp_in_η_γ).trans hη_γ_loc_supp_target
  have hη_γ_loc_supp_compact : IsCompact (tsupport η_γ_loc) := hη_γ_loc_cpt
  have hψ_total_cpt : HasCompactSupport ψ_total :=
    hη_γ_loc_supp_compact.of_isClosed_subset (isClosed_tsupport _)
      (hψ_total_supp_in_η_combined.trans hη_combined_supp_in_η_γ)
  have h_pointwise_eq :
      ∀ y ∈ Ωγ_target, chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
          (chartPullback I α χ) y = ψ_total y := by
    intro y hy_target
    set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
      have := hy_target
      rw [hΩγ_target_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at this
      exact this
    have hz_source : z ∈ (extChartAt I γ).source :=
      (extChartAt I γ).map_target hsymm_target
    have hz_chartγ : z ∈ (chartAt H γ).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hz_source
      exact hz_source
    have h_pushed_eq : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
        (chartPullback I α χ) y =
        ρ_γ_M z * chartPullback I α χ z := by
      unfold chartPushed
      rfl
    rw [h_pushed_eq]
    have hργE_y : ργE y = ρ_γ_M z := by
      rw [hργE_def]
      exact etaEuclid_apply_of_mem (I := I) (M := M) γ ρ_γ_M hy_target
    have hψ_total_y : ψ_total y = η_γ_loc y * ργE y * χ_loc (Φ.toFun y) := rfl
    rw [hψ_total_y]
    by_cases h_y_in_supp_η_γ : y ∈ tsupport η_γ_loc
    · have hy_in_Ωγα : y ∈ Ω_γα := hη_γ_loc_supp_Ωγα h_y_in_supp_η_γ
      by_cases hρ_zero : ρ_γ_M z = 0
      · rw [hρ_zero, hργE_y, hρ_zero]; ring
      · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
          have h_in : z ∈ Function.support ρ_γ_M := by
            simp only [Function.mem_support, ne_eq]; exact hρ_zero
          exact subset_tsupport _ h_in
        by_cases hz_in_α : z ∈ (chartAt H α).source
        · rw [chartPullback_apply_of_mem (I := I) (M := M) α χ hz_in_α]
          by_cases hz_in_Kα : z ∈ K_α
          · have hz_in_KM : z ∈ K_M := ⟨hz_in_Kα, hz_in_tsupp_ρ⟩
            have hy_in_KEγ : y ∈ K_E_γ := by
              refine ⟨z, hz_in_KM, ?_⟩
              change (toEuclidean (E := E)) (extChartAt I γ z) = y
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              rw [h_z_chart]
              exact (toEuclidean (E := E)).apply_symm_apply y
            have hη_γ_loc_y : η_γ_loc y = 1 := by
              apply hη_γ_loc_one
              exact Metric.self_subset_cthickening K_E_γ hy_in_KEγ
            have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
              have h := hΦ_eq_KM z hz_in_KM
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
                rw [h_z_chart]
                exact (toEuclidean (E := E)).apply_symm_apply y
              rw [← hy_eq]
              exact h
            rw [hΦ_y]
            have h_Φy_in_KEα : (toEuclidean (E := E)) (extChartAt I α z) ∈ K_E_α :=
              ⟨z, hz_in_KM, rfl⟩
            have hη_α_loc_Φy : η_α_loc ((toEuclidean (E := E)) (extChartAt I α z)) = 1 := by
              apply hη_α_loc_one
              exact Metric.self_subset_cthickening K_E_α h_Φy_in_KEα
            have hχ_loc_Φy : χ_loc ((toEuclidean (E := E)) (extChartAt I α z)) =
                χ ((toEuclidean (E := E)) (extChartAt I α z)) := by
              change η_α_loc _ * χ _ = χ _
              rw [hη_α_loc_Φy]; ring
            rw [hχ_loc_Φy, hη_γ_loc_y, hργE_y]
            ring
          · have hχα_z_eq : (toEuclidean (E := E)) (extChartAt I α z) ∉ tsupport χ := by
              intro hin
              have := hχ_supp hin
              rcases this with ⟨x', hx'_K, hx'_eq⟩
              have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K
              have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
                have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                    (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
                exact (toEuclidean (E := E)).injective h_eu
              have hz_in_α_ext : z ∈ (extChartAt I α).source := by
                rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
                  (I := I) (M := M)]
                exact hz_in_α
              have hx'_α_ext : x' ∈ (extChartAt I α).source := by
                rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
                  (I := I) (M := M)]
                exact hx'_chart
              have h_inj := (extChartAt I α).injOn hx'_α_ext hz_in_α_ext h_eq_chart_α
              have : z ∈ K_α := by rw [← h_inj]; exact hx'_K
              exact hz_in_Kα this
            have hχ_z : χ ((toEuclidean (E := E)) (extChartAt I α z)) = 0 :=
              image_eq_zero_of_notMem_tsupport hχα_z_eq
            have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
              rw [hΦ_eq_on_Ωγα y hy_in_Ωγα]
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
                rw [h_z_chart]
                exact (toEuclidean (E := E)).apply_symm_apply y
              rw [← hy_eq]
              exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hz_chartγ
            have hχ_loc_zero : χ_loc ((toEuclidean (E := E)) (extChartAt I α z)) = 0 := by
              change η_α_loc _ * χ _ = 0
              rw [hχ_z]; ring
            rw [hΦ_y, hχ_loc_zero, hχ_z]; ring
        · rw [chartPullback_apply_of_notMem (I := I) (M := M) α χ hz_in_α]
          exfalso
          have hy_in_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
            hΩγα_subset_overlap hy_in_Ωγα
          unfold chartOverlapEuclid at hy_in_overlap
          rcases hy_in_overlap with ⟨z', ⟨w, hw_inter, hwz'⟩, hz'y⟩
          have hy_eq : (toEuclidean (E := E)) (extChartAt I γ w) = y := by
            rw [← hz'y, ← hwz']
          have h_w_chart_γ : w ∈ (extChartAt I γ).source := by
            rw [extChartAt_source]; exact hw_inter.1
          have h_z_eq_w : z = w := by
            have h_y_eq_chart : (toEuclidean (E := E)).symm y = extChartAt I γ w := by
              rw [← hy_eq, (toEuclidean (E := E)).symm_apply_apply]
            change (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = w
            rw [h_y_eq_chart]
            exact (extChartAt I γ).left_inv h_w_chart_γ
          rw [h_z_eq_w] at hz_in_α
          exact hz_in_α hw_inter.2
    · have h_zero : η_γ_loc y = 0 := image_eq_zero_of_notMem_tsupport h_y_in_supp_η_γ
      rw [h_zero]; simp only [zero_mul]
      by_cases hρ_zero : ρ_γ_M z = 0
      · rw [hρ_zero]; ring
      · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
          have h_in : z ∈ Function.support ρ_γ_M := by
            simp only [Function.mem_support, ne_eq]; exact hρ_zero
          exact subset_tsupport _ h_in
        by_cases hpb_zero : chartPullback I α χ z = 0
        · rw [hpb_zero]; ring
        · exfalso
          have hz_chartα : z ∈ (chartAt H α).source := by
            by_contra hcontra
            apply hpb_zero
            exact chartPullback_apply_of_notMem (I := I) (M := M) α χ hcontra
          rw [chartPullback_apply_of_mem (I := I) (M := M) α χ hz_chartα] at hpb_zero
          have h_arg_in_tsupp_χ : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport χ := by
            have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support χ := by
              simp only [Function.mem_support, ne_eq]; exact hpb_zero
            exact subset_tsupport _ this
          have h_arg_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
              (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
            hχ_supp h_arg_in_tsupp_χ
          obtain ⟨x', hx'_K_α, hx'_eq⟩ := h_arg_in_image_K_α
          have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K_α
          have h_eq_chart : extChartAt I α x' = extChartAt I α z := by
            have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
            exact (toEuclidean (E := E)).injective h_eu
          have hx'_α_ext : x' ∈ (extChartAt I α).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hx'_chart
          have hz_α_ext : z ∈ (extChartAt I α).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hz_chartα
          have h_inj := (extChartAt I α).injOn hx'_α_ext hz_α_ext h_eq_chart
          have hz_in_K_α : z ∈ K_α := by rw [← h_inj]; exact hx'_K_α
          have hz_in_K_M : z ∈ K_M := ⟨hz_in_K_α, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := by
            refine ⟨z, hz_in_K_M, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I γ z) = y
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          have hy_in_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
            Metric.self_subset_cthickening K_E_γ hy_in_KEγ
          have h_η_y_one : η_γ_loc y = 1 := hη_γ_loc_one y hy_in_cthick
          have hy_in_supp : y ∈ Function.support η_γ_loc := by
            simp only [Function.mem_support, ne_eq, h_η_y_one]
            exact one_ne_zero
          exact h_y_in_supp_η_γ (subset_tsupport _ hy_in_supp)
  have h_ae_eq : (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
        (chartPullback I α χ)) =ᵐ[volume.restrict Ωγ_target] ψ_total := by
    refine (ae_restrict_iff' hΩγ_target_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact h_pointwise_eq y hy
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩγ_target_open h_ae_eq]
  have hψ_total_supp_in_Uγ : tsupport ψ_total ⊆ Uγ :=
    (hψ_total_supp_in_η_combined.trans hη_combined_supp_in_η_γ).trans hη_γ_loc_supp
  have hUγ_subset_target : Uγ ⊆ Ωγ_target := fun y hy => hy.2
  have hUγ_subset_Ωγα : Uγ ⊆ Ω_γα := fun y hy => hy.1
  have h_wkp_target_eq_Uγ :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ωγ_target =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Uγ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_of_compactSupport_smooth_subset
        (d := Module.finrank ℝ E) hp_one hΩγ_target_open hUγ_open hUγ_subset_target
        hψ_total_smooth hψ_total_cpt hψ_total_supp_in_Uγ
  have h_wkp_Ωγα_eq_Uγ :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Uγ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_of_compactSupport_smooth_subset
        (d := Module.finrank ℝ E) hp_one hΩγα_open hUγ_open hUγ_subset_Ωγα
        hψ_total_smooth hψ_total_cpt hψ_total_supp_in_Uγ
  have h_wkp_target_eq_Ωγα :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ωγ_target =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα := by
    rw [h_wkp_target_eq_Uγ, h_wkp_Ωγα_eq_Uγ]
  rw [h_wkp_target_eq_Ωγα]
  have h_χ_loc_comp_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p (fun y => χ_loc (Φ.toFun y)) Ω_γα :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := Module.finrank ℝ E) 1 (le_refl 1) hp_one hp_top hΩγα_open hΩαγ_open Φ
      hχ_loc_mem_Ωαγ hχ_loc_cpt hχ_loc_supp_in_Ωαγ
  have h_leib_step : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα ≤
      ENNReal.ofReal K_leib *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => χ_loc (Φ.toFun y)) Ω_γα :=
    hK_leib_bound h_χ_loc_comp_mem
  have h_chain_step :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => χ_loc (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p χ_loc Ω_αγ := by
    have h := DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le
      hp_one hp_top hΩγα_open hΩαγ_open Φ 1 (le_refl 1)
      hχ_loc_mem_Ωαγ hχ_loc_cpt hχ_loc_supp_in_Ωαγ
    exact h
  have hχ_loc_supp_in_Uα : tsupport χ_loc ⊆ Uα := by
    refine hχ_loc_supp_in_η_α.trans ?_
    intro y hy
    exact hη_α_loc_supp hy
  have hUα_subset_target : Uα ⊆ Ωα_target := fun y hy => hy.2
  have hUα_subset_Ωαγ : Uα ⊆ Ω_αγ := fun y hy => hy.1
  have h_wkp_subset_α_step1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_loc Ω_αγ =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_loc Uα :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_of_compactSupport_smooth_subset
        (d := Module.finrank ℝ E) hp_one hΩαγ_open hUα_open hUα_subset_Ωαγ
        hχ_loc_smooth hχ_loc_cpt hχ_loc_supp_in_Uα
  have h_wkp_subset_α_step2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_loc Ωα_target =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_loc Uα :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_of_compactSupport_smooth_subset
        (d := Module.finrank ℝ E) hp_one hΩα_target_open hUα_open hUα_subset_target
        hχ_loc_smooth hχ_loc_cpt hχ_loc_supp_in_Uα
  have h_wkp_subset_α :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_loc Ω_αγ =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_loc Ωα_target := by
    rw [h_wkp_subset_α_step1, h_wkp_subset_α_step2]
  have hχ_supp_in_Ωα_target : tsupport χ ⊆ Ωα_target := by
    refine hχ_supp.trans ?_
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H α).source := hK_α_in_α hxK
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I α x, h_target, rfl⟩
  have hχ_mem_Ωα_target : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p χ Ωα_target :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
        (d := Module.finrank ℝ E) hΩα_target_open hχ_smooth hχ_cpt hχ_supp_in_Ωα_target
        hp_one 1
  have h_leib_α_step : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p χ_loc Ωα_target ≤
      ENNReal.ofReal K_leib_α *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p χ Ωα_target := by
    have h_eq : χ_loc = (fun y => η_α_loc y * χ y) := rfl
    rw [h_eq]
    exact hK_leib_α_bound hχ_mem_Ωα_target
  have h_chain_combined : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p (fun y => χ_loc (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        (ENNReal.ofReal K_leib_α *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p χ Ωα_target) := by
    refine h_chain_step.trans ?_
    rw [h_wkp_subset_α]
    exact mul_le_mul_of_nonneg_left h_leib_α_step (zero_le _)
  have h_combined :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα ≤
      ENNReal.ofReal K_leib * (ENNReal.ofReal K_chain *
        (ENNReal.ofReal K_leib_α *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p χ Ωα_target)) := by
    refine h_leib_step.trans ?_
    exact mul_le_mul_of_nonneg_left h_chain_combined (zero_le _)
  refine h_combined.trans ?_
  have h_K_eq : ENNReal.ofReal K_leib *
      (ENNReal.ofReal K_chain * (ENNReal.ofReal K_leib_α *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p χ Ωα_target)) =
      ENNReal.ofReal K *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p χ Ωα_target := by
    rw [hK_def]
    rw [ENNReal.ofReal_mul (mul_pos hK_leib_pos hK_chain_pos).le]
    rw [ENNReal.ofReal_mul hK_leib_pos.le]
    ring
  exact h_K_eq ▸ le_refl _

end Chart

end Sobolev
end Analysis
end DifferentialGeometry
