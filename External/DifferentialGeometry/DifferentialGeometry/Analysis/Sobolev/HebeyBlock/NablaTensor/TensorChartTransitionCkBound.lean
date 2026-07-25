import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Elliptic.MetricExtension


namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def transitionCoeffOnEuclid
    (r s : ℕ) (α β : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (y : EuclN) : ℝ :=
  transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma transitionCoeffOnEuclid_def
    (r s : ℕ) (α β : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (y : EuclN) :
    transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q y =
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

noncomputable def chartTransitionEuclidOverlap (α β : M) : Set EuclN :=
  {y | y ∈ chartTargetEuclid (I := I) (M := M) α ∧
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H β).source}

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma mem_chartTransitionEuclidOverlap {α β : M} {y : EuclN} :
    y ∈ chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β ↔
      y ∈ chartTargetEuclid (I := I) (M := M) α ∧
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H β).source :=
  Iff.rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma isOpen_chartTransitionEuclidOverlap (α β : M) :
    IsOpen (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) := by
  classical
  set U : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hU_def
  have hU_open : IsOpen U := chartTargetEuclid_isOpen (I := I) (M := M) α
  let f : EuclN → M := fun y => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.continuous
  have h_chart_symm_contOn : ContinuousOn (extChartAt I α).symm
      ((extChartAt I α).target) := by
    have h := continuousOn_extChartAt_symm (I := I) α
    exact h
  have h_maps : Set.MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y) U
      ((extChartAt I α).target) := by
    intro y hy
    exact toEuclidean_symm_mem_target (I := I) hy
  have hf_contOn : ContinuousOn f U :=
    h_chart_symm_contOn.comp h_toE_cont.continuousOn h_maps
  have h_pre_open : IsOpen (U ∩ f ⁻¹' (chartAt H β).source) := by
    have h_β_open : IsOpen ((chartAt H β).source) :=
      (chartAt H β).open_source
    have h_preU : IsOpen (U ∩ f ⁻¹' (chartAt H β).source) := by
      rw [show U ∩ f ⁻¹' (chartAt H β).source =
          f ⁻¹' (chartAt H β).source ∩ U from Set.inter_comm _ _]
      have h_continuousOn_open :=
        hf_contOn.isOpen_inter_preimage hU_open h_β_open
      simpa [Set.inter_comm] using h_continuousOn_open
    exact h_preU
  have h_eq : chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β =
      U ∩ f ⁻¹' (chartAt H β).source := by
    ext y
    constructor
    · rintro ⟨hyU, hyβ⟩
      exact ⟨hyU, hyβ⟩
    · rintro ⟨hyU, hyβ⟩
      exact ⟨hyU, hyβ⟩
  rw [h_eq]
  exact h_pre_open

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma transitionCoeffOnEuclid_contDiffOn
    (r s : ℕ) (α β : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (transitionCoeffOnEuclid (E := E) (I := I) (M := M)
        r s α β P₀ Q)
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) := by
  classical
  have h_chart_symm : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_tc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q)
      ((chartAt H α).source ∩ (chartAt H β).source) :=
    contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q
  have h_maps : Set.MapsTo
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β)
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    intro y hy
    refine ⟨?_, hy.2⟩
    have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy.1
    have h_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (extChartAt I α).source :=
      (extChartAt I α).map_target h_tgt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src
  have h_overlap_subset_target :
      chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β ⊆
        chartTargetEuclid (I := I) (M := M) α := fun y hy => hy.1
  have h_chart_symm_sub : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) :=
    h_chart_symm.mono h_overlap_subset_target
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞
      (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q)
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) :=
    h_tc.comp h_chart_symm_sub h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

set_option maxHeartbeats 800000 in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartTransition_Ck_bound_on_compact
    (r s k : ℕ) (α β : M)
    {K_E : Set EuclN} (hK_compact : IsCompact K_E)
    (hK_sub : K_E ⊆ chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ∈ Finset.range k,
      ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ∀ y ∈ K_E,
        ‖iteratedFDeriv ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q)
            y‖ ≤ C := by
  classical
  set U : Set EuclN := chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β
    with hU_def
  have hU_open : IsOpen U :=
    isOpen_chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β
  have hU_uniqueDiff : UniqueDiffOn ℝ U := hU_open.uniqueDiffOn
  have h_pull_contDiffOn : ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U :=
    fun P₀ Q => transitionCoeffOnEuclid_contDiffOn
      (E := E) (I := I) (M := M) r s α β P₀ Q
  have h_iteratedFDerivWithin_eq : ∀ (j : ℕ) (P₀ Q : TensorCompIdx (E := E) r s)
      (y : EuclN), y ∈ U →
      iteratedFDerivWithin ℝ j
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y =
      iteratedFDeriv ℝ j
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) y :=
    fun j P₀ Q y hy => iteratedFDerivWithin_of_isOpen j hU_open hy
  have h_iter_contOn : ∀ (j : ℕ) (P₀ Q : TensorCompIdx (E := E) r s),
      ContinuousOn (fun y => iteratedFDerivWithin ℝ j
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y) U :=
    fun j P₀ Q =>
      (h_pull_contDiffOn P₀ Q).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast le_top) hU_uniqueDiff
  have h_per_triple : ∀ (j : ℕ) (P₀ Q : TensorCompIdx (E := E) r s),
      ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ y ∈ K_E,
        ‖iteratedFDeriv ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) y‖ ≤ Cj := by
    intro j P₀ Q
    by_cases hKne : K_E.Nonempty
    · have h_iter_K : ContinuousOn (fun y => iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y) K_E :=
        (h_iter_contOn j P₀ Q).mono hK_sub
      have h_cont_norm : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y‖) K_E :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
        hK_compact.exists_isMaxOn hKne h_cont_norm
      refine ⟨‖iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y₀‖,
        norm_nonneg _, ?_⟩
      intro y hy
      have hy_U : y ∈ U := hK_sub hy
      have h₁ : ‖iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y‖ ≤
          ‖iteratedFDerivWithin ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y₀‖ :=
        hy₀_max hy
      have h₂ : iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y =
          iteratedFDeriv ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) y :=
        h_iteratedFDerivWithin_eq j P₀ Q y hy_U
      rw [h₂] at h₁
      exact h₁
    · refine ⟨0, le_refl _, ?_⟩
      intro y hy
      exact absurd ⟨y, hy⟩ hKne
  choose Cj hCj_nn hCj_bd using h_per_triple
  by_cases hk : k = 0
  · refine ⟨0, le_refl _, ?_⟩
    intro j hj _ _ _ _
    subst hk
    simp at hj
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    let T : Finset (ℕ × TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s) :=
      (Finset.range k) ×ˢ ((Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)))
    have hT_ne : T.Nonempty := by
      classical
      let P₀_witness : TensorCompIdx (E := E) r s :=
        (fun _ : Fin r => ⟨0, (NeZero.pos _)⟩,
          fun _ : Fin s => ⟨0, (NeZero.pos _)⟩)
      refine ⟨(0, P₀_witness, P₀_witness), ?_⟩
      simp [T, Finset.mem_product, Finset.mem_range, hk_pos]
    let C : ℝ := T.sup' hT_ne (fun t => Cj t.1 t.2.1 t.2.2)
    have hC_ge : ∀ j P₀ Q, (j, P₀, Q) ∈ T → Cj j P₀ Q ≤ C := by
      intro j P₀ Q ht
      have := Finset.le_sup' (f := fun t : ℕ × TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s => Cj t.1 t.2.1 t.2.2) ht
      exact this
    obtain ⟨t₀, ht₀⟩ := hT_ne
    have hC_nn : 0 ≤ C :=
      le_trans (hCj_nn t₀.1 t₀.2.1 t₀.2.2) (hC_ge t₀.1 t₀.2.1 t₀.2.2 ht₀)
    refine ⟨C, hC_nn, ?_⟩
    intro j hj P₀ Q y hy
    have hmem : (j, P₀, Q) ∈ T := by
      refine Finset.mem_product.mpr ⟨hj, ?_⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    exact (hCj_bd j P₀ Q y hy).trans (hC_ge j P₀ Q hmem)

set_option maxHeartbeats 800000 in

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartTransition_Ck_bound_on_compact_manifold
    (r s k : ℕ) (α β : M)
    {K_M : Set M} (hK_compact : IsCompact K_M)
    (hK_α : K_M ⊆ (chartAt H α).source)
    (hK_β : K_M ⊆ (chartAt H β).source) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ∈ Finset.range k,
      ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ∀ x ∈ K_M,
        ‖iteratedFDeriv ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q)
            ((toEuclidean (E := E)) ((extChartAt I α) x))‖ ≤ C := by
  classical
  let f : M → EuclN := fun x => (toEuclidean (E := E)) ((extChartAt I α) x)
  have h_ext_cont : ContinuousOn (extChartAt I α) (chartAt H α).source := by
    have h := continuousOn_extChartAt (I := I) α
    rw [extChartAt_source (I := I)] at h
    exact h
  have h_toE_cont : Continuous (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous
  have hf_cont : ContinuousOn f (chartAt H α).source :=
    h_toE_cont.continuousOn.comp h_ext_cont (fun _ hx => Set.mem_univ _)
  have h_KM_sub : K_M ⊆ (chartAt H α).source := hK_α
  have hK_E_compact : IsCompact (f '' K_M) :=
    hK_compact.image_of_continuousOn (hf_cont.mono h_KM_sub)
  have h_KE_sub : f '' K_M ⊆
      chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β := by
    rintro y ⟨x, hx, hfx⟩
    have hx_src : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hK_α hx
    have hx_tgt : (extChartAt I α) x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_src
    have h_first : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      refine ⟨(extChartAt I α) x, hx_tgt, ?_⟩
      change (toEuclidean (E := E)) ((extChartAt I α) x) = y
      exact hfx
    have h_toE_symm : (toEuclidean (E := E)).symm y = (extChartAt I α) x := by
      have : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) x)) = (extChartAt I α) x := by simp
      rw [← hfx]; exact this
    have h_chart_symm : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) = x := by
      rw [h_toE_symm]
      exact (extChartAt I α).left_inv hx_src
    have h_second : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) ∈ (chartAt H β).source := by
      rw [h_chart_symm]; exact hK_β hx
    exact ⟨h_first, h_second⟩
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    tensorChartTransition_Ck_bound_on_compact (E := E) (I := I) (M := M)
      r s k α β hK_E_compact h_KE_sub
  refine ⟨C, hC_nn, ?_⟩
  intro j hj P₀ Q x hx
  have hf_mem : f x ∈ f '' K_M := ⟨x, hx, rfl⟩
  exact hC_bd j hj P₀ Q (f x) hf_mem

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
