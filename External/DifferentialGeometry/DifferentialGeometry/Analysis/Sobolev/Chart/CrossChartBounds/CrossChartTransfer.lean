import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
import DifferentialGeometry.Analysis.Calculus.IteratedCompBound
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal Nat BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma contMDiffOn_extChartSymm_toEuclideanSymm (α : M) :
    ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_inner_contDiff : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.contDiff
  have h_inner : ContMDiff 𝓘(ℝ, EuclN) 𝓘(ℝ, E) ∞
      (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr h_inner_contDiff
  have h_outer : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I α).symm (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact h_outer.comp h_inner.contMDiffOn h_maps

omit [FiniteDimensional ℝ E] in
private theorem norm_iteratedFDerivWithin_comp_le_sumDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} {f : E → F} {n : ℕ} {N : WithTop ℕ∞}
    {s : Set E} {t : Set F} {x : E}
    (hg : ContDiffOn ℝ N g t) (hf : ContDiffOn ℝ N f s) (hn : (n : WithTop ℕ∞) ≤ N)
    (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s)
    (hst : MapsTo f s t) (hx : x ∈ s) {D : ℝ}
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x‖ ≤
      (n ! : ℝ) * (∑ i ∈ Finset.range (n + 1),
          ‖iteratedFDerivWithin ℝ i g t (f x)‖) * D ^ n := by
  classical
  set C : ℝ := ∑ i ∈ Finset.range (n + 1),
      ‖iteratedFDerivWithin ℝ i g t (f x)‖ with hC_def
  have hC_ge : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C := by
    intro i hi
    rw [hC_def]
    refine Finset.single_le_sum (f := fun j =>
        ‖iteratedFDerivWithin ℝ j g t (f x)‖) (fun j _ => norm_nonneg _) ?_
    exact Finset.mem_range_succ_iff.mpr hi
  exact norm_iteratedFDerivWithin_comp_le hg hf hn ht hs hst hx hC_ge hD

def pouCoeffPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (β : M) : EuclN → ℝ :=
  chartPushedRaw I β (fun x => (ρ β : C^∞⟮I, M; ℝ⟯) x)

omit [IsManifold I ∞ M] in
theorem crossChart_pushed_eq_pou_mul_comp_on_overlap
    [I.Boundaryless]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (β α : M) (u : M → ℝ)
    {y : EuclN} (hy : y ∈ chartOverlapEuclid (I := I) (M := M) β α) :
    chartPushed (I := I) (M := M) ρ β u y =
      pouCoeffPushed (I := I) (M := M) ρ β y *
        chartPushedRaw I α u (chartTransitionEuclid (I := I) (M := M) β α y) := by
  classical
  rcases hy with ⟨z, ⟨x, hx_in, hxz⟩, hzy⟩
  have hx_β : x ∈ (chartAt H β).source := hx_in.1
  have hx_α : x ∈ (chartAt H α).source := hx_in.2
  have hy_eq : y = (toEuclidean (E := E)) (extChartAt I β x) := by rw [← hzy, ← hxz]
  have hx_β_ext : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hx_β
  have h_symm_y : (extChartAt I β).symm ((toEuclidean (E := E)).symm y) = x := by
    rw [hy_eq, (toEuclidean (E := E)).symm_apply_apply, (extChartAt I β).left_inv hx_β_ext]
  have h_lhs : chartPushed (I := I) (M := M) ρ β u y =
      (ρ β : C^∞⟮I, M; ℝ⟯) x * u x := by
    unfold chartPushed
    rw [h_symm_y]
  have hy_target_β : y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [hy_eq]
    exact ⟨extChartAt I β x, (extChartAt I β).map_source hx_β_ext, rfl⟩
  have h_pou : pouCoeffPushed (I := I) (M := M) ρ β y =
      (ρ β : C^∞⟮I, M; ℝ⟯) x := by
    unfold pouCoeffPushed
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target_β, h_symm_y]
  have h_T_eq : chartTransitionEuclid (I := I) (M := M) β α y =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    rw [hy_eq]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hx_β
  have h_Ty_target_α : chartTransitionEuclid (I := I) (M := M) β α y ∈
      chartTargetEuclid (I := I) (M := M) α := by
    rw [h_T_eq]
    have hx_α_ext : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hx_α
    exact ⟨extChartAt I α x, (extChartAt I α).map_source hx_α_ext, rfl⟩
  have h_comp : chartPushedRaw I α u (chartTransitionEuclid (I := I) (M := M) β α y) =
      u x := by
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u h_Ty_target_α, h_T_eq,
      (toEuclidean (E := E)).symm_apply_apply]
    have hx_α_ext : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hx_α
    rw [(extChartAt I α).left_inv hx_α_ext]
  rw [h_lhs, h_pou, h_comp]

lemma pouCoeffPushed_contDiffOn
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (β : M) :
    ContDiffOn ℝ ∞ (pouCoeffPushed (I := I) (M := M) ρ β)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Φ : EuclN → ℝ := fun y =>
    (ρ β : C^∞⟮I, M; ℝ⟯) ((extChartAt I β).symm ((toEuclidean (E := E)).symm y))
    with hΦ_def
  have hEqOn : Set.EqOn (pouCoeffPushed (I := I) (M := M) ρ β) Φ
      (chartTargetEuclid (I := I) (M := M) β) := by
    intro y hy
    unfold pouCoeffPushed
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy]
  have h_chart_symm : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I β).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) β) :=
    contMDiffOn_extChartSymm_toEuclideanSymm (I := I) (M := M) β
  have h_pou_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((ρ β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (ρ β).contMDiff
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ Φ
      (chartTargetEuclid (I := I) (M := M) β) := by
    intro y hy
    exact (h_pou_smooth _).comp_contMDiffWithinAt y (h_chart_symm y hy)
  have h_contDiffOn : ContDiffOn ℝ ∞ Φ (chartTargetEuclid (I := I) (M := M) β) :=
    (contMDiffOn_iff_contDiffOn).mp h_comp
  exact h_contDiffOn.congr hEqOn

set_option maxHeartbeats 1600000 in

theorem crossChart_transfer_bound
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (β α : M) (k : ℕ)
    {K_M : Set M} (hK_compact : IsCompact K_M)
    (hK_β : K_M ⊆ (chartAt H β).source)
    (hK_α : K_M ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ j ∈ Finset.range (k + 1),
        ∀ x ∈ K_M,
          ‖iteratedFDeriv ℝ j (chartPushed (I := I) (M := M) ρ β u)
              ((toEuclidean (E := E)) (extChartAt I β x))‖ ≤
            C * ∑ i ∈ Finset.range (j + 1),
              ‖iteratedFDeriv ℝ i (chartPushedRaw I α u)
                (chartTransitionEuclid (I := I) (M := M) β α
                  ((toEuclidean (E := E)) (extChartAt I β x)))‖ := by
  classical
  set Ωβ : Set EuclN := chartOverlapEuclid (I := I) (M := M) β α with hΩβ_def
  have hΩβ_open : IsOpen Ωβ := chartOverlapEuclid_isOpen (I := I) (M := M) β α
  have hΩβ_uniqueDiff : UniqueDiffOn ℝ Ωβ := hΩβ_open.uniqueDiffOn
  set Ωα : Set EuclN := chartOverlapEuclid (I := I) (M := M) α β with hΩα_def
  have hΩα_open : IsOpen Ωα := chartOverlapEuclid_isOpen (I := I) (M := M) α β
  have hΩα_uniqueDiff : UniqueDiffOn ℝ Ωα := hΩα_open.uniqueDiffOn
  set fβ : M → EuclN := fun x => (toEuclidean (E := E)) (extChartAt I β x) with hfβ_def
  have hK_E_compact : IsCompact (fβ '' K_M) :=
    kEuclid_compact (I := I) (M := M) β hK_compact hK_β
  have hK_E_sub : fβ '' K_M ⊆ Ωβ :=
    kEuclid_subset_overlap (I := I) (M := M) β α hK_β hK_α
  have hT_contDiffOn : ContDiffOn ℝ ∞
      (chartTransitionEuclid (I := I) (M := M) β α) Ωβ := by
    have h := chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) β α
    exact h.of_le (by exact_mod_cast le_top)
  have hT_maps : MapsTo (chartTransitionEuclid (I := I) (M := M) β α) Ωβ Ωα :=
    fun y hy => chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) β α hy
  have hT_iter_contOn : ∀ i : ℕ,
      ContinuousOn (fun y => iteratedFDerivWithin ℝ i
        (chartTransitionEuclid (I := I) (M := M) β α) Ωβ y) Ωβ :=
    fun i => hT_contDiffOn.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast le_top) hΩβ_uniqueDiff
  have hpou_contDiffOn_target : ContDiffOn ℝ ∞
      (pouCoeffPushed (I := I) (M := M) ρ β)
      (chartTargetEuclid (I := I) (M := M) β) :=
    pouCoeffPushed_contDiffOn (I := I) (M := M) ρ β
  have hΩβ_sub_target : Ωβ ⊆ chartTargetEuclid (I := I) (M := M) β :=
    chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α
  have hpou_contDiffOn : ContDiffOn ℝ ∞
      (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ :=
    hpou_contDiffOn_target.mono hΩβ_sub_target
  have hpou_iter_contOn : ∀ i : ℕ,
      ContinuousOn (fun y => iteratedFDerivWithin ℝ i
        (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y) Ωβ :=
    fun i => hpou_contDiffOn.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast le_top) hΩβ_uniqueDiff
  obtain ⟨D, hD_one, hD_bd⟩ :
      ∃ D : ℝ, 1 ≤ D ∧ ∀ i, i ≤ k → ∀ y ∈ fβ '' K_M,
        ‖iteratedFDerivWithin ℝ i
          (chartTransitionEuclid (I := I) (M := M) β α) Ωβ y‖ ≤ D := by
    by_cases hKne : (fβ '' K_M).Nonempty
    · have hmax : ∀ i, i ≤ k → ∃ Mi : ℝ, 0 ≤ Mi ∧ ∀ y ∈ fβ '' K_M,
          ‖iteratedFDerivWithin ℝ i
            (chartTransitionEuclid (I := I) (M := M) β α) Ωβ y‖ ≤ Mi := by
        intro i _
        have h_contK : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ i
            (chartTransitionEuclid (I := I) (M := M) β α) Ωβ y‖) (fβ '' K_M) :=
          continuous_norm.comp_continuousOn ((hT_iter_contOn i).mono hK_E_sub)
        obtain ⟨z, _hz, hz_max⟩ := hK_E_compact.exists_isMaxOn hKne h_contK
        exact ⟨_, norm_nonneg _, fun y hy => hz_max hy⟩
      choose Mi hMi0 hMib using hmax
      refine ⟨max 1 ((Finset.range (k + 1)).sup' (by simp)
        (fun i => if hi : i ≤ k then Mi i hi else 0)), le_max_left _ _, ?_⟩
      intro i hi y hy
      refine (hMib i hi y hy).trans ?_
      refine le_trans ?_ (le_max_right _ _)
      refine Finset.le_sup'_of_le _ (Finset.mem_range_succ_iff.mpr hi) ?_
      simp only [hi, dif_pos, le_refl]
    · exact ⟨1, le_refl _, fun i _ y hy => absurd ⟨y, hy⟩ hKne⟩
  obtain ⟨B, hB0, hB_bd⟩ :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ i, i ≤ k → ∀ y ∈ fβ '' K_M,
        ‖iteratedFDerivWithin ℝ i
          (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖ ≤ B := by
    by_cases hKne : (fβ '' K_M).Nonempty
    · have hmax : ∀ i, i ≤ k → ∃ Mi : ℝ, 0 ≤ Mi ∧ ∀ y ∈ fβ '' K_M,
          ‖iteratedFDerivWithin ℝ i
            (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖ ≤ Mi := by
        intro i _
        have h_contK : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ i
            (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖) (fβ '' K_M) :=
          continuous_norm.comp_continuousOn ((hpou_iter_contOn i).mono hK_E_sub)
        obtain ⟨z, _hz, hz_max⟩ := hK_E_compact.exists_isMaxOn hKne h_contK
        exact ⟨_, norm_nonneg _, fun y hy => hz_max hy⟩
      choose Mi hMi0 hMib using hmax
      refine ⟨(Finset.range (k + 1)).sup' (by simp)
        (fun i => if hi : i ≤ k then Mi i hi else 0), ?_, ?_⟩
      · refine Finset.le_sup'_of_le _ (Finset.mem_range_succ_iff.mpr (Nat.zero_le k)) ?_
        simp only [Nat.zero_le, dif_pos]; exact hMi0 0 (Nat.zero_le k)
      · intro i hi y hy
        refine (hMib i hi y hy).trans ?_
        refine Finset.le_sup'_of_le _ (Finset.mem_range_succ_iff.mpr hi) ?_
        simp only [hi, dif_pos, le_refl]
    · exact ⟨0, le_refl _, fun i _ y hy => absurd ⟨y, hy⟩ hKne⟩
  set C : ℝ := (k + 1 : ℕ) * (2 ^ k : ℕ) * ((k ! : ℝ) * B * D ^ k + 1) with hC_def
  have hD_nonneg : (0 : ℝ) ≤ D := le_trans zero_le_one hD_one
  have hDk_nonneg : (0 : ℝ) ≤ D ^ k := pow_nonneg hD_nonneg k
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h1 : (0 : ℝ) ≤ (k ! : ℝ) * B * D ^ k :=
      mul_nonneg (mul_nonneg (by positivity) hB0) hDk_nonneg
    have h2 : (0 : ℝ) ≤ ((k ! : ℝ) * B * D ^ k + 1) := by linarith
    positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u hu_smooth j hj x hx
  have hj_le : j ≤ k := Finset.mem_range_succ_iff.mp hj
  set y : EuclN := fβ x with hy_def
  have hy_mem_image : y ∈ fβ '' K_M := ⟨x, hx, rfl⟩
  have hy_overlap : y ∈ Ωβ := hK_E_sub hy_mem_image
  have hraw_contDiffOn : ContDiffOn ℝ ∞ (chartPushedRaw I α u) Ωα := by
    have hΨ_eqOn : Set.EqOn (chartPushedRaw I α u)
        (fun z => u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro z hz
      exact chartPushedRaw_apply_of_mem (I := I) (M := M) α u hz
    have h_chart_symm : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
        (fun z : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm z))
        (chartTargetEuclid (I := I) (M := M) α) :=
      contMDiffOn_extChartSymm_toEuclideanSymm (I := I) (M := M) α
    have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞
        (fun z => u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro z hz
      exact (hu_smooth _).comp_contMDiffWithinAt z (h_chart_symm z hz)
    have h_target_contDiffOn : ContDiffOn ℝ ∞
        (fun z => u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (contMDiffOn_iff_contDiffOn).mp h_comp
    have hΩα_sub_target : Ωα ⊆ chartTargetEuclid (I := I) (M := M) α :=
      chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β
    exact (h_target_contDiffOn.congr hΨ_eqOn).mono hΩα_sub_target
  set prodFun : EuclN → ℝ := fun z =>
    pouCoeffPushed (I := I) (M := M) ρ β z *
      chartPushedRaw I α u (chartTransitionEuclid (I := I) (M := M) β α z)
    with hprod_def
  have h_eqOn_prod : Set.EqOn (chartPushed (I := I) (M := M) ρ β u) prodFun Ωβ := by
    intro z hz
    exact crossChart_pushed_eq_pou_mul_comp_on_overlap (I := I) (M := M) ρ β α u hz
  have h_iter_lhs :
      iteratedFDeriv ℝ j (chartPushed (I := I) (M := M) ρ β u) y =
      iteratedFDerivWithin ℝ j prodFun Ωβ y := by
    have h_within_pushed :
        iteratedFDerivWithin ℝ j (chartPushed (I := I) (M := M) ρ β u) Ωβ y =
        iteratedFDeriv ℝ j (chartPushed (I := I) (M := M) ρ β u) y :=
      iteratedFDerivWithin_of_isOpen j hΩβ_open hy_overlap
    rw [← h_within_pushed]
    exact iteratedFDerivWithin_congr h_eqOn_prod hy_overlap j
  set compFun : EuclN → ℝ := fun z =>
    chartPushedRaw I α u (chartTransitionEuclid (I := I) (M := M) β α z)
    with hcomp_def
  have hcomp_contDiffOn : ContDiffOn ℝ ∞ compFun Ωβ := by
    have h := hraw_contDiffOn.comp hT_contDiffOn hT_maps
    exact h
  have h_leibniz :
      ‖iteratedFDerivWithin ℝ j prodFun Ωβ y‖ ≤
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i
              (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖ *
            ‖iteratedFDerivWithin ℝ (j - i) compFun Ωβ y‖ := by
    have h := norm_iteratedFDerivWithin_mul_le
      (f := pouCoeffPushed (I := I) (M := M) ρ β) (g := compFun)
      (hpou_contDiffOn.of_le (by exact_mod_cast le_top))
      (hcomp_contDiffOn.of_le (by exact_mod_cast le_top))
      hΩβ_uniqueDiff hy_overlap (n := j) le_rfl
    exact h
  have hT_shape : ∀ m : ℕ, m ≤ k → ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i
        (chartTransitionEuclid (I := I) (M := M) β α) Ωβ y‖ ≤ D ^ i := by
    intro m _ i hi1 him
    have hi_le_k : i ≤ k := le_trans him ‹m ≤ k›
    have h := hD_bd i hi_le_k y hy_mem_image
    calc ‖iteratedFDerivWithin ℝ i
          (chartTransitionEuclid (I := I) (M := M) β α) Ωβ y‖
        ≤ D := h
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ hD_one hi1
  have h_faa : ∀ m : ℕ, m ≤ j →
      ‖iteratedFDerivWithin ℝ m compFun Ωβ y‖ ≤
        (m ! : ℝ) * (∑ i ∈ Finset.range (m + 1),
            ‖iteratedFDerivWithin ℝ i (chartPushedRaw I α u) Ωα
              (chartTransitionEuclid (I := I) (M := M) β α y)‖) * D ^ m := by
    intro m hm
    have hm_le_k : m ≤ k := le_trans hm hj_le
    exact norm_iteratedFDerivWithin_comp_le_sumDeriv
      (g := chartPushedRaw I α u)
      (f := chartTransitionEuclid (I := I) (M := M) β α)
      hraw_contDiffOn hT_contDiffOn (by exact_mod_cast le_top)
      hΩα_uniqueDiff hΩβ_uniqueDiff hT_maps hy_overlap
      (fun i hi1 him => hT_shape m hm_le_k i hi1 him)
  have hTy_overlap : chartTransitionEuclid (I := I) (M := M) β α y ∈ Ωα :=
    hT_maps hy_overlap
  have h_raw_within_eq : ∀ i : ℕ,
      iteratedFDerivWithin ℝ i (chartPushedRaw I α u) Ωα
        (chartTransitionEuclid (I := I) (M := M) β α y) =
      iteratedFDeriv ℝ i (chartPushedRaw I α u)
        (chartTransitionEuclid (I := I) (M := M) β α y) :=
    fun i => iteratedFDerivWithin_of_isOpen i hΩα_open hTy_overlap
  set S : ℝ := ∑ i ∈ Finset.range (j + 1),
    ‖iteratedFDeriv ℝ i (chartPushedRaw I α u)
      (chartTransitionEuclid (I := I) (M := M) β α y)‖ with hS_def
  have hS_nonneg : 0 ≤ S := by
    rw [hS_def]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h_inner_sum_le : ∀ m : ℕ, m ≤ j →
      (∑ i ∈ Finset.range (m + 1),
        ‖iteratedFDeriv ℝ i (chartPushedRaw I α u)
          (chartTransitionEuclid (I := I) (M := M) β α y)‖) ≤ S := by
    intro m hm
    rw [hS_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
    intro i hi
    rw [Finset.mem_range] at hi ⊢; omega
  have h_faa' : ∀ m : ℕ, m ≤ j →
      ‖iteratedFDerivWithin ℝ m compFun Ωβ y‖ ≤
        (m ! : ℝ) * S * D ^ m := by
    intro m hm
    refine (h_faa m hm).trans ?_
    have h_rw : (∑ i ∈ Finset.range (m + 1),
        ‖iteratedFDerivWithin ℝ i (chartPushedRaw I α u) Ωα
          (chartTransitionEuclid (I := I) (M := M) β α y)‖) =
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ i (chartPushedRaw I α u)
            (chartTransitionEuclid (I := I) (M := M) β α y)‖ := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_raw_within_eq i]
    rw [h_rw]
    have hm_factorial_nonneg : (0 : ℝ) ≤ (m ! : ℝ) := by positivity
    have hDm_nonneg : (0 : ℝ) ≤ D ^ m := by positivity
    have h_sum_le := h_inner_sum_le m hm
    have : (m ! : ℝ) * (∑ i ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ i (chartPushedRaw I α u)
            (chartTransitionEuclid (I := I) (M := M) β α y)‖) * D ^ m ≤
        (m ! : ℝ) * S * D ^ m := by
      gcongr
    exact this
  have h_summand_bound : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖ *
        ‖iteratedFDerivWithin ℝ (j - i) compFun Ωβ y‖ ≤
      (j.choose i : ℝ) * B * (((j - i)! : ℝ) * S * D ^ (j - i)) := by
    intro i hi
    have hi_le_j : i ≤ j := Finset.mem_range_succ_iff.mp hi
    have hi_le_k : i ≤ k := le_trans hi_le_j hj_le
    have h_pou_i : ‖iteratedFDerivWithin ℝ i
        (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖ ≤ B :=
      hB_bd i hi_le_k y hy_mem_image
    have h_comp_i : ‖iteratedFDerivWithin ℝ (j - i) compFun Ωβ y‖ ≤
        ((j - i)! : ℝ) * S * D ^ (j - i) :=
      h_faa' (j - i) (Nat.sub_le j i)
    have hchoose_nonneg : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    have h_pou_nonneg : (0 : ℝ) ≤ ‖iteratedFDerivWithin ℝ i
        (pouCoeffPushed (I := I) (M := M) ρ β) Ωβ y‖ := norm_nonneg _
    have h_comp_nonneg : (0 : ℝ) ≤ ‖iteratedFDerivWithin ℝ (j - i) compFun Ωβ y‖ :=
      norm_nonneg _
    gcongr
  have h_sum_bound :
      ‖iteratedFDerivWithin ℝ j prodFun Ωβ y‖ ≤
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * B * (((j - i)! : ℝ) * S * D ^ (j - i)) :=
    h_leibniz.trans (Finset.sum_le_sum h_summand_bound)
  have h_RHS_le : ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * B * (((j - i)! : ℝ) * S * D ^ (j - i)) ≤ C * S := by
    have h_each : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * B * (((j - i)! : ℝ) * S * D ^ (j - i)) ≤
          (2 ^ k : ℕ) * B * ((k ! : ℝ) * S * D ^ k) := by
      intro i hi
      have hi_le_j : i ≤ j := Finset.mem_range_succ_iff.mp hi
      have h_choose : (j.choose i : ℝ) ≤ (2 ^ k : ℕ) := by
        have h1 : j.choose i ≤ 2 ^ j := by
          calc j.choose i ≤ ∑ m ∈ Finset.range (j + 1), j.choose m :=
                Finset.single_le_sum (f := fun m => j.choose m)
                  (fun m _ => Nat.zero_le _) (Finset.mem_range_succ_iff.mpr hi_le_j)
            _ = 2 ^ j := by rw [Nat.sum_range_choose]
        have h2 : (2 : ℕ) ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hj_le
        exact_mod_cast le_trans h1 h2
      have h_fact : ((j - i)! : ℝ) ≤ (k ! : ℝ) := by
        have : (j - i)! ≤ k ! := Nat.factorial_le (le_trans (Nat.sub_le j i) hj_le)
        exact_mod_cast this
      have h_pow : D ^ (j - i) ≤ D ^ k :=
        pow_le_pow_right₀ hD_one (le_trans (Nat.sub_le j i) hj_le)
      have hB_nonneg : (0 : ℝ) ≤ B := hB0
      have hS_nn : (0 : ℝ) ≤ S := hS_nonneg
      have hD_nn : (0 : ℝ) ≤ D := le_trans zero_le_one hD_one
      gcongr
    refine (Finset.sum_le_sum h_each).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hj1_le : ((j + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hj_le 1
    rw [hC_def]
    have hterm_nonneg : (0 : ℝ) ≤ (2 ^ k : ℕ) * B * ((k ! : ℝ) * S * D ^ k) := by
      have : (0 : ℝ) ≤ (2 ^ k : ℕ) := by positivity
      have hB_nonneg : (0 : ℝ) ≤ B := hB0
      positivity
    calc ((j + 1 : ℕ) : ℝ) * ((2 ^ k : ℕ) * B * ((k ! : ℝ) * S * D ^ k))
        ≤ ((k + 1 : ℕ) : ℝ) * ((2 ^ k : ℕ) * B * ((k ! : ℝ) * S * D ^ k)) := by
          gcongr
      _ = ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℕ) * ((k ! : ℝ) * B * D ^ k) * S := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℕ) * ((k ! : ℝ) * B * D ^ k + 1) * S := by
          have hbase_nonneg : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℕ) := by positivity
          have hkbd_le : (k ! : ℝ) * B * D ^ k ≤ (k ! : ℝ) * B * D ^ k + 1 := by linarith
          gcongr
  rw [h_iter_lhs, hS_def]
  calc ‖iteratedFDerivWithin ℝ j prodFun Ωβ y‖
      ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * B * (((j - i)! : ℝ) * S * D ^ (j - i)) := h_sum_bound
    _ ≤ C * S := h_RHS_le

theorem crossChart_transfer_bound_const
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (β α : M) (k : ℕ)
    {K_M : Set M} (hK_compact : IsCompact K_M)
    (hK_β : K_M ⊆ (chartAt H β).source)
    (hK_α : K_M ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ j ∈ Finset.range (k + 1),
        ∀ x ∈ K_M,
          ‖iteratedFDeriv ℝ j (chartPushed (I := I) (M := M) ρ β u)
              ((toEuclidean (E := E)) (extChartAt I β x))‖ ≤
            C * ∑ i ∈ Finset.range (j + 1),
              ‖iteratedFDeriv ℝ i (chartPushedRaw I α u)
                (chartTransitionEuclid (I := I) (M := M) β α
                  ((toEuclidean (E := E)) (extChartAt I β x)))‖ :=
  crossChart_transfer_bound (I := I) (M := M) ρ β α k hK_compact hK_β hK_α

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
