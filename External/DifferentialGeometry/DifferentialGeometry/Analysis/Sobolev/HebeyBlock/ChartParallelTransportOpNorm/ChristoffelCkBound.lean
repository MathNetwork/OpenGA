import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.FDerivDecomp
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents


namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 800000 in

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_Ck_bound_from_metric_Ck1 [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (k : ℕ) (α : M)
    {K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK_compact : IsCompact K)
    (hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ∈ Finset.range k,
        ∀ y ∈ K,
          ‖iteratedFDeriv ℝ j
              (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
                chartChristoffelBilin (I := I) (M := M) g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
              y‖ ≤ C := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let Φ : EuclideanSpace ℝ (Fin n) → (E →L[ℝ] E →L[ℝ] E) := fun z =>
    chartChristoffelBilin (I := I) (M := M) g α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
  have hΦ : Φ = fun z =>
    chartChristoffelBilin (I := I) (M := M) g α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := rfl
  let U : Set (EuclideanSpace ℝ (Fin n)) := chartTargetEuclid (I := I) (M := M) α
  have hU_open : IsOpen U := chartTargetEuclid_isOpen (I := I) (M := M) α
  let Ψ : EuclideanSpace ℝ (Fin n) → (E →L[ℝ] E →L[ℝ] E) := fun z =>
    ∑ i : Fin n, ∑ j : Fin n, ∑ κ : Fin n,
      ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
        (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
          (chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z) •
            (chartModelBasis E) κ))
  have hΨ : Ψ = fun z =>
    ∑ i : Fin n, ∑ j : Fin n, ∑ κ : Fin n,
      ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
        (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
          (chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z) •
            (chartModelBasis E) κ)) := rfl
  have h_toE_symm_mem_target : ∀ {y : EuclideanSpace ℝ (Fin n)},
      y ∈ U → (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; simp
    rw [hyz]
    exact hz_target
  have hΦΨ_on_U : Set.EqOn Φ Ψ U := by
    intro y hy
    have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      h_toE_symm_mem_target hy
    have h_right_inv :
        (extChartAt I α) ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
          (toEuclidean (E := E)).symm y :=
      (extChartAt I α).right_inv hy_target
    simp only [hΦ, hΨ, chartChristoffelBilin]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun κ _ => ?_)
    rw [h_right_inv]
  have h_target_eq_interior :
      (extChartAt I α).target = interior ((extChartAt I α).target : Set E) :=
    (isOpen_extChartAt_target (I := I) α).interior_eq.symm
  have h_toE_symm_contDiff : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) => (toEuclidean (E := E)).symm z) :=
    (toEuclidean (E := E)).symm.contDiff
  have h_chart_chr_scalar_contDiffOn : ∀ i j κ : Fin n,
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) =>
          chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z)) U := by
    intro i j κ
    have h_inner_contDiff : ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) => (toEuclidean (E := E)).symm z) Set.univ :=
      h_toE_symm_contDiff.contDiffOn
    have h_outer_contDiffOn : ContDiffOn ℝ ∞
        (chartChristoffel (I := I) g α i j κ)
        (interior ((extChartAt I α).target : Set E)) :=
      chartChristoffel_contDiffOn_interior (I := I) g α i j κ
    have h_maps : Set.MapsTo (fun z : EuclideanSpace ℝ (Fin n) =>
        (toEuclidean (E := E)).symm z)
        U (interior ((extChartAt I α).target : Set E)) := by
      intro z hz
      have hz_target : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target :=
        h_toE_symm_mem_target hz
      rw [← h_target_eq_interior]
      exact hz_target
    exact h_outer_contDiffOn.comp (h_inner_contDiff.mono (Set.subset_univ _)) h_maps
  let N : Fin n → Fin n → Fin n → (E →L[ℝ] E →L[ℝ] E) := fun i j κ =>
    ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
      (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
        ((chartModelBasis E) κ))
  have h_summand_eq : ∀ (i j κ : Fin n) (z : EuclideanSpace ℝ (Fin n)),
      ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
          (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
            (chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z) •
              (chartModelBasis E) κ)) =
        chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z) •
          N i j κ := by
    intro i j κ z
    set s : ℝ := chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z)
    have h_inner : ((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
        (s • (chartModelBasis E) κ) =
        s • ((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
              ((chartModelBasis E) κ) := by
      ext w
      simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
        smul_smul, mul_comm]
    rw [h_inner]
    have h_outer : ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
        (s • ((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
                ((chartModelBasis E) κ)) =
        s • ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
              (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
                ((chartModelBasis E) κ)) := by
      ext v w
      simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
        smul_smul, mul_comm]
    exact h_outer
  have hΨ_contDiffOn : ContDiffOn ℝ ∞ Ψ U := by
    refine ContDiffOn.sum (fun i _ => ?_)
    refine ContDiffOn.sum (fun j _ => ?_)
    refine ContDiffOn.sum (fun κ _ => ?_)
    have h_scalar := h_chart_chr_scalar_contDiffOn i j κ
    have h_eq : (fun z : EuclideanSpace ℝ (Fin n) =>
        ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
          (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
            (chartChristoffel (I := I) g α i j κ ((toEuclidean (E := E)).symm z) •
              (chartModelBasis E) κ))) =
        fun z => chartChristoffel (I := I) g α i j κ
          ((toEuclidean (E := E)).symm z) • N i j κ := by
      funext z
      exact h_summand_eq i j κ z
    rw [h_eq]
    exact h_scalar.smul_const (N i j κ)
  have h_iterated_eq : ∀ j_idx : ℕ, ∀ y ∈ U,
      iteratedFDeriv ℝ j_idx Φ y = iteratedFDeriv ℝ j_idx Ψ y := by
    intro j_idx y hy
    have hΦΨ_nhds : Φ =ᶠ[nhds y] Ψ :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨U, hU_open.mem_nhds hy, fun z hz => hΦΨ_on_U hz⟩
    exact (Filter.EventuallyEq.iteratedFDeriv ℝ hΦΨ_nhds j_idx).eq_of_nhds
  have hU_uniqueDiff : UniqueDiffOn ℝ U := hU_open.uniqueDiffOn
  have h_iteratedFDerivWithin_eq_iteratedFDeriv : ∀ j_idx : ℕ, ∀ y ∈ U,
      iteratedFDerivWithin ℝ j_idx Ψ U y = iteratedFDeriv ℝ j_idx Ψ y :=
    fun j_idx y hy => iteratedFDerivWithin_of_isOpen j_idx hU_open hy
  have h_iterated_contOn : ∀ j_idx : ℕ,
      ContinuousOn (fun y => iteratedFDerivWithin ℝ j_idx Ψ U y) U := fun j_idx =>
    hΨ_contDiffOn.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU_uniqueDiff
  have h_per_order : ∀ j_idx : ℕ, ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ y ∈ K,
      ‖iteratedFDeriv ℝ j_idx Φ y‖ ≤ Cj := by
    intro j_idx
    by_cases hKne : K.Nonempty
    · have h_iter_K : ContinuousOn (iteratedFDerivWithin ℝ j_idx Ψ U) K :=
        (h_iterated_contOn j_idx).mono hK_sub
      have h_cont_within : ContinuousOn (fun y =>
          ‖iteratedFDerivWithin ℝ j_idx Ψ U y‖) K :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, hy₀_K, hy₀_max⟩ := hK_compact.exists_isMaxOn hKne h_cont_within
      refine ⟨‖iteratedFDerivWithin ℝ j_idx Ψ U y₀‖, norm_nonneg _, ?_⟩
      intro y hy
      have hy_U : y ∈ U := hK_sub hy
      have h₁ : ‖iteratedFDerivWithin ℝ j_idx Ψ U y‖ ≤
          ‖iteratedFDerivWithin ℝ j_idx Ψ U y₀‖ := hy₀_max hy
      have h₂ : iteratedFDerivWithin ℝ j_idx Ψ U y =
          iteratedFDeriv ℝ j_idx Ψ y :=
        h_iteratedFDerivWithin_eq_iteratedFDeriv j_idx y hy_U
      have h₃ : iteratedFDeriv ℝ j_idx Ψ y = iteratedFDeriv ℝ j_idx Φ y :=
        (h_iterated_eq j_idx y hy_U).symm
      rw [h₂, h₃] at h₁
      exact h₁
    · refine ⟨0, le_refl _, ?_⟩
      intro y hy
      exfalso
      exact hKne ⟨y, hy⟩
  choose Cj hCj_nn hCj_bd using h_per_order
  by_cases hk : k = 0
  · refine ⟨0, le_refl _, ?_⟩
    intro j_idx hj
    subst hk
    simp at hj
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have h_nonempty : (Finset.range k).Nonempty :=
      ⟨0, Finset.mem_range.mpr hk_pos⟩
    let C : ℝ := (Finset.range k).sup' h_nonempty Cj
    have hC_ge : ∀ j_idx ∈ Finset.range k, Cj j_idx ≤ C := fun j_idx hj =>
      Finset.le_sup' Cj hj
    have hC_nn : 0 ≤ C := le_trans (hCj_nn 0) (hC_ge 0 (Finset.mem_range.mpr hk_pos))
    refine ⟨C, hC_nn, ?_⟩
    intro j_idx hj y hy
    exact (hCj_bd j_idx y hy).trans (hC_ge j_idx hj)

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
