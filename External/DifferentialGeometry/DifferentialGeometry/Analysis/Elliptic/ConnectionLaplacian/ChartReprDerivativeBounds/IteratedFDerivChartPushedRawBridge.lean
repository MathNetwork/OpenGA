import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
theorem chartPushedRaw_sq_eq_compositionSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u y) ^ 2 =
      (u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 := by
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
    (I := I) (M := M) α u hy]

omit [IsManifold I ∞ M] in
theorem fderiv_chartPushedRaw_sq_le_compFderivSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ)
    (_hu : ContDiffOn ℝ 1 (u ∘ (extChartAt I α).symm) (extChartAt I α).target)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ‖fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y‖
      ^ 2 ≤
      ‖((toEuclidean (E := E)).symm : EuclN ≃L[ℝ] E).toContinuousLinearMap‖
          ^ 2 *
      ‖fderiv ℝ (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
  classical
  set L : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with hL_def
  set f : E → ℝ := u ∘ (extChartAt I α).symm with hf_def
  have h_open : IsOpen (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_nhds_y : DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α ∈ nhds y := h_open.mem_nhds hy
  have h_eventuallyEq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u =ᶠ[nhds y]
        (f ∘ (L : EuclN → E)) := by
    filter_upwards [h_nhds_y] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α u hz]
    rfl
  have h_fderiv_eq :
      fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y =
        fderiv ℝ (f ∘ (L : EuclN → E)) y :=
    Filter.EventuallyEq.fderiv_eq h_eventuallyEq
  rw [h_fderiv_eq]
  rw [L.comp_right_fderiv (f := f) (x := y)]
  have h_norm_comp_le :
      ‖(fderiv ℝ f (L y)).comp (L : EuclN →L[ℝ] E)‖ ≤
        ‖fderiv ℝ f (L y)‖ * ‖(L : EuclN →L[ℝ] E)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h_lhs_nn : 0 ≤ ‖(fderiv ℝ f (L y)).comp (L : EuclN →L[ℝ] E)‖ :=
    norm_nonneg _
  have h_sq_le :
      ‖(fderiv ℝ f (L y)).comp (L : EuclN →L[ℝ] E)‖ ^ 2 ≤
        (‖fderiv ℝ f (L y)‖ * ‖(L : EuclN →L[ℝ] E)‖) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nn h_norm_comp_le 2
  refine h_sq_le.trans (le_of_eq ?_)
  have h_norm_eq :
      ‖(L : EuclN →L[ℝ] E)‖ =
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖ := rfl
  rw [h_norm_eq]
  change (‖fderiv ℝ f (L y)‖ *
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖) ^ 2 =
      ‖((toEuclidean (E := E)).symm :
          EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 2 *
      ‖fderiv ℝ (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2
  rw [hf_def, hL_def]
  ring

omit [IsManifold I ∞ M] in
theorem iteratedFDeriv_two_chartPushedRaw_sq_le_compIterSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ)
    (_hu : ContDiffOn ℝ 2 (u ∘ (extChartAt I α).symm) (extChartAt I α).target)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y‖
      ^ 2 ≤
      ‖((toEuclidean (E := E)).symm : EuclN ≃L[ℝ] E).toContinuousLinearMap‖
          ^ 4 *
      ‖iteratedFDeriv ℝ 2 (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
  classical
  set L : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with hL_def
  set f : E → ℝ := u ∘ (extChartAt I α).symm with hf_def
  set s : Set E := (extChartAt I α).target with hs_def
  have h_open_target : IsOpen
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_nhds_y : DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α ∈ nhds y := h_open_target.mem_nhds hy
  have h_eventuallyEq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u =ᶠ[nhds y]
        (f ∘ (L : EuclN → E)) := by
    filter_upwards [h_nhds_y] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α u hz]
    rfl
  have h_iter_eq :
      iteratedFDeriv ℝ 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y =
        iteratedFDeriv ℝ 2 (f ∘ (L : EuclN → E)) y :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ h_eventuallyEq 2).eq_of_nhds
  rw [h_iter_eq]
  have h_preimage :
      (L : EuclN → E) ⁻¹' s = DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
    rw [hs_def]
    rw [← DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M) α]
  have h_open_s : IsOpen s := by
    rw [hs_def]; exact isOpen_extChartAt_target (I := I) α
  have h_open_preimage : IsOpen ((L : EuclN → E) ⁻¹' s) := by
    rw [h_preimage]; exact h_open_target
  have h_y_in_preimage : y ∈ (L : EuclN → E) ⁻¹' s := by
    rw [h_preimage]; exact hy
  have h_Ly_in_s : (L : EuclN → E) y ∈ s := h_y_in_preimage
  have h_iter_within_eucl :
      iteratedFDeriv ℝ 2 (f ∘ (L : EuclN → E)) y =
        iteratedFDerivWithin ℝ 2 (f ∘ (L : EuclN → E))
          ((L : EuclN → E) ⁻¹' s) y := by
    have := iteratedFDerivWithin_of_isOpen
      (n := 2) (f := f ∘ (L : EuclN → E)) (𝕜 := ℝ)
      h_open_preimage h_y_in_preimage
    exact this.symm
  rw [h_iter_within_eucl]
  have h_uniqueDiffOn_s : UniqueDiffOn ℝ s := h_open_s.uniqueDiffOn
  have h_chain :
      iteratedFDerivWithin ℝ 2 (f ∘ (L : EuclN → E))
          ((L : EuclN → E) ⁻¹' s) y =
        (iteratedFDerivWithin ℝ 2 f s ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E)) :=
    L.iteratedFDerivWithin_comp_right f h_uniqueDiffOn_s h_Ly_in_s 2
  rw [h_chain]
  have h_iter_within_E :
      iteratedFDerivWithin ℝ 2 f s ((L : EuclN → E) y) =
        iteratedFDeriv ℝ 2 f ((L : EuclN → E) y) :=
    iteratedFDerivWithin_of_isOpen (n := 2) (f := f) (𝕜 := ℝ)
      h_open_s h_Ly_in_s
  rw [h_iter_within_E]
  have h_norm_bound :
      ‖(iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E))‖ ≤
        ‖iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)‖ *
          ∏ _i : Fin 2, ‖(L : EuclN →L[ℝ] E)‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  have h_prod_eq : ∏ _i : Fin 2, ‖(L : EuclN →L[ℝ] E)‖ =
      ‖(L : EuclN →L[ℝ] E)‖ ^ 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_eq] at h_norm_bound
  have h_lhs_nn :
      0 ≤ ‖(iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E))‖ := norm_nonneg _
  have h_sq_le :
      ‖(iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E))‖ ^ 2 ≤
        (‖iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)‖ *
          ‖(L : EuclN →L[ℝ] E)‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nn h_norm_bound 2
  refine h_sq_le.trans (le_of_eq ?_)
  have h_norm_eq :
      ‖(L : EuclN →L[ℝ] E)‖ =
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖ := rfl
  rw [h_norm_eq]
  change (‖iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)‖ *
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 2) ^ 2 =
      ‖((toEuclidean (E := E)).symm :
          EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 4 *
      ‖iteratedFDeriv ℝ 2 (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2
  rw [hf_def, hL_def]
  ring

end Connection
end Integral
end DifferentialGeometry

end
