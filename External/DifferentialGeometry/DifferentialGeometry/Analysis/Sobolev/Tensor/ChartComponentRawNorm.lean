import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.POUFDerivBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def chartComponentRawSobolevNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem wkpNormChartRaw_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s) :
    chartComponentRawSobolevNorm (I := I) (M := M) g r s k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (chartPushedRaw (I := I) (M := M) α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem wkpNormChartRaw_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s) :
    0 ≤ chartComponentRawSobolevNorm (I := I) (M := M) g r s k T :=
  zero_le _

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChartRaw_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    chartComponentRawSobolevNorm (I := I) (M := M) g r s k (0 : SmoothCcTensor g r s) = 0 := by
  classical
  unfold chartComponentRawSobolevNorm
  refine Finset.sum_eq_zero ?_
  intro α _
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  have hraw_zero :
      tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx = (fun _ : M => (0 : ℝ)) := by
    funext x
    rw [tensorChartComponentRaw_def]
    have hzero : tensorTrivProj (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α x = 0 := by
      unfold tensorTrivProj
      have hsec : (0 : SmoothCcTensor g r s).toSection x = 0 := rfl
      rw [hsec, map_zero]
    rw [hzero, map_zero]
  rw [hraw_zero]
  have hpush_zero :
      chartPushedRaw (I := I) (M := M) α (fun _ : M => (0 : ℝ)) =
        (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
    funext y
    classical
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
  rw [hpush_zero]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw
    (α : M) (ρ u : M → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartPushedRaw (I := I) (M := M) α (fun x : M => ρ x * u x) y =
      chartSmoothExt (I := I) (M := M) α ρ y *
        chartPushedRaw (I := I) (M := M) α u y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy]
    have hsymm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    change (ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        (u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
       else 0) *
      u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    rw [if_pos hsymm]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy]
    rw [mul_zero]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw_funext
    (α : M) (ρ u : M → ℝ) :
    (chartPushedRaw (I := I) (M := M) α (fun x : M => ρ x * u x)) =
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartSmoothExt (I := I) (M := M) α ρ y *
          chartPushedRaw (I := I) (M := M) α u y) := by
  funext y
  exact chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw
    (I := I) (M := M) α ρ u y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_eq_chartSmoothExt_mul_chartPushedRaw_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx =
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
          chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) y) := by
  classical
  rw [tensorChartComp_def, tensorChartComponent_def]
  have hPouRaw : (tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx) =
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) := by
    funext x; rfl
  rw [hPouRaw]
  exact chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw_funext
    (I := I) (M := M) α
    (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx =
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
  classical
  rw [tensorChartComp_def, tensorChartComponent_def]
  have hpou_zero : ∀ x : M,
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := fun x =>
    chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  have hpou_comp_zero :
      (tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx) =
      (fun _ : M => (0 : ℝ)) := by
    funext x
    unfold tensorChartComponentPou
    rw [hpou_zero x]
    ring
  rw [hpou_comp_zero]
  funext y
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNorm_tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  rw [tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (I := I) (M := M) g r s T hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_eq_finsum_chartAtlasPOU
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold wtwokTwoNorm
  refine tsum_eq_sum ?_
  intro α hα
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  exact wkpNorm_tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (I := I) (M := M) g r s k T hα Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSmoothExt_chartAtlasPOU_contDiff (α : M) :
    ContDiff ℝ (⊤ : ℕ∞)
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  contDiff_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartSmoothExt_chartAtlasPOU_hasCompactSupport (α : M) :
    HasCompactSupport
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  hasCompactSupport_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedFDeriv_bound_chartSmoothExt_chartAtlasPOU
    (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (j : ℕ),
        j ≤ m →
        ‖iteratedFDeriv ℝ j
            (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y‖ ≤ C :=
  exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartSmoothExt_chartAtlasPOU_contDiff (I := I) (M := M) α)
    (chartSmoothExt_chartAtlasPOU_hasCompactSupport (I := I) (M := M) α) m

theorem exists_per_chart_leibniz_multiplier_bound
    (α : M) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ},
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2 u
            (chartTargetEuclid (I := I) (M := M) α) →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (fun y => chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
              u y)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2 u
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set η : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartSmoothExt (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hη_def
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η :=
    chartSmoothExt_chartAtlasPOU_contDiff (I := I) (M := M) α
  have hη_cpt : HasCompactSupport η :=
    chartSmoothExt_chartAtlasPOU_hasCompactSupport (I := I) (M := M) α
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_iteratedFDeriv_bound_chartSmoothExt_chartAtlasPOU
      (I := I) (M := M) α (2 * k)
  set Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hη_bound_on_Ω : ∀ j ≤ 2 * k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C :=
    fun j hj x _ => hC_bound x j hj
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) (2 * k)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
      hΩ_open hη_smooth hC_nn hη_bound_on_Ω
  exact ⟨K, hK_pos, fun {u} hu => hK_bound hu⟩

theorem wkpNorm_tensorChartComp_le_const_mul_wkpNorm_chartPushedRaw_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) (α : M) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (T : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
            (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
            (chartTargetEuclid (I := I) (M := M) α) →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (chartPushedRaw (I := I) (M := M) α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    exists_per_chart_leibniz_multiplier_bound (I := I) (M := M) α k
  refine ⟨K, hK_pos, ?_⟩
  intro T Idx Jdx hMem
  rw [tensorChartComp_eq_chartSmoothExt_mul_chartPushedRaw_raw
    (I := I) (M := M) g r s T α Idx Jdx]
  exact hK_bound hMem

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
