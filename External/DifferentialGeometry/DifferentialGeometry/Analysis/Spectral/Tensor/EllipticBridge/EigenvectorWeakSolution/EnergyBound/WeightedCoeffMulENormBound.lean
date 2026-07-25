import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section ExplicitNormBound

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


theorem eLpNorm_weighted_contDiffOn_mul_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (_hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (_hw : MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (hw_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => c y * w y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          eLpNorm w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, ?_⟩
  have h_dom : ∀ᵐ y ∂μw, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
    · rw [hy hyK, mul_zero, smul_zero, norm_zero]
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μw ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * eLpNorm w 2 μw := by
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μw := h_smul

theorem eLpNorm_weighted_contDiffOn_mul_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (_hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : EuclN → ℝ,
        MemLp w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) →
        (∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)), y ∉ K → w y = 0) →
        eLpNorm (fun y => c y * w y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm w 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, fun w hw hw_zero => ?_⟩
  have h_dom : ∀ᵐ y ∂μw, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
    · rw [hy hyK, mul_zero, smul_zero, norm_zero]
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μw ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * eLpNorm w 2 μw := by
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μw := h_smul

end ExplicitNormBound

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (α : M)

example {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (hw_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => c y * w y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          eLpNorm w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_weighted_contDiffOn_mul_le (I := I) (M := M) g α hc
    hK_compact hK_meas hK_in hw hw_zero

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
