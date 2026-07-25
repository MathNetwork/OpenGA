import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.WeightedCoeffMulENormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDiv


noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section PerSummandBound


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_indicatorPou_mul_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (w : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
          2
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
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  refine ⟨C, hC_nn, ?_⟩
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC_bd y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_dom : ∀ᵐ y ∂μw,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ ≤
        ‖(C : ℝ) • w y‖ := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hlhs :
        ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ =
          ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ * ‖w y‖ :=
      norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hci_bd y) (norm_nonneg _)
  have h_mono :
      eLpNorm
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
          2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * eLpNorm w 2 μw := by
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
        2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μw := h_smul


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_indicatorPou_mul_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : EuclN → ℝ,
        eLpNorm
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
              w y) 2
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
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  refine ⟨C, hC_nn, fun w => ?_⟩
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC_bd y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_dom : ∀ᵐ y ∂μw,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ ≤
        ‖(C : ℝ) • w y‖ := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hlhs :
        ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ =
          ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ * ‖w y‖ :=
      norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hci_bd y) (norm_nonneg _)
  have h_mono :
      eLpNorm
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
          2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * eLpNorm w 2 μw := by
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
        2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μw := h_smul

end PerSummandBound

section MeasurabilityTransfer


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma aestronglyMeasurable_weighted_of_chartL2
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ}
    (hf : AEStronglyMeasurable f (chartL2Measure (I := I) (M := M) α)) :
    AEStronglyMeasurable f
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  hf.mono_ac
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α)

end MeasurabilityTransfer

section UniformConstant


omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_eLpNorm_bound
    {ι : Type*} [Finite ι]
    {μ : Measure EuclN} {f : ι → EuclN → ℝ} {a : ι → ℝ≥0∞}
    (h : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ eLpNorm (f j) 2 μ ≤ ENNReal.ofReal C * a j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j : ι, eLpNorm (f j) 2 μ ≤ ENNReal.ofReal C * a j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose Cf hCf_nn hCf using h
  refine ⟨∑ j : ι, Cf j, Finset.sum_nonneg (fun j _ => hCf_nn j), fun j => ?_⟩
  refine (hCf j).trans (mul_le_mul_left ?_ (a j))
  exact ENNReal.ofReal_le_ofReal
    (Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j))

end UniformConstant

section MainBound

omit [CompleteSpace E] in
theorem eLpNorm_crossRightGradCoeffDivLimit_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                    g r s i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s i α P l :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set ι : Type _ :=
    Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s with hι_def
  choose CcompF hCcompF_nn hCcompF using
    (fun j : ι => eLpNorm_indicatorPou_mul_le_uniform (I := I) (M := M) g α
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2))
  choose CpartF hCpartF_nn hCpartF using
    (fun j : ι => eLpNorm_indicatorPou_mul_le_uniform (I := I) (M := M) g α
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2))
  refine ⟨max ((Fintype.card ι : ℝ) * ∑ j : ι, CcompF j)
      ((Fintype.card ι : ℝ) * ∑ j : ι, CpartF j),
    le_max_of_le_left (mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun j _ => hCcompF_nn j))), fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set Acomp : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => ((crossRightLimitComponent (I := I) (M := M)
      g r s i α P :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hAcomp_def
  set Apart : TensorCompIdx (E := E) r s → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun P l => ((cutoffPartialLpLimit (I := I) (M := M)
      g r s i α P l :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hApart_def
  set Sumcomp : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s, eLpNorm (Acomp P) 2 μw with hSumcomp_def
  set Sumpart : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ l : Fin (Module.finrank ℝ E), eLpNorm (Apart P l) 2 μw with hSumpart_def
  set summandComp : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2)) y *
      Acomp j.2.1 y with hsummandComp_def
  set summandPart : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2) y *
      Apart j.2.1 j.1 y with hsummandPart_def
  set Ccomp : ℝ := ∑ j : ι, CcompF j with hCcomp_def
  set Cpart : ℝ := ∑ j : ι, CpartF j with hCpart_def
  have hCcomp_nn : 0 ≤ Ccomp :=
    Finset.sum_nonneg (fun j _ => hCcompF_nn j)
  have hCpart_nn : 0 ≤ Cpart :=
    Finset.sum_nonneg (fun j _ => hCpartF_nn j)
  have hCcomp : ∀ j : ι,
      eLpNorm (summandComp j) 2 μw ≤
        ENNReal.ofReal Ccomp * eLpNorm (Acomp j.2.1) 2 μw := by
    intro j
    refine le_trans (hCcompF j (Acomp j.2.1)) ?_
    gcongr
    rw [hCcomp_def]
    exact Finset.single_le_sum (fun k _ => hCcompF_nn k) (Finset.mem_univ j)
  have hCpart : ∀ j : ι,
      eLpNorm (summandPart j) 2 μw ≤
        ENNReal.ofReal Cpart * eLpNorm (Apart j.2.1 j.1) 2 μw := by
    intro j
    refine le_trans (hCpartF j (Apart j.2.1 j.1)) ?_
    gcongr
    rw [hCpart_def]
    exact Finset.single_le_sum (fun k _ => hCpartF_nn k) (Finset.mem_univ j)
  have hAcomp_meas : ∀ P : TensorCompIdx (E := E) r s,
      AEStronglyMeasurable (Acomp P) μw := by
    intro P
    rw [hAcomp_def, hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (Lp.aestronglyMeasurable _)
  have hApart_meas : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      AEStronglyMeasurable (Apart P l) μw := by
    intro P l
    rw [hApart_def, hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (Lp.aestronglyMeasurable _)
  have hsummandComp_meas : ∀ j, AEStronglyMeasurable (summandComp j) μw := by
    intro j
    rw [hsummandComp_def]
    refine AEStronglyMeasurable.mul ?_ (hAcomp_meas j.2.1)
    rw [hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (aestronglyMeasurable_indicator_mul (I := I) (M := M) α
        (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2))
  have hsummandPart_meas : ∀ j, AEStronglyMeasurable (summandPart j) μw := by
    intro j
    rw [hsummandPart_def]
    refine AEStronglyMeasurable.mul ?_ (hApart_meas j.2.1 j.1)
    rw [hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (aestronglyMeasurable_indicator_mul (I := I) (M := M) α
        (crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2))
  have h_funcA :
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (crossRightDivFactor (I := I) (M := M)
                      g r s α P₀ l P Q)) y *
                (crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandComp j := by
    funext y
    rw [Finset.sum_apply]
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_funcB :
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandPart j := by
    funext y
    rw [Finset.sum_apply]
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_triangle :
      eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀) 2 μw
        ≤ (∑ j : ι, eLpNorm (summandComp j) 2 μw)
          + (∑ j : ι, eLpNorm (summandPart j) 2 μw) := by
    have h_split : crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ =
        (∑ j : ι, summandComp j) + (∑ j : ι, summandPart j) := by
      rw [← h_funcA, ← h_funcB]
      rfl
    rw [h_split]
    refine le_trans (eLpNorm_add_le ?_ ?_ (by norm_num)) (add_le_add ?_ ?_)
    · exact Finset.aestronglyMeasurable_sum _ (fun j _ => hsummandComp_meas j)
    · exact Finset.aestronglyMeasurable_sum _ (fun j _ => hsummandPart_meas j)
    · exact eLpNorm_sum_le (fun j _ => hsummandComp_meas j) (by norm_num)
    · exact eLpNorm_sum_le (fun j _ => hsummandPart_meas j) (by norm_num)
  have h_groupA :
      (∑ j : ι, eLpNorm (summandComp j) 2 μw)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp := by
    have h_each : ∀ j : ι,
        eLpNorm (summandComp j) 2 μw ≤ ENNReal.ofReal Ccomp * Sumcomp := by
      intro j
      refine (hCcomp j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Ccomp))
      rw [hSumcomp_def]
      exact Finset.single_le_sum (f := fun P => eLpNorm (Acomp P) 2 μw)
        (fun P _ => zero_le _) (Finset.mem_univ j.2.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have h_groupB :
      (∑ j : ι, eLpNorm (summandPart j) 2 μw)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart := by
    have h_each : ∀ j : ι,
        eLpNorm (summandPart j) 2 μw ≤ ENNReal.ofReal Cpart * Sumpart := by
      intro j
      refine (hCpart j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Cpart))
      rw [hSumpart_def]
      refine le_trans ?_
        (Finset.single_le_sum (f := fun P => ∑ l : Fin (Module.finrank ℝ E),
          eLpNorm (Apart P l) 2 μw)
          (fun P _ => zero_le _) (Finset.mem_univ j.2.1))
      exact Finset.single_le_sum (f := fun l => eLpNorm (Apart j.2.1 l) 2 μw)
        (fun l _ => zero_le _) (Finset.mem_univ j.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have hCcomp_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hCpart_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2 μw
        ≤ (∑ j : ι, eLpNorm (summandComp j) 2 μw)
          + (∑ j : ι, eLpNorm (summandPart j) 2 μw) := h_triangle
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp
          + ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart :=
        add_le_add h_groupA h_groupB
    _ ≤ ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * Sumcomp
          + ENNReal.ofReal
              (max ((Fintype.card ι : ℝ) * Ccomp)
                ((Fintype.card ι : ℝ) * Cpart)) * Sumpart :=
        add_le_add (mul_le_mul_left hCcomp_le _)
          (mul_le_mul_left hCpart_le _)
    _ = ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * (Sumcomp + Sumpart) :=
        (mul_add _ _ _).symm

end MainBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
