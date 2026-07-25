import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.MemW1pResidualFull
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.H1ComplTendsto
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothApproxSeqIdentification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open DifferentialGeometry.Analysis.Laplacian.MemW1pFChartResidualFull
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqH1ComplTendsto
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_le_wkpNorm_one_two
    (u : EuclN → ℝ) (Ω : Set EuclN) :
    eLpNorm u 2 ((volume : Measure EuclN).restrict Ω) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2 u Ω := by
  classical
  have h_iter_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
        (d := Module.finrank ℝ E) (p := 2) 0 (fun i : Fin 0 => i.elim0) u Ω = u :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero
      (d := Module.finrank ℝ E) (p := 2) (fun i : Fin 0 => i.elim0) u Ω
  have h_zero_le :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
      (d := Module.finrank ℝ E) (k := 1) (p := 2) u Ω 0 (by norm_num : (0 : ℕ) ≤ 1)
      (fun i : Fin 0 => i.elim0)
  rw [h_iter_eq] at h_zero_le
  exact h_zero_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_tendsto_zero_of_wkpNorm_one_two_tendsto_zero
    {u : ℕ → EuclN → ℝ} {F_lim : EuclN → ℝ} {Ω : Set EuclN}
    (h_tendsto : Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => u n y - F_lim y) Ω)
      atTop (𝓝 0)) :
    Tendsto (fun n =>
      eLpNorm (fun y => u n y - F_lim y) 2
        ((volume : Measure EuclN).restrict Ω))
      atTop (𝓝 0) := by
  classical
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ => (0 : ℝ≥0∞)) (h := fun n =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => u n y - F_lim y) Ω)
    tendsto_const_nhds h_tendsto
    (fun _ => zero_le _)
    (fun n => eLpNorm_le_wkpNorm_one_two (fun y => u n y - F_lim y) Ω)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma volume_restrict_chartTarget_absolutelyContinuous_weighted
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro A hA
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
    at hA
  rw [Measure.restrict_apply' h_chartTarget_meas]
  rw [Measure.restrict_apply' h_chartTarget_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothFChartResidual_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (smoothFChartResidual (I := I) (M := M) g α v) μ := by
  unfold smoothFChartResidual fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartResidual_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h) μ := by
  unfold fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_subseq_ae_volume_restrict
    (g : SmoothRiemannianMetric I M) (α : M)
    {v : ℕ → SmoothScalar g} {F_lim : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F_lim
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (h_tendsto : Tendsto (fun n =>
      eLpNorm (fun y =>
          smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ n)) y) atTop
          (𝓝 (F_lim y)) := by
  classical
  have h_aesm_n : ∀ n, AEStronglyMeasurable
      (smoothFChartResidual (I := I) (M := M) g α (v n))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    smoothFChartResidual_aestronglyMeasurable (I := I) (M := M) g α (v n) _
  have h_tim : TendstoInMeasure
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      atTop F_lim :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      h_aesm_n hF_aesm h_tendsto
  exact h_tim.exists_seq_tendsto_ae

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_subseq_ae_weighted_restrict
    (g : SmoothRiemannianMetric I M) (α : M)
    {v : ℕ → SmoothScalar g} {F : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (h_tendsto : Tendsto (fun n =>
      eLpNorm (fun y =>
          smoothFChartResidual (I := I) (M := M) g α (v n) y - F y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ n)) y) atTop
          (𝓝 (F y)) := by
  classical
  have h_aesm_n : ∀ n, AEStronglyMeasurable
      (smoothFChartResidual (I := I) (M := M) g α (v n))
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    smoothFChartResidual_aestronglyMeasurable (I := I) (M := M) g α (v n) _
  have h_tim : TendstoInMeasure
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      atTop F :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      h_aesm_n hF_aesm h_tendsto
  exact h_tim.exists_seq_tendsto_ae

theorem smoothApproxSeq_smoothFChartResidual_limit_eq_fChartResidual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y =>
            smoothFChartResidual (I := I) (M := M) g α
              (smoothApproxSeq (I := I) (M := M) g hu_h n) y -
            F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h := by
  classical
  intro F_lim h_F_lim_w1p h_wkp_tendsto
  set v : ℕ → SmoothScalar g := fun n =>
    smoothApproxSeq (I := I) (M := M) g hu_h n with hv_def
  have hF_lim_memLp : MemLp F_lim 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_F_lim_w1p.1
  have hF_lim_aesm_volume : AEStronglyMeasurable F_lim
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hF_lim_memLp.aestronglyMeasurable
  have hF_res_aesm_weighted :
      AEStronglyMeasurable
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h)
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    fChartResidual_aestronglyMeasurable (I := I) (M := M) g α u_h _
  have h_eLpNorm_volume_tendsto :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    eLpNorm_tendsto_zero_of_wkpNorm_one_two_tendsto_zero
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      (F_lim := F_lim)
      (Ω := chartTargetEuclid (I := I) (M := M) α)
      h_wkp_tendsto
  have h_h1Compl_tendsto : Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h) :=
    smoothApproxSeq_tendsto_h1Compl (I := I) (M := M) g hu_h
  have h_eLpNorm_weighted_tendsto :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            smoothFChartResidual (I := I) (M := M) g α (v n) y -
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    smoothFChartResidual_tendsto_fChartResidual_lp_weighted
      (I := I) (M := M) g α v h_h1Compl_tendsto
  obtain ⟨σ, hσ_strict, hσ_ae⟩ :=
    exists_subseq_ae_volume_restrict (I := I) (M := M) g α
      (v := v) (F_lim := F_lim) hF_lim_aesm_volume h_eLpNorm_volume_tendsto
  have h_eLpNorm_weighted_subseq :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            smoothFChartResidual (I := I) (M := M) g α (v (σ n)) y -
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    h_eLpNorm_weighted_tendsto.comp hσ_strict.tendsto_atTop
  obtain ⟨τ, hτ_strict, hτ_ae⟩ :=
    exists_subseq_ae_weighted_restrict (I := I) (M := M) g α
      (v := fun n => v (σ n))
      (F := DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      hF_res_aesm_weighted h_eLpNorm_weighted_subseq
  have h_volume_ae_σ_τ :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ (τ n))) y) atTop
          (𝓝 (F_lim y)) := by
    filter_upwards [hσ_ae] with y hy
    exact hy.comp hτ_strict.tendsto_atTop
  have h_vol_abs : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
    volume_restrict_chartTarget_absolutelyContinuous_weighted
      (I := I) (M := M) g α
  have h_volume_ae_σ_τ_fChart :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ (τ n))) y) atTop
          (𝓝 ((DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h) y)) :=
    h_vol_abs.ae_le hτ_ae
  filter_upwards [h_volume_ae_σ_τ, h_volume_ae_σ_τ_fChart]
    with y h_to_Flim h_to_fChart
  exact tendsto_nhds_unique h_to_Flim h_to_fChart

end SmoothApproxSeqIdentification
end Laplacian
end Analysis
end DifferentialGeometry

end
