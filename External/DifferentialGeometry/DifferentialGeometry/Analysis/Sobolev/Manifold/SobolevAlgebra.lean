import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseLemmas
import DifferentialGeometry.Analysis.Sobolev.Manifold.SobolevAlgebraSmoothExtension
import DifferentialGeometry.Analysis.Sobolev.Manifold.SobolevAlgebraSmoothMultiplierWkpBound
import DifferentialGeometry.Analysis.Sobolev.Manifold.SobolevAlgebraChartSmoothFactors


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma chartPushed_mul_eq_smoothExtension_mul_chartPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y =
      smoothExtension (I := I) (M := M) α (fun x => b x * u x) y *
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hLHS :
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * (u x * v x) := rfl
  have hRHS1 : smoothExtension (I := I) (M := M) α (fun x => b x * u x) y =
      b x * u x := by
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α
      (fun x => b x * u x) hy]
  have hRHS2 : chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * v x := rfl
  rw [hLHS, hRHS1, hRHS2]
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

private lemma per_chart_mul_smooth_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ K_α : ℝ, 0 ≤ K_α ∧
      ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (fun x => u x * v x))
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K_α *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 p
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff (I := I) (M := M) α
  have hbu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => b x * u x) := hb_smooth.mul hu
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  obtain ⟨Cα, hCα_nn, hCα_bound⟩ :=
    smoothExtension_first_order_bound (I := I) (M := M) α hbu_smooth hbu_supp
  set η : EuclN → ℝ := smoothExtension (I := I) (M := M) α (fun x : M => b x * u x)
    with hη_def
  have hη_smooth : ContDiff ℝ ∞ η := by
    rw [hη_def]
    exact contDiff_smoothExtension (I := I) (M := M) α hbu_smooth hbu_supp
  have hη_smooth_top : ContDiff ℝ (⊤ : ℕ∞) η := hη_smooth
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hCα_on_Ω : ∀ j ≤ 1, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ j η y‖ ≤ Cα := fun j hj y _ =>
    hCα_bound j hj y
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      (d := Module.finrank ℝ E) (k := 1) (le_refl _) hp_one hp_top hΩ_open
      hη_smooth_top hCα_nn hCα_on_Ω
  refine ⟨K, hK_pos.le, ?_⟩
  intro v hv
  have h_factorize :
      (fun y : EuclN => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y)
        =ᵐ[volume.restrict Ω]
      (fun y : EuclN => η y *
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y) := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [hη_def]
    exact chartPushed_mul_eq_smoothExtension_mul_chartPushed
      (I := I) (M := M) α (b := b) (u := u) (v := v) hb_one_on_tsupp hy
  have hv_chartPushed_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v) Ω := by
    have h := DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_one hv
    exact h α
  have h_eucl_bound :=
    hK_bound (u := chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
      hv_chartPushed_mem
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one hΩ_open h_factorize]
  exact h_eucl_bound

theorem mul_smooth_chart_bound_C1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∃ Cu : ℝ, 0 ≤ Cu ∧
        ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
          wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p)
              (fun x => u x * v x) ≤
            ENNReal.ofReal Cu *
              wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  intro u hu
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : (1 : ℝ) ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : ENNReal.ofReal p ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  set S : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hS_def
  have h_per_α : ∀ α ∈ S, ∃ K_α : ℝ, 0 ≤ K_α ∧
      ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (fun x => u x * v x))
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K_α *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
              (chartTargetEuclid (I := I) (M := M) α) := fun α _ =>
    per_chart_mul_smooth_bound (I := I) (M := M) g hp_enn_one hp_enn_top α hu
  set Kfun : M → ℝ := fun α =>
    if hα : α ∈ S then Classical.choose (h_per_α α hα) else 0 with hKfun_def
  have hKfun_eq_of_mem : ∀ α (hα : α ∈ S), Kfun α = Classical.choose (h_per_α α hα) := by
    intro α hα
    change (if hα' : α ∈ S then Classical.choose (h_per_α α hα') else 0) =
      Classical.choose (h_per_α α hα)
    rw [dif_pos hα]
  have hKfun_nn : ∀ α ∈ S, 0 ≤ Kfun α := by
    intro α hα
    rw [hKfun_eq_of_mem α hα]
    exact (Classical.choose_spec (h_per_α α hα)).1
  have hKfun_bound : ∀ α ∈ S, ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => u x * v x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (Kfun α) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro α hα v hv
    have hbnd := (Classical.choose_spec (h_per_α α hα)).2 hv
    rw [hKfun_eq_of_mem α hα]
    exact hbnd
  refine ⟨∑ α ∈ S, Kfun α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α hα => hKfun_nn α hα)
  intro v hv
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one (fun x => u x * v x),
    wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one v]
  refine (Finset.sum_le_sum (fun α hα => hKfun_bound α hα hv)).trans ?_
  set sumK : ℝ := ∑ α ∈ S, Kfun α with hsumK_def
  have hKfun_sum_le : ∀ α ∈ S, ENNReal.ofReal (Kfun α) ≤ ENNReal.ofReal sumK := by
    intro α hα
    apply ENNReal.ofReal_le_ofReal
    rw [hsumK_def]
    exact Finset.single_le_sum (f := Kfun) (fun β hβ => hKfun_nn β hβ) hα
  have h_step1 : (∑ α ∈ S,
      ENNReal.ofReal (Kfun α) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑ α ∈ S,
          ENNReal.ofReal sumK *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
              (chartTargetEuclid (I := I) (M := M) α) := by
    refine Finset.sum_le_sum (fun α hα => ?_)
    exact mul_le_mul' (hKfun_sum_le α hα) (le_refl _)
  refine h_step1.trans ?_
  rw [← Finset.mul_sum]

omit [FiniteDimensional ℝ E] in
private lemma eLpNorm_restrict_le_ofReal_mul_volume_pow
    {p : ℝ≥0∞} {Ω : Set EuclN}
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    {f : EuclN → ℝ} {C : ℝ} (hC_nn : 0 ≤ C)
    (h_supp : ∀ y, y ∉ K → f y = 0)
    (h_bound : ∀ y, ‖f y‖ ≤ C) :
    eLpNorm f p (volume.restrict Ω) ≤
      ENNReal.ofReal C * (volume K) ^ (1 / p.toReal) := by
  classical
  have h_pointwise : ∀ y, ‖f y‖ ≤ ‖K.indicator (fun _ : EuclN => C) y‖ := by
    intro y
    by_cases hy : y ∈ K
    · have h_ind : K.indicator (fun _ : EuclN => C) y = C := Set.indicator_of_mem hy _
      rw [h_ind]
      have : ‖C‖ = C := by rw [Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [this]
      exact h_bound y
    · have h_ind : K.indicator (fun _ : EuclN => C) y = 0 := Set.indicator_of_notMem hy _
      rw [h_supp y hy, h_ind, norm_zero]
  have h_ae : ∀ᵐ y ∂(volume.restrict Ω),
      ‖f y‖ ≤ ‖K.indicator (fun _ : EuclN => C) y‖ :=
    Filter.Eventually.of_forall h_pointwise
  refine (eLpNorm_mono_ae h_ae).trans ?_
  have h_indicator_bd : eLpNorm (K.indicator (fun _ : EuclN => C)) p (volume.restrict Ω) ≤
      ‖C‖ₑ * (volume.restrict Ω) K ^ (1 / p.toReal) :=
    eLpNorm_indicator_const_le (μ := volume.restrict Ω) (s := K) (c := C) (p := p)
  refine h_indicator_bd.trans ?_
  have h_meas_le : (volume.restrict Ω) K ≤ volume K := by
    rw [Measure.restrict_apply hK_meas]
    exact measure_mono Set.inter_subset_left
  refine mul_le_mul' ?_ ?_
  · rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_nn]
  · exact ENNReal.rpow_le_rpow h_meas_le (by positivity)

private lemma eLpNorm_Eu_dR_Ev_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_le_one : ∀ x : M, 0 ≤ b x ∧ b x ≤ 1)
    {uMax vMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax)
    (hv_bound : ∀ x : M, ‖v x‖ ≤ vMax) (hvMax_nn : 0 ≤ vMax)
    {C_R : ℝ} (hC_R_nn : 0 ≤ C_R)
    (hC_R_bound : ∀ y : EuclN, ‖fderiv ℝ (liftedPou (I := I) (M := M) α) y‖ ≤ C_R)
    (i : Fin (Module.finrank ℝ E)) {p : ℝ≥0∞} :
    eLpNorm (fun y : EuclN => leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y) p
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
    ENNReal.ofReal (uMax * vMax * C_R) *
      (volume (chartCarrierLocal (I := I) (M := M) α)) ^ (1 / p.toReal) := by
  classical
  set K_α : Set EuclN := chartCarrierLocal (I := I) (M := M) α
  have hK_compact : IsCompact K_α := chartCarrierLocal_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K_α := hK_compact.isClosed.measurableSet
  have hC_nn : 0 ≤ uMax * vMax * C_R :=
    mul_nonneg (mul_nonneg huMax_nn hvMax_nn) hC_R_nn
  have h_R_supp_in_K : tsupport (liftedPou (I := I) (M := M) α) ⊆ K_α :=
    tsupport_liftedPou_subset_chartCarrierLocal (I := I) (M := M) α
  have h_supp : ∀ y : EuclN, y ∉ K_α →
      leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y = 0 := by
    intro y hy_off
    have h_R_zero_nhd : ∀ᶠ z in nhds y, liftedPou (I := I) (M := M) α z = 0 := by
      have h_compl_open : IsOpen (tsupport (liftedPou (I := I) (M := M) α))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hy_off_R_supp : y ∉ tsupport (liftedPou (I := I) (M := M) α) :=
        fun h => hy_off (h_R_supp_in_K h)
      filter_upwards [h_compl_open.mem_nhds hy_off_R_supp] with z hz
      have hz_off_supp : z ∉ Function.support (liftedPou (I := I) (M := M) α) :=
        fun h_supp_z => hz (subset_tsupport _ h_supp_z)
      simpa using hz_off_supp
    have h_fderiv_zero : fderiv ℝ (liftedPou (I := I) (M := M) α) y = 0 := by
      have h_eq : liftedPou (I := I) (M := M) α =ᶠ[nhds y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_R_zero_nhd] with z hz
        exact hz
      rw [Filter.EventuallyEq.fderiv_eq h_eq]
      exact fderiv_const_apply (0 : ℝ)
    rw [h_fderiv_zero]
    simp
  have h_bound : ∀ y : EuclN,
      ‖leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y‖ ≤ uMax * vMax * C_R := by
    intro y
    have hEu_bd := leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α
      hb_le_one hu_bound huMax_nn y
    have hEv_bd := leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α
      hb_le_one hv_bound hvMax_nn y
    have h_dR_bd : ‖(fderiv ℝ (liftedPou (I := I) (M := M) α) y)
        (EuclideanSpace.single i (1 : ℝ))‖ ≤ C_R := by
      have h := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y)
        (EuclideanSpace.single i (1 : ℝ))
      have h_one : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
      rw [h_one, mul_one] at h
      exact h.trans (hC_R_bound y)
    calc
      ‖leftSmoothFactor (I := I) (M := M) α b u y *
        (fderiv ℝ (liftedPou (I := I) (M := M) α) y) (EuclideanSpace.single i (1 : ℝ)) *
        leftSmoothFactor (I := I) (M := M) α b v y‖
        = ‖leftSmoothFactor (I := I) (M := M) α b u y‖ *
          ‖(fderiv ℝ (liftedPou (I := I) (M := M) α) y)
            (EuclideanSpace.single i (1 : ℝ))‖ *
          ‖leftSmoothFactor (I := I) (M := M) α b v y‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ uMax * C_R * vMax := by gcongr
      _ = uMax * vMax * C_R := by ring
  exact eLpNorm_restrict_le_ofReal_mul_volume_pow hK_meas hC_nn h_supp h_bound

private lemma per_chart_bilinear_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ (⊤ : ℝ≥0∞)) (α : M) :
    ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 p
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
                (fun x => u x * v x))
              (chartTargetEuclid (I := I) (M := M) α) ≤
            ENNReal.ofReal vMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) 1 p
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal uMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) 1 p
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal (Bα * uMax * vMax) := by
  classical
  obtain ⟨b, hb_smooth, hb_range, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff_with_data (I := I) (M := M) α
  have hb_le_one : ∀ x : M, 0 ≤ b x ∧ b x ≤ 1 := hb_range
  obtain ⟨C_R, hC_R_nn, hC_R_bound⟩ :=
    exists_liftedPou_grad_bound (I := I) (M := M) α
  set d : ℕ := Module.finrank ℝ E with hd_def
  set vol_K : ℝ≥0∞ := volume (chartCarrierLocal (I := I) (M := M) α) with hvolK_def
  have hK_compact : IsCompact (chartCarrierLocal (I := I) (M := M) α) :=
    chartCarrierLocal_isCompact (I := I) (M := M) α
  have hvolK_finite : vol_K < ⊤ := hK_compact.measure_lt_top
  have hvolK_ne_top : vol_K ≠ ⊤ := hvolK_finite.ne
  set vol_K_pow : ℝ := (vol_K.toReal) ^ (1 / p.toReal) with hvolK_pow_def
  have hvolK_pow_nn : 0 ≤ vol_K_pow := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set Bα : ℝ := (d : ℝ) * C_R * vol_K_pow with hBα_def
  have hd_real_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hBα_nn : 0 ≤ Bα :=
    mul_nonneg (mul_nonneg hd_real_nn hC_R_nn) hvolK_pow_nn
  refine ⟨Bα, hBα_nn, ?_⟩
  intro u v hu hv uMax vMax huMax_nn hvMax_nn hu_bound hv_bound
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set Pu := smoothPushed (I := I) (M := M) α u
  set Pv := smoothPushed (I := I) (M := M) α v
  set Eu := leftSmoothFactor (I := I) (M := M) α b u
  set Ev := leftSmoothFactor (I := I) (M := M) α b v
  set R := liftedPou (I := I) (M := M) α
  have h_chartPushed_uv_eq : (fun y : EuclN => chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
      (fun x => u x * v x) y) =ᵐ[volume.restrict Ω]
      fun y : EuclN => Pu y * Ev y := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have h1 : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y =
      smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) y := by
      classical
      rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
      unfold chartPushed
      ring
    have h2 := smoothPushed_mul_leftSmoothFactor_eq_smoothExtension_uv (I := I) (M := M)
      α (b := b) (u := u) (v := v) hb_one_on_tsupp
    have h2' : smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) y = Pu y * Ev y := by
      have hh := congrFun h2 y
      simp only at hh
      exact hh.symm
    exact h1.trans h2'
  have h_chartPushed_u_eq_Pu : (fun y : EuclN => chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y) =ᵐ[volume.restrict Ω]
      fun y => Pu y := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    classical
    change chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y =
      smoothExtension (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) y
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
    rfl
  have h_chartPushed_v_eq_Pv : (fun y : EuclN => chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y) =ᵐ[volume.restrict Ω]
      fun y => Pv y := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    classical
    change chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v y =
      smoothExtension (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x) y
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
    rfl
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := d) hp_one hΩ_open h_chartPushed_uv_eq,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := d) hp_one hΩ_open h_chartPushed_u_eq_Pu,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := d) hp_one hΩ_open h_chartPushed_v_eq_Pv]
  letI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_succ_eq
        (d := d) 0 p (fun y => Pu y * Ev y) Ω,
      DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_succ_eq
        (d := d) 0 p Pu Ω,
      DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_succ_eq
        (d := d) 0 p Pv Ω]
  simp_rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero
    (d := d) p _ Ω]
  set ePu : ℝ≥0∞ := eLpNorm Pu p (volume.restrict Ω) with hePu_def
  set ePv : ℝ≥0∞ := eLpNorm Pv p (volume.restrict Ω) with hePv_def
  set gPu : Fin d → ℝ≥0∞ := fun i => eLpNorm
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := d) p i Pu Ω) p (volume.restrict Ω) with hgPu_def
  set gPv : Fin d → ℝ≥0∞ := fun i => eLpNorm
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := d) p i Pv Ω) p (volume.restrict Ω) with hgPv_def
  set vMax_e : ℝ≥0∞ := ENNReal.ofReal vMax with hvMax_e_def
  set uMax_e : ℝ≥0∞ := ENNReal.ofReal uMax with huMax_e_def
  have h_Pu_bound : ∀ y, ‖Pu y‖ ≤ uMax := smoothPushed_norm_le_of_bound
    (I := I) (M := M) α hu_bound huMax_nn
  have h_Pv_bound : ∀ y, ‖Pv y‖ ≤ vMax := smoothPushed_norm_le_of_bound
    (I := I) (M := M) α hv_bound hvMax_nn
  have h_Eu_bound : ∀ y, ‖Eu y‖ ≤ uMax :=
    leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α hb_le_one hu_bound huMax_nn
  have h_Ev_bound : ∀ y, ‖Ev y‖ ≤ vMax :=
    leftSmoothFactor_norm_le_of_bound (I := I) (M := M) α hb_le_one hv_bound hvMax_nn
  have h_Lp_bound : eLpNorm (fun y => Pu y * Ev y) p (volume.restrict Ω) ≤
      vMax_e * ePu := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := Pu) (c := vMax) ?_ p
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall (fun y _ => ?_)
    calc
      ‖Pu y * Ev y‖ = ‖Ev y‖ * ‖Pu y‖ := by rw [norm_mul, mul_comm]
      _ ≤ vMax * ‖Pu y‖ := by gcongr; exact h_Ev_bound y
  have h_grad_bound : ∀ i : Fin d,
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i (fun y => Pu y * Ev y) Ω) p (volume.restrict Ω) ≤
        vMax_e * gPu i + uMax_e * gPv i +
          ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by
    intro i
    have hPu_smooth : ContDiff ℝ (⊤ : ℕ∞) Pu := smoothPushed_smooth (I := I) (M := M) α hu
    obtain ⟨Cu0, hCu0_nn, hCu0_bd⟩ := iteratedFDeriv_bound_of_compactSupport
      hPu_smooth (smoothPushed_hasCompactSupport (I := I) (M := M) α u) 0
    obtain ⟨Cu1, hCu1_nn, hCu1_bd⟩ := iteratedFDeriv_bound_of_compactSupport
      hPu_smooth (smoothPushed_hasCompactSupport (I := I) (M := M) α u) 1
    set Cu := max Cu0 Cu1
    have hCu_nn : 0 ≤ Cu := le_max_of_le_left hCu0_nn
    have hPu_bd_C : ∀ y ∈ Ω, ‖Pu y‖ ≤ Cu := fun y _ => by
      have h := hCu0_bd y; rw [norm_iteratedFDeriv_zero] at h
      exact h.trans (le_max_left _ _)
    have hPu_grad_bd_C : ∀ y ∈ Ω, ‖fderiv ℝ Pu y‖ ≤ Cu := fun y _ => by
      have h := hCu1_bd y; rw [norm_iteratedFDeriv_one] at h
      exact h.trans (le_max_right _ _)
    have hEv_mem : DeGiorgi.MemW1p (d := d) p Ev Ω :=
      leftSmoothFactor_memW1p (I := I) (M := M) α hb_smooth hv hb_supp hp_one
    have h_PuEv_ae := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_smul_smooth_bounded_ae
      (d := d) hp_one hΩ_open hPu_smooth hPu_bd_C hPu_grad_bd_C hEv_mem i
    have hR_smooth : ContDiff ℝ (⊤ : ℕ∞) R := liftedPou_smooth (I := I) (M := M) α
    have hR_bd : ∀ y ∈ Ω, ‖R y‖ ≤ max 1 C_R := fun y _ =>
      (liftedPou_norm_le_one (I := I) (M := M) α y).trans (le_max_left _ _)
    have hR_grad_bd : ∀ y ∈ Ω, ‖fderiv ℝ R y‖ ≤ max 1 C_R := fun y _ =>
      (hC_R_bound y).trans (le_max_right _ _)
    have h_REv_ae := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_smul_smooth_bounded_ae
      (d := d) hp_one hΩ_open hR_smooth hR_bd hR_grad_bd hEv_mem i
    have h_R_Ev_eq_Pv : (fun y : EuclN => R y * Ev y) = Pv :=
      liftedPou_mul_leftSmoothFactor_eq_smoothPushed (I := I) (M := M)
        α (b := b) (v := v) hb_one_on_tsupp
    have h_chosen_Pv_eq : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i Pv Ω =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i (fun y => R y * Ev y) Ω := by
      rw [h_R_Ev_eq_Pv]
    have h_Pv_ae : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i Pv Ω
      =ᵐ[volume.restrict Ω]
      (fun y => R y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Ev Ω y +
        (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y) := by
      rw [h_chosen_Pv_eq]
      exact h_REv_ae
    have h_Pu_eq_R_Eu : (fun y : EuclN => R y * Eu y) = Pu :=
      liftedPou_mul_leftSmoothFactor_eq_smoothPushed (I := I) (M := M)
        α (b := b) (v := u) hb_one_on_tsupp
    have h_combined : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := d) p i (fun y => Pu y * Ev y) Ω
      =ᵐ[volume.restrict Ω]
      (fun y => Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω y -
        Eu y * (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y +
        (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y) := by
      filter_upwards [h_PuEv_ae, h_Pv_ae] with y hy1 hy2
      have hPu_y : Pu y = R y * Eu y := by
        have := congrFun h_Pu_eq_R_Eu y
        exact this.symm
      rw [hy1, hPu_y]
      have h_eq_R_Ev :
          R y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Ev Ω y =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pv Ω y -
            (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y := by
        linarith
      have h_factor :
          R y * Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Ev Ω y =
            Eu y * (R y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Ev Ω y) := by ring
      rw [h_factor, h_eq_R_Ev]
      ring
    rw [eLpNorm_congr_ae h_combined]
    set f1 : EuclN → ℝ := fun y => Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := d) p i Pv Ω y with hf1_def
    set f2 : EuclN → ℝ := fun y => Eu y * (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y
      with hf2_def
    set f3 : EuclN → ℝ := fun y => (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y
      with hf3_def
    have h_Eu_cont : Continuous Eu :=
      (leftSmoothFactor_smooth (I := I) (M := M) α hb_smooth hu hb_supp).continuous
    have h_Ev_cont : Continuous Ev :=
      (leftSmoothFactor_smooth (I := I) (M := M) α hb_smooth hv hb_supp).continuous
    have h_dR_cont : Continuous
        (fun y : EuclN => (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ))) :=
      (hR_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have h_dPu_cont : Continuous
        (fun y : EuclN => (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ))) :=
      (hPu_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have h_chosen_cont_AESM : AEStronglyMeasurable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω)
        (volume.restrict Ω) := by
      have hPv_W1p : DeGiorgi.MemW1p (d := d) p Pv Ω :=
        smoothPushed_memW1p (I := I) (M := M) α hv hp_one
      exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        hPv_W1p i).aestronglyMeasurable
    have h_AESM_f1 : AEStronglyMeasurable f1 (volume.restrict Ω) :=
      h_Eu_cont.aestronglyMeasurable.mul h_chosen_cont_AESM
    have h_AESM_f2 : AEStronglyMeasurable f2 (volume.restrict Ω) :=
      (h_Eu_cont.mul h_dR_cont).aestronglyMeasurable.mul h_Ev_cont.aestronglyMeasurable
    have h_AESM_f3 : AEStronglyMeasurable f3 (volume.restrict Ω) :=
      h_dPu_cont.aestronglyMeasurable.mul h_Ev_cont.aestronglyMeasurable
    have h_eq_pointwise :
        (fun y => Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pv Ω y -
          Eu y * (fderiv ℝ R y) (EuclideanSpace.single i (1 : ℝ)) * Ev y +
          (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y) =
        fun y => f1 y + (-f2 y) + f3 y := by
      funext y
      show _ = _
      ring
    rw [h_eq_pointwise]
    have h_AESM_neg_f2 : AEStronglyMeasurable (fun y => -f2 y) (volume.restrict Ω) := by
      have : AEStronglyMeasurable (-f2) (volume.restrict Ω) := h_AESM_f2.neg
      exact this
    have h_AESM_f1_neg_f2 : AEStronglyMeasurable (fun y => f1 y + -f2 y) (volume.restrict Ω) := by
      have : AEStronglyMeasurable (f1 + -f2) (volume.restrict Ω) := h_AESM_f1.add h_AESM_f2.neg
      exact this
    have h_addLR : (fun y => f1 y + -f2 y + f3 y) = (fun y => f1 y + -f2 y) + f3 := by
      funext y
      show _ = _
      rfl
    rw [h_addLR]
    refine (eLpNorm_add_le h_AESM_f1_neg_f2 h_AESM_f3 hp_one).trans ?_
    have h_addLR2 : (fun y => f1 y + -f2 y) = f1 + (-f2) := by
      funext y; rfl
    have h_tri_2 : eLpNorm (fun y => f1 y + -f2 y) p (volume.restrict Ω) ≤
        eLpNorm f1 p (volume.restrict Ω) + eLpNorm f2 p (volume.restrict Ω) := by
      rw [h_addLR2]
      have h := eLpNorm_add_le h_AESM_f1 h_AESM_f2.neg hp_one
      rwa [eLpNorm_neg] at h
    refine (add_le_add h_tri_2 (le_refl (eLpNorm f3 p (volume.restrict Ω)))).trans ?_
    have h_f1_bd : eLpNorm f1 p (volume.restrict Ω) ≤ uMax_e * gPv i := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (g := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω)
        (c := uMax) ?_ p
      refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y _ => ?_)
      change ‖Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pv Ω y‖ ≤ uMax * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pv Ω y‖
      calc
        ‖Eu y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pv Ω y‖
          = ‖Eu y‖ * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pv Ω y‖ := norm_mul _ _
        _ ≤ uMax * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pv Ω y‖ := by gcongr; exact h_Eu_bound y
    have h_f2_bd : eLpNorm f2 p (volume.restrict Ω) ≤
        ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by
      exact eLpNorm_Eu_dR_Ev_bound (I := I) (M := M) α hb_le_one
        hu_bound huMax_nn hv_bound hvMax_nn hC_R_nn hC_R_bound i
    have h_f3_bd : eLpNorm f3 p (volume.restrict Ω) ≤ vMax_e * gPu i := by
      have h_classical_eq_chosen :
          (fun y : EuclN => (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)))
          =ᵐ[volume.restrict Ω]
          DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω := by
        have hPu_compact : HasCompactSupport Pu :=
          smoothPushed_hasCompactSupport (I := I) (M := M) α u
        have hPu_tsupp : tsupport Pu ⊆ Ω :=
          tsupport_smoothPushed_subset_chartTarget (I := I) (M := M) α u
        exact chosenWeakPartial_eq_classical_ae hp_one hΩ_open
          hPu_smooth hPu_compact hPu_tsupp i
      have h_f3_ae : f3 =ᵐ[volume.restrict Ω]
          (fun y => Ev y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω y) := by
        filter_upwards [h_classical_eq_chosen] with y hy
        change (fderiv ℝ Pu y) (EuclideanSpace.single i (1 : ℝ)) * Ev y =
          Ev y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω y
        rw [hy]
        ring
      rw [eLpNorm_congr_ae h_f3_ae]
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (g := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := d) p i Pu Ω)
        (c := vMax) ?_ p
      refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y _ => ?_)
      calc
        ‖Ev y * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := d) p i Pu Ω y‖
          = ‖Ev y‖ * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pu Ω y‖ := norm_mul _ _
        _ ≤ vMax * ‖DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := d) p i Pu Ω y‖ := by gcongr; exact h_Ev_bound y
    calc
      eLpNorm f1 p (volume.restrict Ω) +
        eLpNorm f2 p (volume.restrict Ω) +
        eLpNorm f3 p (volume.restrict Ω)
        ≤ uMax_e * gPv i +
          ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) +
          vMax_e * gPu i := by gcongr
      _ = vMax_e * gPu i + uMax_e * gPv i +
          ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by ring
  refine (add_le_add h_Lp_bound (Finset.sum_le_sum (fun i _ => h_grad_bound i))).trans ?_
  have h_sum_split :
      ∑ i : Fin d, (vMax_e * gPu i + uMax_e * gPv i +
        ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)) =
      (∑ i : Fin d, vMax_e * gPu i) + (∑ i : Fin d, uMax_e * gPv i) +
        ∑ _i : Fin d, ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [h_sum_split]
  rw [show (∑ i : Fin d, vMax_e * gPu i) = vMax_e * ∑ i : Fin d, gPu i from
        (Finset.mul_sum _ _ _).symm,
      show (∑ i : Fin d, uMax_e * gPv i) = uMax_e * ∑ i : Fin d, gPv i from
        (Finset.mul_sum _ _ _).symm]
  rw [show ∑ _i : Fin d, ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal) =
        (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  rw [mul_add vMax_e ePu (∑ i, gPu i), mul_add uMax_e ePv (∑ i, gPv i)]
  have h_const_bound : (d : ℝ≥0∞) *
      (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)) ≤
      ENNReal.ofReal (Bα * uMax * vMax) := by
    have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := (ENNReal.ofReal_natCast _).symm
    have hvol_pow_eq : vol_K ^ (1 / p.toReal) = ENNReal.ofReal vol_K_pow := by
      have h_eq1 : vol_K = ENNReal.ofReal vol_K.toReal :=
        (ENNReal.ofReal_toReal hvolK_ne_top).symm
      have h_inv : 0 ≤ (1 : ℝ) / p.toReal := by positivity
      have h_rpow : (ENNReal.ofReal vol_K.toReal) ^ (1 / p.toReal) =
          ENNReal.ofReal (vol_K.toReal ^ (1 / p.toReal)) :=
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg h_inv
      rw [h_eq1, h_rpow, hvolK_pow_def]
    have h_uvCR_nn : 0 ≤ uMax * vMax * C_R := by positivity
    have h_uvCR_volK_nn : 0 ≤ (uMax * vMax * C_R) * vol_K_pow :=
      mul_nonneg h_uvCR_nn hvolK_pow_nn
    have hBα_eq : Bα * uMax * vMax = (d : ℝ) * ((uMax * vMax * C_R) * vol_K_pow) := by
      rw [hBα_def]; ring
    have h_eq : (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal))
        = ENNReal.ofReal (Bα * uMax * vMax) := by
      calc (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal))
          = ENNReal.ofReal (d : ℝ) *
              (ENNReal.ofReal (uMax * vMax * C_R) * ENNReal.ofReal vol_K_pow) := by
            rw [hd_eq, hvol_pow_eq]
        _ = ENNReal.ofReal (d : ℝ) * ENNReal.ofReal ((uMax * vMax * C_R) * vol_K_pow) := by
            rw [ENNReal.ofReal_mul h_uvCR_nn]
        _ = ENNReal.ofReal ((d : ℝ) * ((uMax * vMax * C_R) * vol_K_pow)) := by
            rw [← ENNReal.ofReal_mul hd_real_nn]
        _ = ENNReal.ofReal (Bα * uMax * vMax) := by
            rw [← hBα_eq]
    rw [h_eq]
  calc
    vMax_e * ePu + (vMax_e * ∑ i : Fin d, gPu i + uMax_e * ∑ i : Fin d, gPv i +
      (d : ℝ≥0∞) * (ENNReal.ofReal (uMax * vMax * C_R) * vol_K ^ (1 / p.toReal)))
      ≤ vMax_e * ePu + (vMax_e * ∑ i, gPu i + uMax_e * ∑ i, gPv i +
        ENNReal.ofReal (Bα * uMax * vMax)) := by gcongr
    _ = (vMax_e * ePu + vMax_e * ∑ i, gPu i) + uMax_e * ∑ i, gPv i +
          ENNReal.ofReal (Bα * uMax * vMax) := by ring
    _ ≤ (vMax_e * ePu + vMax_e * ∑ i, gPu i) + (uMax_e * ePv + uMax_e * ∑ i, gPv i) +
          ENNReal.ofReal (Bα * uMax * vMax) := by
        gcongr
        exact le_add_self

private lemma mul_smooth_chart_bound_explicit_form
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p)
              (fun x => u x * v x) ≤
            ENNReal.ofReal vMax *
              wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u +
            ENNReal.ofReal uMax *
              wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v +
            ENNReal.ofReal (B * uMax * vMax) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : (1 : ℝ) ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : ENNReal.ofReal p ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  set S : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hS_def
  have h_per_α : ∀ α ∈ S, ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
                (fun x => u x * v x))
              (chartTargetEuclid (I := I) (M := M) α) ≤
            ENNReal.ofReal vMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal uMax *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
                (chartTargetEuclid (I := I) (M := M) α) +
            ENNReal.ofReal (Bα * uMax * vMax) := fun α _ =>
    per_chart_bilinear_bound (I := I) (M := M) hp_enn_one hp_enn_top α
  set Bfun : M → ℝ := fun α =>
    if hα : α ∈ S then Classical.choose (h_per_α α hα) else 0 with hBfun_def
  have hBfun_eq_of_mem : ∀ α (hα : α ∈ S), Bfun α = Classical.choose (h_per_α α hα) := by
    intro α hα
    change (if hα' : α ∈ S then Classical.choose (h_per_α α hα') else 0) =
      Classical.choose (h_per_α α hα)
    rw [dif_pos hα]
  have hBfun_nn : ∀ α ∈ S, 0 ≤ Bfun α := by
    intro α hα
    rw [hBfun_eq_of_mem α hα]
    exact (Classical.choose_spec (h_per_α α hα)).1
  refine ⟨∑ α ∈ S, Bfun α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α hα => hBfun_nn α hα)
  intro u v hu hv uMax vMax huMax_nn hvMax_nn hu_bound hv_bound
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one (fun x => u x * v x),
      wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one u,
      wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_enn_one v]
  have hBfun_bound : ∀ α ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => u x * v x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal vMax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) +
        ENNReal.ofReal uMax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
            (chartTargetEuclid (I := I) (M := M) α) +
        ENNReal.ofReal (Bfun α * uMax * vMax) := by
    intro α hα
    rw [hBfun_eq_of_mem α hα]
    exact (Classical.choose_spec (h_per_α α hα)).2 hu hv huMax_nn hvMax_nn hu_bound hv_bound
  refine (Finset.sum_le_sum (fun α hα => hBfun_bound α hα)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  set X : M → ℝ≥0∞ := fun α => DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
    (chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
    (chartTargetEuclid (I := I) (M := M) α) with hX_def
  set Y : M → ℝ≥0∞ := fun α => DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
    (chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v)
    (chartTargetEuclid (I := I) (M := M) α) with hY_def
  rw [show (∑ α ∈ S, ENNReal.ofReal vMax * X α) = ENNReal.ofReal vMax * ∑ α ∈ S, X α from
        (Finset.mul_sum _ _ _).symm,
      show (∑ α ∈ S, ENNReal.ofReal uMax * Y α) = ENNReal.ofReal uMax * ∑ α ∈ S, Y α from
        (Finset.mul_sum _ _ _).symm]
  refine add_le_add (le_refl _) ?_
  have h_sum_ofReal : ∑ α ∈ S, ENNReal.ofReal (Bfun α * uMax * vMax) =
      ENNReal.ofReal (∑ α ∈ S, Bfun α * uMax * vMax) := by
    refine (ENNReal.ofReal_sum_of_nonneg ?_).symm
    intro α hα
    have h := mul_nonneg (mul_nonneg (hBfun_nn α hα) huMax_nn) hvMax_nn
    exact h
  rw [h_sum_ofReal]
  have h_factor : ∑ α ∈ S, Bfun α * uMax * vMax = (∑ α ∈ S, Bfun α) * uMax * vMax := by
    rw [show (∑ α ∈ S, Bfun α * uMax * vMax) = ∑ α ∈ S, Bfun α * (uMax * vMax) from
      Finset.sum_congr rfl (fun α _ => by ring),
      ← Finset.sum_mul]
    ring
  rw [h_factor]

theorem mul_smooth_chart_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u v : M → ℝ},
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) (fun x => u x * v x) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u *
            wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨B, hB_nn, hB_bound⟩ :=
    mul_smooth_chart_bound_explicit_form (I := I) (M := M) g hp
  obtain ⟨M_M, hM_M_nn, hM_M_bound⟩ :=
    smooth_manifold_morrey_sup_bound_uniform (I := I) (M := M) g hp
  set C : ℝ := 2 * M_M + B * M_M ^ 2 with hC_def
  have hC_nn : 0 ≤ C := by
    have h1 : 0 ≤ 2 * M_M := mul_nonneg (by norm_num) hM_M_nn
    have h2 : 0 ≤ B * M_M ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
    linarith
  refine ⟨C, hC_nn, ?_⟩
  intro u v hu hv
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : (1 : ℝ) ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set NU : ℝ≥0∞ := wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u with hNU_def
  set NV : ℝ≥0∞ := wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) v with hNV_def
  have hNU_lt : NU < ⊤ := wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_enn_one
    (DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_enn_one hu)
  have hNV_lt : NV < ⊤ := wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_enn_one
    (DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_enn_one hv)
  have hNU_ne_top : NU ≠ ⊤ := hNU_lt.ne
  have hNV_ne_top : NV ≠ ⊤ := hNV_lt.ne
  set uMax : ℝ := M_M * NU.toReal with huMax_def
  set vMax : ℝ := M_M * NV.toReal with hvMax_def
  have huMax_nn : 0 ≤ uMax := mul_nonneg hM_M_nn ENNReal.toReal_nonneg
  have hvMax_nn : 0 ≤ vMax := mul_nonneg hM_M_nn ENNReal.toReal_nonneg
  have hu_bound : ∀ x : M, ‖u x‖ ≤ uMax := fun x => hM_M_bound hu x
  have hv_bound : ∀ x : M, ‖v x‖ ≤ vMax := fun x => hM_M_bound hv x
  have h_explicit := hB_bound hu hv huMax_nn hvMax_nn hu_bound hv_bound
  refine h_explicit.trans ?_
  have h_ofReal_vMax : ENNReal.ofReal vMax = ENNReal.ofReal M_M * NV := by
    rw [hvMax_def]
    rw [ENNReal.ofReal_mul hM_M_nn, ENNReal.ofReal_toReal hNV_ne_top]
  have h_ofReal_uMax : ENNReal.ofReal uMax = ENNReal.ofReal M_M * NU := by
    rw [huMax_def]
    rw [ENNReal.ofReal_mul hM_M_nn, ENNReal.ofReal_toReal hNU_ne_top]
  have h_ofReal_B_uMax_vMax : ENNReal.ofReal (B * uMax * vMax) =
      ENNReal.ofReal (B * M_M ^ 2) * NU * NV := by
    have h_eq : B * uMax * vMax = B * M_M ^ 2 * NU.toReal * NV.toReal := by
      rw [huMax_def, hvMax_def]
      ring
    rw [h_eq]
    have h_BM2_nn : 0 ≤ B * M_M ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
    have h_BM2_NU_nn : 0 ≤ B * M_M ^ 2 * NU.toReal :=
      mul_nonneg h_BM2_nn ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_mul h_BM2_NU_nn, ENNReal.ofReal_mul h_BM2_nn,
      ENNReal.ofReal_toReal hNU_ne_top, ENNReal.ofReal_toReal hNV_ne_top]
  rw [h_ofReal_vMax, h_ofReal_uMax, h_ofReal_B_uMax_vMax]
  have h_sum_le : ENNReal.ofReal M_M + ENNReal.ofReal M_M + ENNReal.ofReal (B * M_M ^ 2) ≤
      ENNReal.ofReal C := by
    rw [show (ENNReal.ofReal M_M + ENNReal.ofReal M_M : ℝ≥0∞) =
      ENNReal.ofReal (M_M + M_M) from
      (ENNReal.ofReal_add hM_M_nn hM_M_nn).symm,
      show (ENNReal.ofReal (M_M + M_M) + ENNReal.ofReal (B * M_M ^ 2) : ℝ≥0∞) =
        ENNReal.ofReal ((M_M + M_M) + (B * M_M ^ 2)) from
      (ENNReal.ofReal_add (by linarith) (mul_nonneg hB_nn (sq_nonneg _))).symm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hC_def]
    linarith
  have h_LHS_eq : ENNReal.ofReal M_M * NV * NU + ENNReal.ofReal M_M * NU * NV +
      ENNReal.ofReal (B * M_M ^ 2) * NU * NV =
    (ENNReal.ofReal M_M + ENNReal.ofReal M_M + ENNReal.ofReal (B * M_M ^ 2)) * NU * NV := by
    ring
  rw [h_LHS_eq]
  exact mul_le_mul' (mul_le_mul' h_sum_le (le_refl _)) (le_refl _)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
