import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Calculus.ContDiffExtendInterval
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFiniteOrderTimeRegularityPerModeConvSpectralMass
import DifferentialGeometry.Analysis.Integration.L2.ForcingFiniteOrderTimeRegularityParametricIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFiniteOrderTimeRegularitySpectralPath
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFiniteOrderTimeRegularityEigenPairingBound


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem deTurckForcing_solCoeff_continuous_smallTimeBase
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T ∧
      (∀ i, ∃ c : ℝ → ℝ, Continuous c ∧
          c =ᵐ[timeMeasure T]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))) ∧
      (∀ τ : ℝ, 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ B i) ∧
      (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)),
        ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
          deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super) ∧
      (∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set R₀ : ℝ := deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super with hR₀_def
  have hR₀_pos : 0 < R₀ := deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super
  have hhalf_pos : (0 : ℝ) < R₀ ^ 2 / 2 := div_pos (pow_pos hR₀_pos 2) (by norm_num)
  set ρ : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρ_def
  have hρ_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρ := by rw [hρ_def]; linarith
  set σ' : ℝ := ((a : ℝ) + 2) + ρ with hσ'_def
  obtain ⟨Cσ', hCσ'⟩ := hspatial σ'
  set B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => Cσ' * tensorSobolevWeight (I := I) (M := M) i (-ρ) with hB_def
  have hB_sum : Summable B :=
    (tensorEigen_summable_negpow (I := I) (M := M) g₀ ρ hρ_gt).mul_left Cσ'
  have hweight_split : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
          * tensorSobolevWeight (I := I) (M := M) i σ' := by
    intro i
    rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρ) σ']
    congr 1
    rw [hσ'_def]; ring
  have hB_le : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ B i := by
    intro i t htT
    obtain ⟨hsum_t, hbd_t⟩ := hCσ' t htT
    have hterm : tensorSobolevWeight (I := I) (M := M) i σ'
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ' :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j σ') (sq_nonneg _))) hbd_t
    calc tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
            * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
            * (tensorSobolevWeight (I := I) (M := M) i σ'
              * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) := by
          rw [hweight_split i]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρ) * Cσ' :=
          mul_le_mul_of_nonneg_left hterm
            (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρ))
      _ = B i := by rw [hB_def]; ring
  have hpmc_contOn : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) T) := fun i =>
    continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) gforce i) hT.le
  have htend : Filter.Tendsto
      (fun s : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2) => ∑ i ∈ s, B i)
      Filter.atTop (nhds (∑' i, B i)) := hB_sum.hasSum
  obtain ⟨s₀, hs₀⟩ :=
    ((tendsto_order.1 htend).1 _ (by linarith [hhalf_pos] :
      (∑' i, B i) - R₀ ^ 2 / 2 < ∑' i, B i)).exists
  have htail_B_small :
      (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), B ↑x)
        ≤ R₀ ^ 2 / 2 := by
    have hcompl : (∑ i ∈ s₀, B i)
        + (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), B ↑x)
        = ∑' i, B i := hB_sum.sum_add_tsum_compl (s := s₀)
    linarith [hcompl, hs₀]
  have hg_contOn : ContinuousOn
      (fun t => ∑ i ∈ s₀, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2)
      (Set.Icc (0 : ℝ) T) :=
    continuousOn_finset_sum s₀ (fun i _ =>
      ContinuousOn.mul continuousOn_const ((hpmc_contOn i).pow 2))
  have hg0 : (∑ i ∈ s₀, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) 0) ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [perModeConv_zero_left]; ring)
  have hcwa := hg_contOn 0 ⟨le_rfl, hT.le⟩
  rw [Metric.continuousWithinAt_iff] at hcwa
  obtain ⟨δ, hδ_pos, hδ⟩ := hcwa (R₀ ^ 2 / 2) hhalf_pos
  set d : ℝ := min T (δ / 2) with hd_def
  have hd_pos : 0 < d := lt_min hT (by linarith)
  have hd_le : d ≤ T := min_le_left _ _
  have hd_le2 : d ≤ δ / 2 := min_le_right _ _
  have hcont_head : ∀ t ∈ Set.Icc (0 : ℝ) d,
      (∑ i ∈ s₀, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ≤ R₀ ^ 2 / 2 := by
    intro t ht
    have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hd_le⟩
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      have : t ≤ δ / 2 := le_trans ht.2 hd_le2
      linarith
    have hh := hδ htT hdist
    simp only [hg0, Real.dist_eq, sub_zero] at hh
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hh)
  have hball_d : ∀ t ∈ Set.Icc (0 : ℝ) d,
      (∑' i, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ≤ R₀ ^ 2 := by
    intro t ht
    have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hd_le⟩
    set f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
      fun i => tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 with hf_def
    have hf_le_B : ∀ i, f i ≤ B i := fun i => hB_le i t htT
    have hf_nonneg : ∀ i, 0 ≤ f i := fun i =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i ((a : ℝ) + 2)) (sq_nonneg _)
    have hf_sum : Summable f := Summable.of_nonneg_of_le hf_nonneg hf_le_B hB_sum
    have hhead_le : (∑ i ∈ s₀, f i) ≤ R₀ ^ 2 / 2 := hcont_head t ht
    have htail_le :
        (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), f ↑x)
          ≤ (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), B ↑x) :=
      Summable.tsum_le_tsum (fun x => hf_le_B ↑x) (hf_sum.subtype _) (hB_sum.subtype _)
    have hsplit_f : (∑' i, f i)
        = (∑ i ∈ s₀, f i)
          + (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), f ↑x) :=
      (hf_sum.sum_add_tsum_compl (s := s₀)).symm
    calc (∑' i, f i)
        = (∑ i ∈ s₀, f i)
            + (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), f ↑x) :=
          hsplit_f
      _ ≤ R₀ ^ 2 / 2 + R₀ ^ 2 / 2 :=
          add_le_add hhead_le (le_trans htail_le htail_B_small)
      _ = R₀ ^ 2 := by ring
  refine ⟨d, hd_pos, hd_le, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) p.1), ?_, ?_⟩
    · exact Continuous.Icc_extend' ((hpmc_contOn i).restrict)
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
      exact Set.IccExtend_of_mem hT.le _ ht
  · intro τ hτ
    obtain ⟨Cτ, hCτ⟩ := hspatial (τ + ρ)
    refine ⟨fun i => Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρ),
      (tensorEigen_summable_negpow (I := I) (M := M) g₀ ρ hρ_gt).mul_left Cτ, ?_⟩
    intro i t ht
    have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hd_le⟩
    obtain ⟨hsum_t, hbd_t⟩ := hCτ t htT
    have hterm : tensorSobolevWeight (I := I) (M := M) i (τ + ρ)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cτ :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j (τ + ρ)) (sq_nonneg _))) hbd_t
    have hsplit_τ : tensorSobolevWeight (I := I) (M := M) i τ
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
          * tensorSobolevWeight (I := I) (M := M) i (τ + ρ) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρ) (τ + ρ)]
      congr 1; ring
    calc tensorSobolevWeight (I := I) (M := M) i τ
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
            * (tensorSobolevWeight (I := I) (M := M) i (τ + ρ)
              * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) := by
          rw [hsplit_τ]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρ) * Cτ :=
          mul_le_mul_of_nonneg_left hterm
            (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρ))
      _ = Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρ) := by ring
  · have hae_coeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) := fun i =>
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
        (Set.Icc_subset_Icc le_rfl hd_le)
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hT1 hc gforce i)
    have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i
          = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t :=
      (MeasureTheory.ae_all_iff).2 hae_coeff
    filter_upwards [hae_all, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht_coeff ht_mem
    have hnorm_sq : ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ^ 2
        = ∑' i, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
            * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 := by
      rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
      exact tsum_congr (fun i => by rw [ht_coeff i])
    have hWsq_le : ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ^ 2 ≤ R₀ ^ 2 := by
      rw [hnorm_sq]; exact hball_d t ht_mem
    nlinarith [norm_nonneg (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t), hR₀_pos.le, hWsq_le]
  · intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd_le)
      (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hT1 hc gforce i)

private theorem exists_smoothCcTensor_of_allOrder_spectralMass_local
    (g₀ : SmoothRiemannianMetric I M)
    (d : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i) :
    ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = d i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  obtain ⟨B0, hB0s, hB0le⟩ := hmass 0 le_rfl
  set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
    tensorHs_of_spectralMass_majorant (I := I) (M := M) d B0 hB0s hB0le with hv0_def
  set u : TensorL2 0 2 g₀ :=
    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = d i := by
    intro i
    rw [hu_def, tensorHsToL2_tensorL2Coeff]
    simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff]
  have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hBs
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hu_coeff i]; exact hBle i
  have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
    allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
  obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
  refine ⟨S, fun i => ?_⟩
  have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
        = (S : TensorL2 0 2 g₀) from rfl, hS]
  rw [hSL2, hu_coeff i]

private def deTurckRHSReconSectionFiniteOrder (g₀ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ)).hasCompactSupport }

private local instance tensorRSModelNormedAddCommGroup_local :
    NormedAddCommGroup (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2

private local instance tensorRSModelNormedSpace_local :
    NormedSpace ℝ (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace 0 2


section FiniteOrderReconJetEnergy

open Tensor0SBundle TensorMultilinear
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Integral.Connection

section FiniteOrderAnisotropicReconstruction

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth
  tensorChartComponentRaw tensorChartComponentProjection tensorChartBasisElement
  toEuclidean_extChartAt_mem_chartTargetEuclid)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDerivWithin_isOpen_eq_of_isOpen
    {O₁ O₂ : Set E} (h₁ : IsOpen O₁) (h₂ : IsOpen O₂) (n : ℕ) (f : E → ℝ) {z : E}
    (hz₁ : z ∈ O₁) (hz₂ : z ∈ O₂) :
    iteratedFDerivWithin ℝ n f O₁ z = iteratedFDerivWithin ℝ n f O₂ z := by
  rw [iteratedFDerivWithin_of_isOpen n h₁ hz₁, iteratedFDerivWithin_of_isOpen n h₂ hz₂]

set_option maxHeartbeats 1600000 in
private theorem pdIter_rawCompOnE_eigenSeries_tsum_eq_local
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (d : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (hd : ∀ i, tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S) i = d i)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (L : List E) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentialGeometry.Analysis.iteratedDirDeriv L
        (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx) y
      = ∑' i, d i * DifferentialGeometry.Analysis.iteratedDirDeriv L
          (tensorChartComponentOnModel (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) y := by
  classical
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  have hzero : ∀ z ∈ Ω, tensorChartComponentOnModel (I := I) (M := M) g S α Jdx z
      = ∑' i, d i * tensorChartComponentOnModel (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx z := by
    intro z hz
    have hz_src : (extChartAt I α).symm z ∈ (chartAt H α).source := by
      have hzt : z ∈ (extChartAt I α).target := interior_subset hz
      have := (extChartAt I α).map_target hzt
      rwa [extChartAt_source (I := I)] at this
    exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
      g S d hd hmass α Jdx hz_src
  obtain ⟨r, hr_pos, hball⟩ := Metric.isOpen_iff.mp hΩ_open y hy
  set Bo : Set E := Metric.ball y (r / 2) with hBo_def
  set Bc : Set E := Metric.closedBall y (r / 2) with hBc_def
  have hBo_open : IsOpen Bo := Metric.isOpen_ball
  have hBoBc : Bo ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro z hz
    rw [hBc_def, Metric.mem_closedBall] at hz
    exact hball (by rw [Metric.mem_ball]; linarith)
  have hBo_sub : Bo ⊆ Ω := hBoBc.trans hBc_sub
  have hyBo : y ∈ Bo := Metric.mem_ball_self (by positivity)
  set ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → E → ℝ :=
    fun i => tensorChartComponentOnModel (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx with hψ_def
  have hψ_smooth : ∀ i, ContDiffOn ℝ ∞ (ψ i) Ω := fun i =>
    rawCompOnE_contDiffOn (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx
  obtain ⟨C, p, hC_nn, hC⟩ := exists_pdIter_rawCompOnE_eigen_jet_le_lambda_pow
    (I := I) (M := M) g α Jdx L.length ([] : List E)
    (isCompact_closedBall y (r / 2)) hBc_sub
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  obtain ⟨Bd, hBd_sum, hBd_le⟩ := hmass (2 * ((p : ℝ) + (sW : ℝ))) (by positivity)
  have hBd_nn : ∀ i, 0 ≤ Bd i := by
    intro i
    have h := hBd_le i
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i (2 * ((p : ℝ) + (sW : ℝ)))
    nlinarith [sq_nonneg (d i), hw.le]
  have hd_abs : ∀ i, |d i| ≤ Real.sqrt (Bd i) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((p : ℝ) + (sW : ℝ))) :=
    fun i => abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((p : ℝ) + (sW : ℝ))
      (hBd_le i)
  set vmode : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => C * (Real.sqrt (Bd i) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))
    with hvmode_def
  have hvmode_sum : Summable vmode :=
    (summable_sqrt_mul_weight_neg (I := I) (M := M) g Bd hBd_sum hBd_nn hsW_gt).mul_left C
  have hcollapse : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((p : ℝ) + (sW : ℝ))) *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p =
      tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
    intro i
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) p,
      ← Real.rpow_add (hbase_pos i)]
    congr 1; ring
  have hmode_le : ∀ i, |d i| * (C *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p) ≤ vmode i := by
    intro i
    have hpow_nn : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p :=
      pow_nonneg (hbase_pos i).le p
    calc |d i| * (C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p)
        ≤ (Real.sqrt (Bd i) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((p : ℝ) + (sW : ℝ)))) *
          (C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p) := by
          refine mul_le_mul_of_nonneg_right (hd_abs i) (by positivity)
      _ = C * (Real.sqrt (Bd i) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((p : ℝ) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p)) := by ring
      _ = vmode i := by rw [hcollapse i, hvmode_def]
  set fm : TensorEigenIdx (I := I) (M := M) g 0 2 → E → ℝ :=
    fun i z => d i * ψ i z with hfm_def
  have hfm_cd : ∀ i, ContDiffOn ℝ ((L.length : ℕ∞) : ℕ∞) (fm i) Bo := by
    intro i
    exact contDiffOn_const.mul (((hψ_smooth i).mono hBo_sub).of_le
      (by exact_mod_cast le_top))
  have hfm_bound : ∀ (n : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2) (z : E),
      z ∈ Bo → (n : ℕ∞) ≤ (L.length : ℕ∞) →
      ‖iteratedFDerivWithin ℝ n (fm i) Bo z‖ ≤ vmode i := by
    intro n i z hz hn
    have hn' : n ≤ L.length := by exact_mod_cast hn
    set Ad : ℝ →L[ℝ] ℝ := (d i) • ContinuousLinearMap.id ℝ ℝ with hAd_def
    have hAd_norm : ‖Ad‖ ≤ |d i| := by
      refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg (d i)) (fun x => ?_)
      rw [hAd_def]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Real.norm_eq_abs, abs_mul, le_refl]
    have hcomp : Set.EqOn (fm i) (Ad ∘ (ψ i)) Bo := by
      intro z' _
      simp only [hfm_def, hAd_def, Function.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    have hψi_cw : ContDiffWithinAt ℝ ((n : ℕ) : ℕ∞) (ψ i) Bo z :=
      (((hψ_smooth i).mono hBo_sub) z hz).of_le (by exact_mod_cast le_top)
    have h1 : ‖iteratedFDerivWithin ℝ n (fm i) Bo z‖
        ≤ ‖Ad‖ * ‖iteratedFDerivWithin ℝ n (ψ i) Bo z‖ := by
      rw [iteratedFDerivWithin_congr hcomp hz]
      exact Ad.norm_iteratedFDerivWithin_comp_left hψi_cw hBo_open.uniqueDiffOn hz
        (le_refl _)
    have h2 : ‖iteratedFDerivWithin ℝ n (ψ i) Bo z‖
        = ‖iteratedFDerivWithin ℝ n (ψ i) Ω z‖ := by
      rw [iteratedFDerivWithin_isOpen_eq_of_isOpen hBo_open hΩ_open n (ψ i) hz
        (hBo_sub hz)]
    have h3 := hC n hn' i z (hBoBc hz)
    simp only [DifferentialGeometry.Analysis.pdIter_nil] at h3
    refine le_trans h1 ?_
    rw [h2]
    calc ‖Ad‖ * ‖iteratedFDerivWithin ℝ n (ψ i) Ω z‖
        ≤ |d i| * (C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p) :=
          mul_le_mul hAd_norm h3 (norm_nonneg _) (abs_nonneg (d i))
      _ ≤ vmode i := hmode_le i
  have htsum_deriv := DifferentialGeometry.Analysis.iteratedFDerivWithin_tsum
    (f := fm) (v := fun _ i => vmode i) (s := Bo) (N := (L.length : ℕ∞))
    hBo_open.uniqueDiffOn (convex_ball y (r / 2)) hfm_cd
    (fun n _ => hvmode_sum) hfm_bound hyBo (le_refl _) hyBo
  have hbridgeS := DifferentialGeometry.Analysis.pdIter_eq_iteratedFDerivWithin_apply
    hΩ_open (rawCompOnE_contDiffOn (I := I) (M := M) g S α Jdx) L hy
  have hswitchS : iteratedFDerivWithin ℝ L.length
        (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx) Ω y
      = iteratedFDerivWithin ℝ L.length
        (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx) Bo y :=
    iteratedFDerivWithin_isOpen_eq_of_isOpen hΩ_open hBo_open L.length _ hy hyBo
  have hcongrS : iteratedFDerivWithin ℝ L.length
        (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx) Bo y
      = iteratedFDerivWithin ℝ L.length (fun z => ∑' i, fm i z) Bo y := by
    refine iteratedFDerivWithin_congr (fun z hz => ?_) hyBo L.length
    exact hzero z (hBo_sub hz)
  have hsummable_fd : Summable (fun i => iteratedFDerivWithin ℝ L.length (fm i) Bo y) :=
    Summable.of_norm_bounded hvmode_sum
      (fun i => hfm_bound L.length i y hyBo (le_refl _))
  have heval : (∑' i, iteratedFDerivWithin ℝ L.length (fm i) Bo y)
        (DifferentialGeometry.Analysis.pdVec L)
      = ∑' i, (iteratedFDerivWithin ℝ L.length (fm i) Bo y)
          (DifferentialGeometry.Analysis.pdVec L) :=
    (ContinuousMultilinearMap.hasSum_eval hsummable_fd.hasSum
      (DifferentialGeometry.Analysis.pdVec L)).tsum_eq.symm
  have hmode_eval : ∀ i, (iteratedFDerivWithin ℝ L.length (fm i) Bo y)
        (DifferentialGeometry.Analysis.pdVec L)
      = d i * DifferentialGeometry.Analysis.iteratedDirDeriv L (ψ i) y := by
    intro i
    have hsmul : fm i = (d i) • (ψ i) := by
      funext z'
      simp only [hfm_def, Pi.smul_apply, smul_eq_mul]
    have hψi_cw : ContDiffWithinAt ℝ ((L.length : ℕ) : ℕ∞) (ψ i) Bo y :=
      (((hψ_smooth i).mono hBo_sub) y hyBo).of_le (by exact_mod_cast le_top)
    have h1 : iteratedFDerivWithin ℝ L.length (fm i) Bo y
        = (d i) • iteratedFDerivWithin ℝ L.length (ψ i) Bo y := by
      rw [hsmul]
      exact iteratedFDerivWithin_const_smul_apply hψi_cw hBo_open.uniqueDiffOn hyBo
    have hbridge_i := DifferentialGeometry.Analysis.pdIter_eq_iteratedFDerivWithin_apply
      hΩ_open (hψ_smooth i) L hy
    have hswitch_i : iteratedFDerivWithin ℝ L.length (ψ i) Ω y
        = iteratedFDerivWithin ℝ L.length (ψ i) Bo y :=
      iteratedFDerivWithin_isOpen_eq_of_isOpen hΩ_open hBo_open L.length (ψ i) hy hyBo
    rw [h1]
    have : ((d i) • iteratedFDerivWithin ℝ L.length (ψ i) Bo y)
        (DifferentialGeometry.Analysis.pdVec L)
        = d i * ((iteratedFDerivWithin ℝ L.length (ψ i) Bo y)
            (DifferentialGeometry.Analysis.pdVec L)) := rfl
    rw [this, ← hswitch_i, ← hbridge_i]
  calc DifferentialGeometry.Analysis.iteratedDirDeriv L
        (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx) y
      = (iteratedFDerivWithin ℝ L.length
          (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx) Ω y)
          (DifferentialGeometry.Analysis.pdVec L) := hbridgeS
    _ = (iteratedFDerivWithin ℝ L.length (fun z => ∑' i, fm i z) Bo y)
          (DifferentialGeometry.Analysis.pdVec L) := by rw [hswitchS, hcongrS]
    _ = (∑' i, iteratedFDerivWithin ℝ L.length (fm i) Bo y)
          (DifferentialGeometry.Analysis.pdVec L) := by rw [htsum_deriv]
    _ = ∑' i, (iteratedFDerivWithin ℝ L.length (fm i) Bo y)
          (DifferentialGeometry.Analysis.pdVec L) := heval
    _ = ∑' i, d i * DifferentialGeometry.Analysis.iteratedDirDeriv L (ψ i) y := by
        refine tsum_congr (fun i => hmode_eval i)

set_option maxHeartbeats 1600000 in
private theorem spectralPathFO_rawCompOnE_pdIter_euclidean_contDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (L : List E) :
    ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => DifferentialGeometry.Analysis.iteratedDirDeriv L
        (tensorChartComponentOnModel (I := I) (M := M) g (T_rep q.1) α Jdx) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  set ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → E → ℝ :=
    fun i => DifferentialGeometry.Analysis.iteratedDirDeriv L
      (tensorChartComponentOnModel (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) with hψ_def
  have hψ_smooth : ∀ i, ContDiffOn ℝ ∞ (ψ i) Ω := fun i =>
    pdIter_rawCompOnE_contDiffOn (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx L
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open y₀ hy₀
  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2), isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set E := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set E := Metric.closedBall y₀ (r / 2) with hBc_def
  have hball_le : B ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro z hz
    rw [hBc_def, Metric.mem_closedBall] at hz
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hB_sub : B ⊆ Ω := hball_le.trans hBc_sub
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hslab_inter :
      (Set.Icc (0 : ℝ) T ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc (0 : ℝ) T ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.inter_eq_right.mpr hB_sub]
  rw [hslab_inter]
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : (r / 2) ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (convex_Icc (0 : ℝ) T).prod (convex_closedBall y₀ (r / 2))
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod huniqBc
  obtain ⟨Csp, pSp, hCsp_nn, hCsp⟩ := exists_pdIter_rawCompOnE_eigen_jet_le_lambda_pow
    (I := I) (M := M) g α Jdx kk L hBc_compact hBc_sub
  have hmajorant := eigenTimeSpatialProductMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (I := I) (M := M) g hT kk φ hφ_smooth hmodemass ψ hΩ_open hψ_smooth
    huniqBc hBc_sub Csp pSp hCsp_nn
    (fun n hn i y hy => hCsp n hn i y hy)
  set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun n => if hn : n ≤ kk then Classical.choose (hmajorant n hn) else 0 with hv_def
  have hv_spec : ∀ (n : ℕ) (hn : n ≤ kk), Summable (v n) ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc →
        ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => φ i p.1 * ψ i p.2)
            (Set.Icc (0 : ℝ) T ×ˢ Bc) q‖ ≤ v n i := by
    intro n hn
    have hspec := Classical.choose_spec (hmajorant n hn)
    have hveq : v n = Classical.choose (hmajorant n hn) := by
      rw [hv_def]; exact dif_pos hn
    rw [hveq]
    exact hspec
  have htsum_Bc : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => ∑' i, φ i q.1 * ψ i q.2)
      (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
    have hmode_cd : ∀ i, ContDiffOn ℝ ((kk : ℕ) : ℕ∞)
        (fun q : ℝ × E => φ i q.1 * ψ i q.2) (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
      intro i
      have hfst : ContDiffOn ℝ (kk : ℕ) (fun q : ℝ × E => φ i q.1)
          (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
        ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
      have hsnd : ContDiffOn ℝ (kk : ℕ) (fun q : ℝ × E => ψ i q.2)
          (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
        refine (((hψ_smooth i).mono hBc_sub).of_le
          (by exact_mod_cast le_top)).comp contDiffOn_snd ?_
        intro q hq; exact hq.2
      exact hfst.mul hsnd
    have h := DifferentialGeometry.Analysis.contDiffOn_tsum
      (f := fun i (q : ℝ × E) => φ i q.1 * ψ i q.2) (v := v)
      (s := Set.Icc (0 : ℝ) T ×ˢ Bc) (N := (kk : ℕ∞))
      huniq hconv hmode_cd
      (fun n hn => (hv_spec n (by exact_mod_cast hn)).1)
      (fun n i q hq hn => (hv_spec n (by exact_mod_cast hn)).2 i q hq)
      (x₀ := ((0 : ℝ), y₀))
      ⟨Set.left_mem_Icc.mpr hT.le, Metric.mem_closedBall_self (by positivity)⟩
    exact h.of_le (by exact_mod_cast le_rfl)
  have htsum : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => ∑' i, φ i q.1 * ψ i q.2)
      (Set.Icc (0 : ℝ) T ×ˢ B) :=
    htsum_Bc.mono (Set.prod_mono (le_refl _) hball_le)
  refine htsum.congr ?_
  rintro ⟨t, y⟩ ⟨ht, hyB⟩
  have hyΩ : y ∈ Ω := hB_sub hyB
  have hid := pdIter_rawCompOnE_eigenSeries_tsum_eq_local (I := I) (M := M)
    g (T_rep t) (fun i => φ i t) (hcoeff t ht)
    (fun σ hσ => by
      obtain ⟨B', hB'_sum, hB'_le⟩ := hmodemass 0 (Nat.zero_le kk) σ hσ
      refine ⟨B', hB'_sum, fun i => ?_⟩
      have h := hB'_le i t ht
      rwa [iteratedDeriv_zero] at h)
    α Jdx L hyΩ
  exact hid

private theorem anisoOn_rawCompOnE_spectralPath
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn kk T (interior (extChartAt I α).target)
      (fun t => tensorChartComponentOnModel (I := I) (M := M) g (T_rep t) α Jdx) :=
  ⟨fun t _ => rawCompOnE_contDiffOn (I := I) (M := M) g (T_rep t) α Jdx,
   fun L => spectralPathFO_rawCompOnE_pdIter_euclidean_contDiffOn_local (I := I) (M := M)
     g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Jdx L⟩

section RealizedChartAtoms

variable {g₀ g_bg : SmoothRiemannianMetric I M} {T : ℝ} {k : ℕ}
  {F : ℝ → SmoothCcTensor g₀ 0 2} {δ : ℝ}
  {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ}

private theorem anisoOn_chartGramOnE_realizePath
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => Integral.DivergenceTheorem.chartGramOnE (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α a b y) := by
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hbase := DifferentialGeometry.Analysis.anisoOn_timeIndep (k := k) (T := T) hV
    (chartGramOnE_contDiffOn_int (I := I) g₀ α a b)
  have hraw1 := anisoOn_rawCompOnE_spectralPath (I := I) (M := M) g₀ hT k F φ
    hφ_smooth hcoeff hmodemass α ![a, b]
  have hraw2 := anisoOn_rawCompOnE_spectralPath (I := I) (M := M) g₀ hT k F φ
    hφ_smooth hcoeff hmodemass α ![b, a]
  have hsum := hbase.add hV ((hraw1.add hV hraw2).smul hV (1 / 2 : ℝ))
  refine hsum.congr hV _ (fun t ht y hy => ?_)
  exact (chartGramOnE_realize_eq_add_half_rawCompOnE (I := I) (M := M) g₀ (F t)
    hδ_lt (hδ t) α a b hy).symm

private theorem anisoOn_realizeGram_det
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => (Integral.Measure.chartGramMatrix (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
        ((extChartAt I α).symm y)).det) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hterm : ∀ σp : Equiv.Perm (Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
        (fun t y => (((Equiv.Perm.sign σp : ℤ) : ℝ)) *
          ∏ i : Fin (Module.finrank ℝ E),
            Integral.DivergenceTheorem.chartGramOnE (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α (σp i) i y) := by
    intro σp
    refine DifferentialGeometry.Analysis.AnisotropicJointContDiffOn.smul hV ?_ _
    exact DifferentialGeometry.Analysis.anisoOn_finsetProd hV Finset.univ
      (fun i _ => anisoOn_chartGramOnE_realizePath hT hδ_lt hδ hφ_smooth hcoeff
        hmodemass α (σp i) i)
  have hsum := DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
    (fun σp _ => hterm σp)
  refine hsum.congr hV _ (fun t ht y hy => ?_)
  beta_reduce
  rw [Matrix.det_apply']
  rfl

private theorem anisoOn_realizeGram_adjugate
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => (Integral.Measure.chartGramMatrix (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
        ((extChartAt I α).symm y)).adjugate a b) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hentry : ∀ (r c : Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
        (fun t y => ((Integral.Measure.chartGramMatrix (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
            ((extChartAt I α).symm y)).updateRow b (Pi.single a 1)) r c) := by
    intro r c
    by_cases hr : r = b
    · have hconst := DifferentialGeometry.Analysis.anisoOn_const (k := k) (T := T)
        (V := interior (extChartAt I α).target)
        (@Pi.single (Fin (Module.finrank ℝ E)) (fun _ => ℝ) _ _ a 1 c)
      refine hconst.congr hV _ (fun t ht y hy => ?_)
      beta_reduce
      rw [Matrix.updateRow_apply, if_pos hr]
    · refine (anisoOn_chartGramOnE_realizePath hT hδ_lt hδ hφ_smooth hcoeff
        hmodemass α r c).congr hV _ (fun t ht y hy => ?_)
      beta_reduce
      rw [Matrix.updateRow_apply, if_neg hr]
      rfl
  have hterm : ∀ σp : Equiv.Perm (Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
        (fun t y => (((Equiv.Perm.sign σp : ℤ) : ℝ)) *
          ∏ i : Fin (Module.finrank ℝ E),
            ((Integral.Measure.chartGramMatrix (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
              ((extChartAt I α).symm y)).updateRow b (Pi.single a 1)) (σp i) i) := by
    intro σp
    refine DifferentialGeometry.Analysis.AnisotropicJointContDiffOn.smul hV ?_ _
    exact DifferentialGeometry.Analysis.anisoOn_finsetProd hV Finset.univ
      (fun i _ => hentry (σp i) i)
  have hsum := DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
    (fun σp _ => hterm σp)
  refine hsum.congr hV _ (fun t ht y hy => ?_)
  beta_reduce
  rw [Matrix.adjugate_apply, Matrix.det_apply']

private theorem anisoOn_realizeGram_inv
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => Integral.DivergenceTheorem.chartInvGramMatrix (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
        ((extChartAt I α).symm y) a b) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hdet := anisoOn_realizeGram_det hT hδ_lt hδ hφ_smooth hcoeff hmodemass α
  have hdet_ne : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ interior (extChartAt I α).target,
      (Integral.Measure.chartGramMatrix (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
        ((extChartAt I α).symm y)).det ≠ 0 := by
    intro t _ y hy
    have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
    have hsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      have := (extChartAt I α).map_target hy_t
      rwa [extChartAt_source (I := I)] at this
    have hbase : (extChartAt I α).symm y ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)]
      exact hsrc
    exact ne_of_gt (chartGramMatrix_det_pos (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α hbase)
  have hinv := hdet.inv hV hdet_ne
  have hadj := anisoOn_realizeGram_adjugate hT hδ_lt hδ hφ_smooth hcoeff hmodemass α a b
  refine (hinv.mul hV hadj).congr hV _ (fun t ht y hy => ?_)
  rw [Integral.DivergenceTheorem.chartInvGramMatrix, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv]

private theorem anisoOn_realize_chartChristoffel
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (i j c : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => Integral.DivergenceTheorem.chartChristoffel (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i j c y) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hgram := fun a b => anisoOn_chartGramOnE_realizePath hT hδ_lt hδ hφ_smooth
    hcoeff hmodemass α a b
  have hinv := fun a b => anisoOn_realizeGram_inv hT hδ_lt hδ hφ_smooth hcoeff
    hmodemass α a b
  have hterm : ∀ l : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
        (fun t y => Integral.DivergenceTheorem.chartInvGramMatrix (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
            ((extChartAt I α).symm y) c l *
          (DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E i)
              (Integral.DivergenceTheorem.chartGramOnE (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α l j) y +
            DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E j)
              (Integral.DivergenceTheorem.chartGramOnE (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α l i) y -
            DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E l)
              (Integral.DivergenceTheorem.chartGramOnE (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i j) y)) := by
    intro l
    refine (hinv c l).mul hV ?_
    exact (((hgram l j).pdShift hV (chartModelBasis E i)).add hV
      ((hgram l i).pdShift hV (chartModelBasis E j))).sub hV
      ((hgram i j).pdShift hV (chartModelBasis E l))
  have hsum := (DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
    (fun l _ => hterm l)).smul hV (1 / 2 : ℝ)
  refine hsum.congr hV _ (fun t ht y hy => ?_)
  rw [Integral.DivergenceTheorem.chartChristoffel_def]
  rfl

private theorem anisoOn_realize_chartDeTurckVFComp
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (c : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => chartDeTurckVFComp (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α c y) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hterm : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
        (fun t y => Integral.DivergenceTheorem.chartInvGramMatrix (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α
            ((extChartAt I α).symm y) a b *
          (Integral.DivergenceTheorem.chartChristoffel (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α a b c y -
            Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg α a b c y)) := by
    intro a b
    refine (anisoOn_realizeGram_inv hT hδ_lt hδ hφ_smooth hcoeff hmodemass α a b).mul hV ?_
    refine (anisoOn_realize_chartChristoffel hT hδ_lt hδ hφ_smooth hcoeff hmodemass
      α a b c).sub hV ?_
    exact DifferentialGeometry.Analysis.anisoOn_timeIndep hV
      (Integral.DivergenceTheorem.chartChristoffel_contDiffOn_interior (I := I) g_bg α a b c)
  have hsum := DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
    (fun a (_ : a ∈ Finset.univ) =>
      DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
        (fun b (_ : b ∈ Finset.univ) => hterm a b))
  refine hsum.congr hV _ (fun t ht y hy => ?_)
  rw [chartDeTurckVFComp_def]
  rfl

private theorem anisoOn_realize_chartRicci
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (i c : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => Integral.DivergenceTheorem.chartRicciTensor (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i c y) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hchr := fun a b d => anisoOn_realize_chartChristoffel hT hδ_lt hδ hφ_smooth
    hcoeff hmodemass α a b d
  have hriem : ∀ j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
        (fun t y => Integral.DivergenceTheorem.chartRiemannTensor (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i j c j y) := by
    intro j
    have hterm : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T
        (interior (extChartAt I α).target)
        (fun t y =>
          DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E j)
            (Integral.DivergenceTheorem.chartChristoffel (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i c j) y -
          DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E c)
            (Integral.DivergenceTheorem.chartChristoffel (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i j j) y +
          (∑ m : Fin (Module.finrank ℝ E),
            (Integral.DivergenceTheorem.chartChristoffel (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α j m j y *
              Integral.DivergenceTheorem.chartChristoffel (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i c m y -
              Integral.DivergenceTheorem.chartChristoffel (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α c m j y *
              Integral.DivergenceTheorem.chartChristoffel (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i j m y))) := by
      refine (((hchr i c j).pdShift hV (chartModelBasis E j)).sub hV
        ((hchr i j j).pdShift hV (chartModelBasis E c))).add hV ?_
      refine DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
        (fun m _ => ?_)
      exact ((hchr j m j).mul hV (hchr i c m)).sub hV ((hchr c m j).mul hV (hchr i j m))
    refine hterm.congr hV _ (fun t ht y hy => ?_)
    rw [Integral.DivergenceTheorem.chartRiemannTensor_def]
    rfl
  have hsum := DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
    (fun j (_ : j ∈ Finset.univ) => hriem j)
  refine hsum.congr hV _ (fun t ht y hy => ?_)
  rw [Integral.DivergenceTheorem.chartRicciTensor_def]

private theorem anisoOn_realize_chartLieDeTurckComp
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => chartLieDeTurckComp (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α i j y) := by
  classical
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hgram := fun a b => anisoOn_chartGramOnE_realizePath hT hδ_lt hδ hφ_smooth
    hcoeff hmodemass α a b
  have hvf := fun c => anisoOn_realize_chartDeTurckVFComp (g_bg := g_bg) hT hδ_lt hδ
    hφ_smooth hcoeff hmodemass α c
  have h1 : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => ∑ c : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α c y *
          DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E c)
            (Integral.DivergenceTheorem.chartGramOnE (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i j) y) :=
    DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
      (fun c _ => (hvf c).mul hV ((hgram i j).pdShift hV (chartModelBasis E c)))
  have h2 : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => ∑ c : Fin (Module.finrank ℝ E),
        Integral.DivergenceTheorem.chartGramOnE (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α c j y *
          DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E i)
            (chartDeTurckVFComp (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α c) y) :=
    DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
      (fun c _ => (hgram c j).mul hV ((hvf c).pdShift hV (chartModelBasis E i)))
  have h3 : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => ∑ c : Fin (Module.finrank ℝ E),
        Integral.DivergenceTheorem.chartGramOnE (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) α i c y *
          DifferentialGeometry.Analysis.dirDeriv (chartModelBasis E j)
            (chartDeTurckVFComp (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α c) y) :=
    DifferentialGeometry.Analysis.anisoOn_finsetSum hV Finset.univ
      (fun c _ => (hgram i c).mul hV ((hvf c).pdShift hV (chartModelBasis E j)))
  refine ((h1.add hV h2).add hV h3).congr hV _ (fun t ht y hy => ?_)
  rw [chartLieDeTurckComp_def]
  rfl

private theorem anisoOn_realize_chartDeTurckRicciRHS
    (hT : 0 < T) (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T (interior (extChartAt I α).target)
      (fun t y => chartDeTurckRicciRHS (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α i j y) := by
  have hV : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hric := anisoOn_realize_chartRicci hT hδ_lt hδ hφ_smooth hcoeff hmodemass α i j
  have hlie := anisoOn_realize_chartLieDeTurckComp (g_bg := g_bg) hT hδ_lt hδ hφ_smooth
    hcoeff hmodemass α i j
  refine ((hric.smul hV (-2 : ℝ)).add hV hlie).congr hV _ (fun t ht y hy => ?_)
  rw [chartDeTurckRicciRHS_def]

end RealizedChartAtoms

section IterLaplacianInduction

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma tensorChartComponentRaw_congr_toSection
    {g₁ g₂ : SmoothRiemannianMetric I M}
    (S₁ : SmoothCcTensor g₁ 0 2) (S₂ : SmoothCcTensor g₂ 0 2)
    (h : ∀ x : M, S₁.toSection x = S₂.toSection x) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g₁ 0 2 S₁ α Idx Jdx x =
      tensorChartComponentRaw (I := I) (M := M) g₂ 0 2 S₂ α Idx Jdx x := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  change tensorChartComponentProjection (E := E) 0 2 Idx Jdx
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt
        ℝ x (S₁.toSection x)) =
    tensorChartComponentProjection (E := E) 0 2 Idx Jdx
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt
        ℝ x (S₂.toSection x))
  rw [h x]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentRaw_sub_eq
    (g : SmoothRiemannianMetric I M) (S₁ S₂ : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2 (S₁ - S₂) α Idx Jdx x =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S₁ α Idx Jdx x -
        tensorChartComponentRaw (I := I) (M := M) g 0 2 S₂ α Idx Jdx x := by
  have hrepr : S₁ - S₂ = S₁ + (-1 : ℝ) • S₂ := by
    rw [neg_one_smul]
    abel
  rw [hrepr,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_add
      (I := I) (M := M),
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul
      (I := I) (M := M)]
  simp only [smul_eq_mul, neg_one_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma reconFO_raw_eq_chartRHS
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδS : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S) δ)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
        (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg S hδ_lt hδS) α ![] Jdx x =
      chartDeTurckRicciRHS (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδS) g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α x) := by
  have hgood : x ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
      (I := I) α, extChartAt_source (I := I)]
    exact hx
  have hcongr := tensorChartComponentRaw_congr_toSection
    (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg S hδ_lt hδS)
    (DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBg (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδS))
    (fun z => rfl) α ![] Jdx x
  rw [hcongr,
    tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie (I := I) (M := M)
      g_bg (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδS) α hgood ![] Jdx,
    chartDeTurckRicciRHS_def]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma pouRegion_open (α : M) :
    IsOpen ((toEuclidean (E := E)) '' ((extChartAt I α) ''
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x})) := by
  classical
  set pou : M → ℝ := fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    with hpou
  have hpou_cont : Continuous pou := (chartAtlasPOU I M α).contMDiff.continuous
  set U : Set M := {x : M | 0 < pou x} with hU
  have hU_open : IsOpen U := isOpen_lt continuous_const hpou_cont
  have hU_src : U ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source (I := I)]
    refine (chartAtlasPOU_isSubordinate (I := I) (M := M) α) ?_
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hx))
  have himg : (extChartAt I α) '' U =
      (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' U :=
    (extChartAt I α).image_eq_target_inter_inv_preimage hU_src
  have himg_open : IsOpen ((extChartAt I α) '' U) := by
    rw [himg]
    exact (continuousOn_extChartAt_symm (I := I) α).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) α) hU_open
  exact (toEuclidean (E := E)).isOpenMap _ himg_open

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouRegion_subset_chartTargetEuclid (α : M) :
    (toEuclidean (E := E)) '' ((extChartAt I α) ''
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x}) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rintro ŷ ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    refine (chartAtlasPOU_isSubordinate (I := I) (M := M) α) ?_
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hx))
  exact ⟨extChartAt I α x, (extChartAt I α).map_source hx_src, rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouRegion_mem_facts (α : M)
    {ŷ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hŷ : ŷ ∈ (toEuclidean (E := E)) '' ((extChartAt I α) ''
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x})) :
    (extChartAt I α).symm (toEuclidean.symm ŷ) ∈
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ∧
    toEuclidean.symm ŷ ∈ (extChartAt I α).target ∧
    (extChartAt I α) ((extChartAt I α).symm (toEuclidean.symm ŷ)) =
      toEuclidean.symm ŷ ∧
    (toEuclidean (E := E)) ((extChartAt I α)
      ((extChartAt I α).symm (toEuclidean.symm ŷ))) = ŷ := by
  obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hŷ
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    refine (chartAtlasPOU_isSubordinate (I := I) (M := M) α) ?_
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hx))
  have hz_t : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_src
  have hsymm_te : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) x)) = (extChartAt I α) x :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hround : (extChartAt I α).symm ((extChartAt I α) x) = x :=
    (extChartAt I α).left_inv hx_src
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsymm_te, hround]; exact hx
  · rw [hsymm_te]; exact hz_t
  · rw [hsymm_te, hround]
  · rw [hsymm_te, hround]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eq_pdDir (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    euclidPartial (E := E) i u
      = DifferentialGeometry.Analysis.dirDeriv (EuclideanSpace.single i 1) u := rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem anisoOn_pushed_oneMinusConnLapIter_reconFOPath
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (m : ℕ) :
    ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
    DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T
      ((toEuclidean (E := E)) '' ((extChartAt I α) ''
        {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x}))
      (fun t ŷ => chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
          α ![] Jdx) ŷ) := by
  classical
  set R : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) ''
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x}) with hR_def
  have hR_open : IsOpen R := pouRegion_open (I := I) (M := M) α
  have hR_sub : R ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouRegion_subset_chartTargetEuclid (I := I) (M := M) α
  induction m with
  | zero =>
      intro Jdx
      have hE_aniso : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T
          (interior (extChartAt I α).target)
          (fun t => tensorChartComponentOnModel (I := I) (M := M) g₀
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) α Jdx) := by
        have hVE : IsOpen (interior (extChartAt I α).target) := isOpen_interior
        refine (anisoOn_realize_chartDeTurckRicciRHS (g_bg := g_bg) hT hδ_lt hδ
          hφ_smooth hcoeff hmodemass α (Jdx 0) (Jdx 1)).congr hVE _
          (fun t ht y hy => ?_)
        have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
        have hsymm_src : (extChartAt I α).symm y ∈ (chartAt H α).source := by
          have := (extChartAt I α).map_target hy_t
          rwa [extChartAt_source (I := I)] at this
        have hkey := reconFO_raw_eq_chartRHS (I := I) (M := M) g₀ g_bg (F t)
          hδ_lt (hδ t) α Jdx hsymm_src
        have hRI : (extChartAt I α) ((extChartAt I α).symm y) = y :=
          (extChartAt I α).right_inv hy_t
        change chartDeTurckRicciRHS (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) g_bg α
            (Jdx 0) (Jdx 1) y =
          tensorChartComponentOnModel (I := I) (M := M) g₀
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) α Jdx y
        rw [show tensorChartComponentOnModel (I := I) (M := M) g₀
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) α Jdx y =
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) α ![] Jdx
              ((extChartAt I α).symm y) from rfl, hkey, hRI]
      have htrans := hE_aniso.comp_clequiv (toEuclidean (E := E)).symm isOpen_interior
      have hR_sub' : R ⊆ (((toEuclidean (E := E)).symm : EuclideanSpace ℝ
          (Fin (Module.finrank ℝ E)) ≃L[ℝ] E) : EuclideanSpace ℝ
          (Fin (Module.finrank ℝ E)) → E) ⁻¹' (interior (extChartAt I α).target) := by
        intro ŷ hŷ
        obtain ⟨-, hmem, -, -⟩ := pouRegion_mem_facts (I := I) (M := M) α hŷ
        rw [Set.mem_preimage, (isOpen_extChartAt_target (I := I) α).interior_eq]
        exact hmem
      refine ((htrans.mono hR_sub').congr hR_open _ (fun t ht ŷ hŷ => ?_))
      obtain ⟨-, hmem, -, hround⟩ := pouRegion_mem_facts (I := I) (M := M) α hŷ
      have happ := chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 0
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
          α ![] Jdx) (hR_sub hŷ)
      change tensorChartComponentOnModel (I := I) (M := M) g₀
          (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) α Jdx
          ((toEuclidean (E := E)).symm ŷ) =
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 0
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
            α ![] Jdx) ŷ
      rw [happ]
      rfl
  | succ m ih =>
      intro Jdx
      obtain ⟨C₂, C₁, C₀, hC₂s, hC₁s, hC₀s, hformula⟩ :=
        rawTensorConnLap_chartα_raw_eq_T₀_linear_formula (I := I) (M := M)
          g₀ 0 2 α ![] Jdx
      set Wm : (Fin 0 → Fin (Module.finrank ℝ E)) →
          (Fin 2 → Fin (Module.finrank ℝ E)) →
          ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
        fun Idx' Jdx' t ŷ => chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
            α Idx' Jdx') ŷ
        with hWm_def
      have hWm_aniso : ∀ (Idx' : Fin 0 → Fin (Module.finrank ℝ E))
          (Jdx' : Fin 2 → Fin (Module.finrank ℝ E)),
          DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T R (Wm Idx' Jdx') := by
        intro Idx' Jdx'
        have hIdx' : Idx' = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
          funext fun i0 => i0.elim0
        rw [hWm_def, hIdx']
        exact ih Jdx'
      have h2sum : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T R
          (fun t ŷ => ∑ c : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            C₂ c l ŷ * DifferentialGeometry.Analysis.dirDeriv
              (EuclideanSpace.single l 1)
              (DifferentialGeometry.Analysis.dirDeriv (EuclideanSpace.single c 1)
                (Wm ![] Jdx t)) ŷ) := by
        refine DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open Finset.univ
          (fun c _ => DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open
            Finset.univ (fun l _ => ?_))
        refine (DifferentialGeometry.Analysis.anisoOn_timeIndep hR_open
          ((hC₂s c l).mono hR_sub)).mul hR_open ?_
        exact ((hWm_aniso ![] Jdx).pdShift hR_open
          (EuclideanSpace.single c 1)).pdShift hR_open (EuclideanSpace.single l 1)
      have h1sum : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T R
          (fun t ŷ => ∑ Idx' : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin 2 → Fin (Module.finrank ℝ E),
            ∑ c : Fin (Module.finrank ℝ E),
            C₁ Idx' Jdx' c ŷ * DifferentialGeometry.Analysis.dirDeriv
              (EuclideanSpace.single c 1) (Wm Idx' Jdx' t) ŷ) := by
        refine DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open Finset.univ
          (fun Idx' _ => DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open
            Finset.univ (fun Jdx' _ =>
              DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open Finset.univ
                (fun c _ => ?_)))
        refine (DifferentialGeometry.Analysis.anisoOn_timeIndep hR_open
          ((hC₁s Idx' Jdx' c).mono hR_sub)).mul hR_open ?_
        exact (hWm_aniso Idx' Jdx').pdShift hR_open (EuclideanSpace.single c 1)
      have h0sum : DifferentialGeometry.Analysis.AnisotropicJointContDiffOn k T R
          (fun t ŷ => ∑ Idx' : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin 2 → Fin (Module.finrank ℝ E),
            C₀ Idx' Jdx' ŷ * Wm Idx' Jdx' t ŷ) := by
        refine DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open Finset.univ
          (fun Idx' _ => DifferentialGeometry.Analysis.anisoOn_finsetSum hR_open
            Finset.univ (fun Jdx' _ => ?_))
        refine (DifferentialGeometry.Analysis.anisoOn_timeIndep hR_open
          ((hC₀s Idx' Jdx').mono hR_sub)).mul hR_open ?_
        exact hWm_aniso Idx' Jdx'
      have hlap_aniso := (h2sum.add hR_open h1sum).add hR_open h0sum
      refine ((hWm_aniso ![] Jdx).sub hR_open hlap_aniso).congr hR_open _
        (fun t ht ŷ hŷ => ?_)
      obtain ⟨hbU, hbT, hbRI, hbround⟩ := pouRegion_mem_facts (I := I) (M := M) α hŷ
      set b : M := (extChartAt I α).symm (toEuclidean.symm ŷ) with hb_def
      have hb_supp : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α := by
        constructor
        · exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hbU))
        · rw [DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
            (I := I) α]
          exact (extChartAt I α).map_target hbT
      set Qm : SmoothCcTensor g₀ 0 2 :=
        oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
          (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) with hQm_def
      have hform := hformula Qm hb_supp
      have hte : (toEuclidean (E := E)) ((extChartAt I α) b) = ŷ := hbround
      have hpushed_succ : chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (m + 1)
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
            α ![] Jdx) ŷ
          = tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 Qm α ![] Jdx b -
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 Qm) α ![] Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ (hR_sub hŷ)]
        rw [oneMinusConnLapSmoothIter_succ, ← hQm_def]
        change tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 Qm) α ![] Jdx b = _
        rw [show oneMinusConnLapSmooth (I := I) g₀ 0 2 Qm =
            Qm - rawTensorConnLapSmooth (I := I) g₀ 0 2 Qm from rfl]
        exact tensorChartComponentRaw_sub_eq (I := I) (M := M) g₀ Qm
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 Qm) α ![] Jdx b
      change Wm ![] Jdx t ŷ -
          ((∑ c : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            C₂ c l ŷ * DifferentialGeometry.Analysis.dirDeriv (EuclideanSpace.single l 1)
              (DifferentialGeometry.Analysis.dirDeriv (EuclideanSpace.single c 1)
                (Wm ![] Jdx t)) ŷ) +
          (∑ Idx' : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin 2 → Fin (Module.finrank ℝ E),
            ∑ c : Fin (Module.finrank ℝ E),
            C₁ Idx' Jdx' c ŷ * DifferentialGeometry.Analysis.dirDeriv
              (EuclideanSpace.single c 1) (Wm Idx' Jdx' t) ŷ) +
          (∑ Idx' : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin 2 → Fin (Module.finrank ℝ E),
            C₀ Idx' Jdx' ŷ * Wm Idx' Jdx' t ŷ)) =
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (m + 1)
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
            α ![] Jdx) ŷ
      rw [hpushed_succ, hform, hte]
      have hWm_b : Wm ![] Jdx t ŷ
          = tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 Qm α ![] Jdx b := by
        simp only [hWm_def]
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ (hR_sub hŷ)]
      rw [← hWm_b]
      simp only [hQm_def, hWm_def, euclidPartial_eq_pdDir]

set_option maxHeartbeats 1600000 in
private theorem reconFOIter_rawChartComponent_jointContMDiffOn_pou
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (m : ℕ) (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (k : ℕ)
      (fun p : M × ℝ =>
        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)))
          α ![] Jdx p.1)
      ({x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
        Set.Icc (0 : ℝ) T) := by
  classical
  set U : Set M :=
    {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} with hU_def
  set R : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' U) with hR_def
  have hR_sub : R ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouRegion_subset_chartTargetEuclid (I := I) (M := M) α
  have hU_src : U ⊆ (chartAt H α).source := by
    intro x hx
    refine (chartAtlasPOU_isSubordinate (I := I) (M := M) α) ?_
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hx))
  set G : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun q => chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
          (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F q.1) hδ_lt (hδ q.1)))
        α ![] Jdx) q.2 with hG_def
  have hG : ContDiffOn ℝ (k : ℕ) G (Set.Icc (0 : ℝ) T ×ˢ R) :=
    (anisoOn_pushed_oneMinusConnLapIter_reconFOPath (I := I) (M := M) g₀ g_bg hT k F
      hδ_lt hδ φ hφ_smooth hcoeff hmodemass α m Jdx).joint
  set f : M × ℝ → ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun p : M × ℝ => (p.2, toEuclidean (E := E) ((extChartAt I α) p.1)) with hf_def
  have hf_smooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (k : ℕ) f
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_snd ?_
    have hchart : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (k : ℕ)
        (fun p : M × ℝ => extChartAt I α p.1) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_fst
        (fun p hp => hU_src hp.1)).of_le (by exact_mod_cast le_top)
    exact (toEuclidean (E := E)).toContinuousLinearMap.contMDiff.comp_contMDiffOn hchart
  have hmaps : Set.MapsTo f (U ×ˢ Set.Icc (0 : ℝ) T) (Set.Icc (0 : ℝ) T ×ˢ R) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨ht, ⟨(extChartAt I α) x, ⟨x, hx, rfl⟩, rfl⟩⟩
  have heq : Set.EqOn
      (fun p : M × ℝ =>
        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)))
          α ![] Jdx p.1)
      (G ∘ f) (U ×ˢ Set.Icc (0 : ℝ) T) := by
    rintro ⟨x, t⟩ ⟨hx, -⟩
    have hx_src : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hU_src hx
    have hxR : toEuclidean (E := E) ((extChartAt I α) x) ∈ R :=
      ⟨(extChartAt I α) x, ⟨x, hx, rfl⟩, rfl⟩
    simp only [Function.comp, hG_def, hf_def]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ (hR_sub hxR),
      (toEuclidean (E := E)).symm_apply_apply, (extChartAt I α).left_inv hx_src]
  intro q hq
  refine (ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq))
  have hGf : ContDiffWithinAt ℝ (k : ℕ) G (Set.Icc (0 : ℝ) T ×ˢ R) (f q) :=
    hG.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem sectionPath_jointContMDiffOn_of_rawChartComponent_pou
    (g : SmoothRiemannianMetric I M) {T : ℝ} (k : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (hraw : ∀ (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (k : ℕ)
        (fun p : M × ℝ =>
          tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α ![] Jdx p.1)
        ({x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
          Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((T_rep p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, -⟩
  obtain ⟨α, hα_pos⟩ :=
    (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x₀)
  have hU_open : IsOpen
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} :=
    isOpen_lt continuous_const (chartAtlasPOU I M α).contMDiff.continuous
  have hU_src : {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ⊆
      (chartAt H α).source := by
    intro x hx
    refine (chartAtlasPOU_isSubordinate (I := I) (M := M) α) ?_
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hx))
  refine ⟨{x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
    (Set.univ : Set ℝ), hU_open.prod isOpen_univ, ⟨hα_pos, Set.mem_univ _⟩, ?_⟩
  have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ({x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
        (Set.univ : Set ℝ)) =
      {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
        Set.Icc (0 : ℝ) T := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hSum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α Q.1 Q.2 p.1 •
          tensorChartBasisElement (E := E) 0 2 Q.1 Q.2)
      ({x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
        Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_finset_sum (fun Q _ => ?_)
    have hQ1 : Q.1 = (![] : Fin 0 → Fin (Module.finrank ℝ E)) := funext fun i0 => i0.elim0
    have hrawQ := hraw α Q.2
    rw [hQ1]
    exact hrawQ.smul contMDiffOn_const
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        exact hU_src hx₀src
  have hsource : (⟨p₀.1, (T_rep p₀.2).toSection p₀.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfibeq : ∀ p : M × ℝ,
      p.1 ∈ {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} →
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
        ⟨p.1, (T_rep p.2).toSection p.1⟩).2 =
        ∑ Q : CompIdx E 0 2,
          tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α Q.1 Q.2 p.1 •
            tensorChartBasisElement (E := E) 0 2 Q.1 Q.2 := by
    intro p hpU
    have hpx : p.1 ∈ (chartAt H α).source := hU_src hpU
    have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hpx
    have h1 : ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
        ⟨p.1, (T_rep p.2).toSection p.1⟩).2 =
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt
          ℝ p.1 ((T_rep p.2).toSection p.1) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    rw [h1, toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 (T_rep p.2) α hpx,
      map_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [map_smul]
    congr 1
    have hbs : chartBasisFiberSection (I := I) (M := M) 0 2 α Q p.1 =
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).symmL ℝ p.1
          (tensorChartBasisElement (E := E) 0 2 Q.1 Q.2) := rfl
    rw [hbs]
    exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hpbase _
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
          ⟨p.1, (T_rep p.2).toSection p.1⟩).2)
      ({x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
        Set.Icc (0 : ℝ) T) p₀ := by
    refine (hSum p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact hfibeq p hp.1
    · exact hfibeq p₀ hx₀src
  exact ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ((k : ℕ) : WithTop ℕ∞))
    (f := fun p : M × ℝ => (⟨p.1, (T_rep p.2).toSection p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := {x : M | 0 < ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x} ×ˢ
      Set.Icc (0 : ℝ) T) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

end IterLaplacianInduction

end FiniteOrderAnisotropicReconstruction

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckRHSReconSectionFO_oneMinusConnLapIter_path_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (m : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
          (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
  sectionPath_jointContMDiffOn_of_rawChartComponent_pou (I := I) (M := M) (T := T) g₀ k
    (fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
      (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
    (fun α Jdx =>
      reconFOIter_rawChartComponent_jointContMDiffOn_pou (I := I) (M := M)
        g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass m α Jdx)

end FiniteOrderReconJetEnergy

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckRHSReconSectionFO_pathCoeff_timeContDiff_spectralJetMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j
                (fun s => tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                    (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set Rec : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun s => deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s) with hRec
  have hchild : ∀ m : ℕ, ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m (Rec p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
    fun m => deTurckRHSReconSectionFO_oneMinusConnLapIter_path_jointContMDiffOn
      (I := I) (M := M) g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass m
  have hrec_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((Rec p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have h0 := hchild 0
    simpa only [oneMinusConnLapSmoothIter_zero] using h0
  have hkinf : ((k : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hconj1 : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec t)) i)
        (Set.Icc (0 : ℝ) T) := by
    intro i
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig
    have heigM := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_contMDiff
      (I := I) (M := M) g₀ 0 2 i
    have heigP : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
          (eig.toSection p.1)) :=
      heigM.comp contMDiff_fst
    have hpairing : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((k : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            (eig.toFun p.1) ((Rec p.2).toFun p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      tensorInnerPointwise_pair_section_jointContMDiffOn (I := I) (M := M) hkinf g₀
        (fun _ : ℝ => eig) Rec ((heigP.contMDiffOn).of_le hkinf) hrec_joint
    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl
    have hint := contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder μ hT k
      (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x (eig.toFun x) ((Rec t).toFun x)) hpairing
    exact hint.congr (fun t _ => hcoeffInt (Rec t))
  refine ⟨hconj1, ?_⟩
  intro j hj σ hσ
  have hjW : ((j : ℕ) : WithTop ℕ∞) ≤ ((k : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  set sW : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < sW := by rw [hsW_def]; linarith
  obtain ⟨m, hm⟩ := exists_nat_ge ((σ + sW) / 2)
  have h2m : σ + sW ≤ ((2 * m : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨C, hC⟩ := smoothCcTensorPath_eigenPairing_timeJet_uniform_bound (I := I) (M := M)
    g₀ hT k j hj (fun s => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m (Rec s)) (hchild m)
  refine ⟨fun i => C ^ 2 * tensorSobolevWeight (I := I) (M := M) i (-sW),
    (tensorEigen_summable_negpow (I := I) (M := M) g₀ sW hsW_gt).mul_left (C ^ 2), ?_⟩
  intro i t ht
  change tensorSobolevWeight (I := I) (M := M) i σ *
      (iteratedDerivWithin j
        (fun s => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
        (Set.Icc (0 : ℝ) T) t) ^ 2 ≤
    C ^ 2 * tensorSobolevWeight (I := I) (M := M) i (-sW)
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hQcoeff : ∀ s : ℝ,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m (Rec s))) i
        = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m *
            tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i := fun s =>
    tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ hc (Rec s) i m
  have hjet_scaled : iteratedDerivWithin j
      (fun s => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m (Rec s))) i)
      (Set.Icc (0 : ℝ) T) t
      = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m *
        iteratedDerivWithin j
          (fun s => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
          (Set.Icc (0 : ℝ) T) t := by
    rw [iteratedDerivWithin_congr (fun s _ => hQcoeff s) ht]
    exact iteratedDerivWithin_const_mul ht hUD
      ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m)
      (((hconj1 i) t ht).of_le hjW)
  have hCbound := hC i t ht
  have habs := abs_le.mp hCbound
  have hsq : ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m *
      iteratedDerivWithin j
        (fun s => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
        (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ C ^ 2 := by
    rw [← hjet_scaled]
    exact sq_le_sq' habs.1 habs.2
  have hw2m : tensorSobolevWeight (I := I) (M := M) i ((2 * m : ℕ) : ℝ)
      = ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m) ^ 2 := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 m, pow_mul]
  have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) i (-sW) *
        tensorSobolevWeight (I := I) (M := M) i (σ + sW) := by
    rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-sW) (σ + sW)]
    ring_nf
  have hmono : tensorSobolevWeight (I := I) (M := M) i (σ + sW) ≤
      tensorSobolevWeight (I := I) (M := M) i ((2 * m : ℕ) : ℝ) :=
    tensorSobolevWeight_mono (I := I) (M := M) i h2m
  have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-sW) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (-sW)
  calc tensorSobolevWeight (I := I) (M := M) i σ *
      (iteratedDerivWithin j
        (fun s => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
        (Set.Icc (0 : ℝ) T) t) ^ 2
      = tensorSobolevWeight (I := I) (M := M) i (-sW) *
          (tensorSobolevWeight (I := I) (M := M) i (σ + sW) *
            (iteratedDerivWithin j
              (fun s => tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
              (Set.Icc (0 : ℝ) T) t) ^ 2) := by
        rw [hsplit]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i (-sW) *
          (tensorSobolevWeight (I := I) (M := M) i ((2 * m : ℕ) : ℝ) *
            (iteratedDerivWithin j
              (fun s => tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
              (Set.Icc (0 : ℝ) T) t) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hmono (sq_nonneg _)) hwneg_nn
    _ = tensorSobolevWeight (I := I) (M := M) i (-sW) *
          (((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m *
            iteratedDerivWithin j
              (fun s => tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
              (Set.Icc (0 : ℝ) T) t) ^ 2) := by
        rw [hw2m]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i (-sW) * C ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hwneg_nn
    _ = C ^ 2 * tensorSobolevWeight (I := I) (M := M) i (-sW) := by ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckRHSReconSectionFO_path_timeJet_mixed_regularity
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∧
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ j : ℕ, j ≤ k → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
        (Rjet j t).toFun x = iteratedDerivWithin j
          (fun s => (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x)
          (Set.Icc (0 : ℝ) T) t) ∧
      (∀ j : ℕ, j ≤ k → ∀ κ : ℕ,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
          ((0 : ℕ) : WithTop ℕ∞)
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
            ((oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j p.2)).toSection p.1))
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) := by
  classical
  obtain ⟨hcoeffCk, hjetmass⟩ :=
    deTurckRHSReconSectionFO_pathCoeff_timeContDiff_spectralJetMass (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hext : ∀ i, ∃ G : ℝ → ℝ, ContDiff ℝ (k : ℕ) G ∧
      Set.EqOn G (fun t => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T) :=
    fun i => DifferentialGeometry.Analysis.exists_contDiff_extend_of_contDiffOn_Icc hT k _
      (hcoeffCk i)
  choose chat hchat_smooth hchat_eq using hext
  have hjets_global : ∀ i (j : ℕ), j ≤ k → ∀ t ∈ Set.Icc (0 : ℝ) T,
      iteratedDeriv j (chat i) t =
        iteratedDerivWithin j
          (fun s => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
          (Set.Icc (0 : ℝ) T) t := by
    intro i j hj t ht
    rw [← iteratedDerivWithin_eq_iteratedDeriv hUD
      ((hchat_smooth i).contDiffAt.of_le (by exact_mod_cast hj)) ht]
    exact iteratedDerivWithin_congr (hchat_eq i) ht
  have hRcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
          chat i t :=
    fun t ht i => (hchat_eq i ht).symm
  have hRmass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (chat i) t) ^ 2 ≤ B i := by
    intro j hj σ hσ
    obtain ⟨B, hB1, hB2⟩ := hjetmass j hj σ hσ
    refine ⟨B, hB1, fun i t ht => ?_⟩
    rw [hjets_global i j hj t ht]
    exact hB2 i t ht
  have h1 := spectralPathFO_section_jointContMDiffOn_local (I := I) (M := M) g₀ hT k
    (fun s => deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
    chat hchat_smooth hRcoeff hRmass
  have hRjet_ex : ∀ (j : ℕ) (t : ℝ), ∃ S : SmoothCcTensor g₀ 0 2,
      j ≤ k → t ∈ Set.Icc (0 : ℝ) T →
        ∀ i, tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          iteratedDeriv j (chat i) t := by
    intro j t
    by_cases h : j ≤ k ∧ t ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨hj, ht⟩ := h
      have hm : ∀ σ : ℝ, 0 ≤ σ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv j (chat i) t) ^ 2 ≤ B i := by
        intro σ hσ
        obtain ⟨B, hB1, hB2⟩ := hRmass j hj σ hσ
        exact ⟨B, hB1, fun i => hB2 i t ht⟩
      obtain ⟨S, hS⟩ := exists_smoothCcTensor_of_allOrder_spectralMass_local (I := I) (M := M)
        g₀ (fun i => iteratedDeriv j (chat i) t) hm
      exact ⟨S, fun _ _ => hS⟩
    · exact ⟨0, fun hj ht => absurd ⟨hj, ht⟩ h⟩
  choose Rjet hRjet using hRjet_ex
  refine ⟨h1, Rjet, ?_, ?_⟩
  · intro j hj t ht x
    exact spectralPathFO_toFun_timeJet_eq_of_coeff_jets_local (I := I) (M := M) g₀ hT k
      (fun s => deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
      chat hchat_smooth hRcoeff hRmass j hj ht (Rjet j t) (hRjet j t hj ht) x
  · intro j hj κ
    have hφκ_smooth : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        ContDiff ℝ ((0 : ℕ) : ℕ)
          (fun t => (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
            iteratedDeriv j (chat i) t) := by
      intro i
      rw [show (((0 : ℕ) : ℕ) : WithTop ℕ∞) = (0 : WithTop ℕ∞) from rfl, contDiff_zero]
      exact continuous_const.mul
        (ContDiff.continuous_iteratedDeriv j (hchat_smooth i) (by exact_mod_cast hj))
    have hκcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j t))) i =
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
              iteratedDeriv j (chat i) t := by
      intro t ht i
      rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ hc
        (Rjet j t) i κ, hRjet j t hj ht i]
    have hκmass : ∀ (j' : ℕ), j' ≤ 0 → ∀ (σ : ℝ), 0 ≤ σ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv j'
                  (fun u => (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
                    iteratedDeriv j (chat i) u) t) ^ 2 ≤ B i := by
      intro j' hj' σ hσ
      have hj'0 : j' = 0 := Nat.le_zero.mp hj'
      subst hj'0
      obtain ⟨B, hB1, hB2⟩ := hRmass j hj (σ + ((2 * κ : ℕ) : ℝ)) (by positivity)
      refine ⟨B, hB1, fun i t ht => ?_⟩
      rw [iteratedDeriv_zero]
      have hwsplit : tensorSobolevWeight (I := I) (M := M) i σ *
          ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
            iteratedDeriv j (chat i) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ + ((2 * κ : ℕ) : ℝ)) *
            (iteratedDeriv j (chat i) t) ^ 2 := by
        rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ ((2 * κ : ℕ) : ℝ)]
        have hw2κ : tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ)
            = ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ) ^ 2 := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast, mul_comm 2 κ, pow_mul]
        rw [hw2κ, mul_pow]
        ring
      rw [hwsplit]
      exact hB2 i t ht
    exact spectralPathFO_section_jointContMDiffOn_local (I := I) (M := M) g₀ hT 0
      (fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j t))
      (fun i t => (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
        iteratedDeriv j (chat i) t)
      hφκ_smooth hκcoeff hκmass

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckRHSReconSectionFO_eigenPairing_jointCk_timeJet_realization
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((k : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
              (I := I) (M := M) g₀ 0 2 i).toFun p.1)
            ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) ∧
    (∀ j : ℕ, j ≤ k → ∃ Rjt : ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        iteratedDerivWithin j
            (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ∧
      (∀ κ : ℕ, ContinuousOn
        (fun t => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))‖ ^ 2)
        (Set.Icc (0 : ℝ) T))) := by
  classical
  obtain ⟨hjointP, Rjet, hRjet_eq, hRjet_lap⟩ :=
    deTurckRHSReconSectionFO_path_timeJet_mixed_regularity (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hkinf : ((k : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hpairing : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((k : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
              (I := I) (M := M) g₀ 0 2 i).toFun p.1)
            ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have heigM := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_contMDiff
      (I := I) (M := M) g₀ 0 2 i
    have heigP : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
          ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
            (I := I) (M := M) g₀ 0 2 i).toSection p.1)) :=
      heigM.comp contMDiff_fst
    exact tensorInnerPointwise_pair_section_jointContMDiffOn (I := I) (M := M) hkinf g₀
      (fun _ : ℝ => Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
        (I := I) (M := M) g₀ 0 2 i)
      (fun s : ℝ => deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
      ((heigP.contMDiffOn).of_le hkinf) hjointP
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  refine ⟨hpairing, ?_⟩
  intro j hjk
  have hjW : ((j : ℕ) : WithTop ℕ∞) ≤ ((k : ℕ) : WithTop ℕ∞) := by exact_mod_cast hjk
  refine ⟨Rjet j, ?_, ?_⟩
  · intro i t ht
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig
    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl
    have hγfam : ∀ x : M, ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞)
        (fun s => (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x)
        (Set.Icc (0 : ℝ) T) t := fun x =>
      (smoothCcTensor_path_toFun_contDiffWithinAt (I := I) (M := M) g₀
        (fun s => deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
        hjointP x ht).of_le hjW
    have hfib : ∀ x : M,
        iteratedDerivWithin j
            (fun s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
              (I := I) (M := M) g₀ 0 2 x (eig.toFun x)
              ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x))
            (Set.Icc (0 : ℝ) T) t
          = DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
              (eig.toFun x) ((Rjet j t).toFun x) := by
      intro x
      have hL := clm_comm_iteratedDerivWithin_finiteOrder
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x))
        (fun s => (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x)
        hT ht j (hγfam x)
      rw [hRjet_eq j hjk t ht x]
      exact hL
    have hLHSfun : (fun s : ℝ => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
        = (fun s : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x (eig.toFun x)
            ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x) ∂μ) :=
      funext fun s => hcoeffInt (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
    have hinter := iteratedDerivWithin_integral_param_Icc_finiteOrder μ hT j
      (fun x s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x (eig.toFun x)
        ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x))
      ((hpairing i).of_le hjW) t ht
    rw [hLHSfun, hinter, hcoeffInt (Rjet j t)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hfib x))
  · intro κ
    set Sfam : ℝ → SmoothCcTensor g₀ 0 2 :=
      fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j t) with hSfam
    have hpair0 := tensorInnerPointwise_pair_section_jointContMDiffOn (I := I) (M := M)
      (N := ((0 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_top) g₀ Sfam Sfam
      (hRjet_lap j hjk κ) (hRjet_lap j hjk κ)
    have hnormeq : (fun t : ℝ => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam t)‖ ^ 2)
        = fun t : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x) ∂μ := by
      funext t
      rw [SmoothCcTensor.norm_toL2,
        Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self]
      rfl
    have hcd := contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder μ hT 0
      (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x)) hpair0
    have hfinal : ContinuousOn
        (fun t => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam t)‖ ^ 2)
        (Set.Icc (0 : ℝ) T) := by
      rw [hnormeq]
      exact hcd.continuousOn
    exact hfinal

private theorem deTurckRHSRecon_pathCoeff_finiteOrder_timeContDiff_withinMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j
                (fun s => tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                    (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i) := by
  classical
  obtain ⟨hjoint, hjet⟩ :=
    deTurckRHSReconSectionFO_eigenPairing_jointCk_timeJet_realization (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  refine ⟨?_, ?_⟩
  · intro i
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig
    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl
    refine ContDiffOn.congr ?_
      (fun t _ => hcoeffInt (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
    exact contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder μ hT k
      (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M)
        g₀ 0 2 x (eig.toFun x)
        ((deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)).toFun x))
      (hjoint i)
  · intro j hjk σ hσ
    obtain ⟨Rjt, hRjt_coeff, hRjt_norm⟩ := hjet j hjk
    set s : ℝ := (weylSobolevExp (E := E) : ℝ) + 1 with hs_def
    have hs : (weylSobolevExp (E := E) : ℝ) < s := by rw [hs_def]; linarith
    obtain ⟨κ, hκ⟩ := exists_nat_ge ((σ + s) / 2)
    have hκ2 : σ + s ≤ ((2 * κ : ℕ) : ℝ) := by
      push_cast
      have : (σ + s) / 2 ≤ (κ : ℝ) := hκ
      linarith
    obtain ⟨t₀, ht₀_mem, ht₀_max⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT.le) (hRjt_norm κ)
    set C : ℝ := ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t₀))‖ ^ 2 with hC_def
    have hC : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ) *
            (tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2 ≤ C := by
      intro i t ht
      have hweq : tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2 =
          (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))) i) ^ 2 := by
        rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M)
            g₀ hc (Rjt t) i κ,
          mul_pow]
        congr 1
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast, mul_comm 2 κ, pow_mul, sq]
      rw [hweq]
      have hsummable := tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t)))
      have hle_tsum : (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))) i) ^ 2 ≤
          ∑' i' : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
            (tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))) i') ^ 2 :=
        hsummable.le_tsum i (fun i' _ => sq_nonneg _)
      rw [tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t)))] at hle_tsum
      exact le_trans hle_tsum (ht₀_max ht)
    refine ⟨fun i => C * tensorSobolevWeight (I := I) (M := M) i (-s),
      (tensorEigen_summable_negpow (I := I) (M := M) g₀ s hs).mul_left C, ?_⟩
    intro i t ht
    rw [hRjt_coeff i t ht]
    have hnegnn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-s) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (-s)
    have hmono : tensorSobolevWeight (I := I) (M := M) i (σ + s) ≤
        tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ) :=
      tensorSobolevWeight_mono (I := I) (M := M) i hκ2
    have hadd : tensorSobolevWeight (I := I) (M := M) i σ =
        tensorSobolevWeight (I := I) (M := M) i (-s) *
          tensorSobolevWeight (I := I) (M := M) i (σ + s) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-s) (σ + s)]
      ring_nf
    calc tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-s) *
            (tensorSobolevWeight (I := I) (M := M) i (σ + s) *
              (tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2) := by
          rw [hadd]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-s) * C := by
          refine mul_le_mul_of_nonneg_left ?_ hnegnn
          refine le_trans (mul_le_mul_of_nonneg_right hmono (sq_nonneg _)) ?_
          exact hC i t ht
      _ = C * tensorSobolevWeight (I := I) (M := M) i (-s) := by ring

private theorem deTurckRemainder_pathCoeff_finiteOrder_timeContDiff_withinMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j
                (fun s => tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                    (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨hrecon_smooth, hrecon_mass⟩ :=
    deTurckRHSRecon_pathCoeff_finiteOrder_timeContDiff_withinMass (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  set reconRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hreconRaw_def
  set rawRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (DifferentialGeometry.Integral.Connection.rawTensorConnLapSmooth
          (I := I) g₀ 0 2 (F s))) i with hrawRaw_def
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hcpath_def
  have hsplit : ∀ i s, cpath i s = reconRaw i s - rawRaw i s := by
    intro i s
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
          = deTurckRHSReconSectionFiniteOrder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
            - DifferentialGeometry.Integral.Connection.rawTensorConnLapSmooth
                (I := I) g₀ 0 2 (F s) := rfl
    simp only [hcpath_def, hreconRaw_def, hrawRaw_def]
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  have hrecon_cd : ∀ i, ContDiffOn ℝ (k : ℕ) (reconRaw i) (Set.Icc (0 : ℝ) T) :=
    hrecon_smooth
  have hraw_eqOn : ∀ i, Set.EqOn (rawRaw i)
      (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) := by
    intro i s hs
    simp only [hrawRaw_def]
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F s) i,
      hcoeff s hs i]
  have hraw_cd : ∀ i, ContDiffOn ℝ (k : ℕ) (rawRaw i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine ContDiffOn.congr ?_ (hraw_eqOn i)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn
  refine ⟨?_, ?_⟩
  · intro i
    exact ContDiffOn.congr ((hrecon_cd i).sub (hraw_cd i)) (fun t _ => hsplit i t)
  · intro j hjk σ hσ
    obtain ⟨Brecon, hBrecon_sum, hBrecon_le⟩ := hrecon_mass j hjk σ hσ
    obtain ⟨Braw, hBraw_sum, hBraw_le⟩ := hmodemass j hjk (σ + 2) (by linarith)
    refine ⟨fun i => 2 * Brecon i + 2 * Braw i,
      (hBrecon_sum.mul_left 2).add (hBraw_sum.mul_left 2), ?_⟩
    intro i t ht
    have hUDO : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
    have hcds : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (reconRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hrecon_cd i) t ht).of_le (by exact_mod_cast hjk)
    have hcdr : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (rawRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hraw_cd i) t ht).of_le (by exact_mod_cast hjk)
    have hderivEq : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
        iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t -
          iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t := by
      have hcongr : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => reconRaw i s - rawRaw i s)
            (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (fun s _ => hsplit i s) ht
      rw [hcongr]
      have hsub := iteratedDerivWithin_sub (f := reconRaw i) (g := rawRaw i)
        (n := j) ht hUDO hcds hcdr
      simpa only [Pi.sub_apply] using hsub
    have hrawDerivEq : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
        -i.lambda * iteratedDeriv j (φ i) t := by
      have hcongr : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (hraw_eqOn i) ht
      rw [hcongr,
        iteratedDerivWithin_const_mul ht hUDO (-i.lambda)
          (((hφ_smooth i).contDiffOn.of_le (by exact_mod_cast hjk)) t ht),
        iteratedDerivWithin_eq_iteratedDeriv hUDO
          ((hφ_smooth i).contDiffAt.of_le (by exact_mod_cast hjk)) ht]
    rw [hderivEq]
    set a : ℝ := iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t with ha_def
    set b : ℝ := iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t with hb_def
    have hwσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    have hsq : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
    have hweighted : tensorSobolevWeight (I := I) (M := M) i σ * (a - b) ^ 2 ≤
        2 * (tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq hwσ_nn
      nlinarith [this]
    refine le_trans hweighted ?_
    have hterm_recon : tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2 ≤ Brecon i :=
      hBrecon_le i t ht
    have hterm_raw : tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2 ≤ Braw i := by
      have hbsq : b ^ 2 = i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2 := by
        rw [hrawDerivEq]; ring
      have hlam_sq_le : i.lambda ^ 2 ≤ tensorSobolevWeight (I := I) (M := M) i 2 := by
        have hw2 : tensorSobolevWeight (I := I) (M := M) i 2 = (1 + i.lambda) ^ 2 := by
          unfold tensorSobolevWeight
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hw2]
        have hlam_nn : 0 ≤ i.lambda := tensor_lambda_nonneg (I := I) (M := M) i
        nlinarith [hlam_nn]
      have hmm : tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          (iteratedDeriv j (φ i) t) ^ 2 ≤ Braw i := hBraw_le i t ht
      have hsplitw : tensorSobolevWeight (I := I) (M := M) i (σ + 2) =
          tensorSobolevWeight (I := I) (M := M) i σ *
            tensorSobolevWeight (I := I) (M := M) i 2 :=
        tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2
      have hdjsq_nn : 0 ≤ (iteratedDeriv j (φ i) t) ^ 2 := sq_nonneg _
      calc tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ *
              (i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2) := by rw [hbsq]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (tensorSobolevWeight (I := I) (M := M) i 2 *
                (iteratedDeriv j (φ i) t) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hwσ_nn
            exact mul_le_mul_of_nonneg_right hlam_sq_le hdjsq_nn
        _ = tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv j (φ i) t) ^ 2 := by rw [hsplitw]; ring
        _ ≤ Braw i := hmm
    nlinarith [hterm_recon, hterm_raw]

private theorem deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ (ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2),
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ψ i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i) ∧
      (∀ (j : ℕ), j ≤ k → ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        iteratedDeriv j (ψ i) t =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (q : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ K) := by
  classical
  obtain ⟨hcpath_smooth, hcpath_mass⟩ :=
    deTurckRemainder_pathCoeff_finiteOrder_timeContDiff_withinMass (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hext : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ∃ G : ℝ → ℝ, ContDiff ℝ (k : ℕ) G ∧
        Set.EqOn G
          (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
          (Set.Icc (0 : ℝ) T) := fun i =>
    DifferentialGeometry.Analysis.exists_contDiff_extend_of_contDiffOn_Icc hT k _ (hcpath_smooth i)
  choose ψ hψ_cd hψ_eqOn using hext
  have hconstruct : ∀ (j : ℕ) (t : ℝ),
      ∃ S : SmoothCcTensor g₀ 0 2,
        (j ≤ k → t ∈ Set.Icc (0 : ℝ) T → ∀ i,
          tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
            iteratedDerivWithin j
              (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
              (Set.Icc (0 : ℝ) T) t) := by
    intro j t
    by_cases hjk : j ≤ k
    · by_cases ht : t ∈ Set.Icc (0 : ℝ) T
      · obtain ⟨S, hS⟩ := exists_smoothCcTensor_of_allOrder_spectralMass_local (I := I) (M := M) g₀
          (fun i => iteratedDerivWithin j
            (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t)
          (fun σ hσ => by
            obtain ⟨B, hBs, hBle⟩ := hcpath_mass j hjk σ hσ
            exact ⟨B, hBs, fun i => hBle i t ht⟩)
        exact ⟨S, fun _ _ i => hS i⟩
      · exact ⟨0, fun _ ht' => absurd ht' ht⟩
    · exact ⟨0, fun hjk' => absurd hjk' hjk⟩
  choose Rjet hRjet using hconstruct
  have hbridge : ∀ (j : ℕ), j ≤ k → ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      iteratedDeriv j (ψ i) t =
        iteratedDerivWithin j
          (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
          (Set.Icc (0 : ℝ) T) t := by
    intro j hjk i t ht
    have hcongr := iteratedDerivWithin_congr (n := j) (hψ_eqOn i) ht
    have heq : iteratedDerivWithin j (ψ i) (Set.Icc (0 : ℝ) T) t = iteratedDeriv j (ψ i) t :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
        ((hψ_cd i).contDiffAt.of_le (by exact_mod_cast hjk)) ht
    rw [← heq, hcongr]
  refine ⟨ψ, Rjet, hψ_cd, ?_, ?_, ?_⟩
  · intro i t ht
    exact hψ_eqOn i ht
  · intro j hjk i t ht
    rw [hbridge j hjk i t ht]
    exact (hRjet j t hjk ht i).symm
  · intro j hjk q
    obtain ⟨C, hC_nn, hCle⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * q)
    obtain ⟨B, hBs, hBle⟩ := hcpath_mass j hjk ((2 * q : ℕ) : ℝ) (by positivity)
    refine ⟨C * Real.sqrt (∑' i, B i),
      mul_nonneg hC_nn (Real.sqrt_nonneg _), fun t ht => ?_⟩
    have hptwise : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((2 * q : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)).coeff i) ^ 2 ≤
          B i := by
      intro i
      have hco : (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)).coeff i =
          iteratedDerivWithin j
            (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t := by
        rw [smoothCcToTensorHs_coeff]; exact hRjet j t hjk ht i
      rw [hco]; exact hBle i t ht
    have hnorm_le :
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)‖ ≤
          Real.sqrt (∑' i, B i) := by
      rw [tensorHs.norm_eq_sqrt_tsum (I := I) (M := M)
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t))]
      exact Real.sqrt_le_sqrt (Summable.tsum_le_tsum hptwise
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)).weighted_summable)
        hBs)
    have hqmem : q ∈ Finset.range (2 * q + 1) := Finset.mem_range.mpr (by omega)
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖
        ≤ ∑ j' ∈ Finset.range (2 * q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖ :=
          Finset.single_le_sum
            (f := fun j' => ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖)
            (fun j' _ => norm_nonneg _) hqmem
      _ ≤ C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)‖ :=
          hCle (Rjet j t)
      _ ≤ C * Real.sqrt (∑' i, B i) := mul_le_mul_of_nonneg_left hnorm_le hC_nn

theorem deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a (F t) hδ_lt (hδ t)).coeff i = ψ i t) := by
  classical
  obtain ⟨ψ, Rjet, hψ_smooth, hψ_eq, hjet, hcovbnd⟩ :=
    deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection (I := I) (M := M)
      g₀ g_bg a ha_super hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  refine ⟨ψ, hψ_smooth, ?_, ?_⟩
  · intro j hj σ hσ
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ,
        σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) ≤ (2 * k' : ℕ) := by
      obtain ⟨k', hk'⟩ := exists_nat_gt (σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1))
      exact ⟨k', by push_cast; linarith⟩
    set σ' : ℝ := ((2 * k' : ℕ) : ℝ) with hσ'_def
    have hσσ' : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by rw [hσ'_def]; linarith
    obtain ⟨C, hC_nn, hCle⟩ :=
      exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum (I := I) (M := M) g₀ k'
    have hcovsum_bnd : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ≤ K := by
      have hbnds : ∀ q ∈ Finset.range (2 * k' + 1), ∃ Kq : ℝ, 0 ≤ Kq ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ Kq :=
        fun q _ => hcovbnd j hj q
      choose! Kq hKq_nn hKq using hbnds
      refine ⟨C * ∑ q ∈ Finset.range (2 * k' + 1), Kq q,
        mul_nonneg hC_nn (Finset.sum_nonneg (fun q hq => hKq_nn q hq)), ?_⟩
      intro t ht
      refine le_trans (hCle (Rjet j t)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hC_nn
      refine Finset.sum_le_sum (fun q hq => ?_)
      exact hKq q hq t ht
    obtain ⟨K, hK_nn, hKle⟩ := hcovsum_bnd
    refine ⟨fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2, ?_, ?_⟩
    · exact (tensorEigen_summable_negpow (I := I) (M := M) g₀ (σ' - σ) hσσ').mul_right (K ^ 2)
    · intro i t ht
      rw [hjet j hj i t ht]
      set u : ℝ := tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i with hu_def
      have hcoeff_eq : (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).coeff i = u := by
        rw [smoothCcToTensorHs_coeff]
      have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
      have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
          tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) *
            tensorSobolevWeight (I := I) (M := M) i σ' := by
        unfold tensorSobolevWeight
        rw [← Real.rpow_add hbase, show -(σ' - σ) + σ' = σ from by ring]
      have hterm_le : tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2 ≤ K ^ 2 := by
        have hmass : tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2 ≤
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ^ 2 := by
          rw [tensorHs.norm_sq_eq_tsum]
          have hsummable :=
            (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).weighted_summable
          have hle := hsummable.le_tsum i (fun i' _ =>
            mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i' σ') (sq_nonneg _))
          rw [hcoeff_eq] at hle
          exact hle
        refine le_trans hmass ?_
        have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ := norm_nonneg _
        have := hKle t ht
        nlinarith [this, hnn, hK_nn]
      calc tensorSobolevWeight (I := I) (M := M) i σ * u ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) *
              (tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2) := by rw [hsplit]; ring
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2 :=
            mul_le_mul_of_nonneg_left hterm_le
              (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  · intro t ht i
    rw [deTurckSmoothN_coeff]
    exact (hψ_eq i t ht).symm

theorem deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (_hT : 0 < T) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (_hd₂_le : d₂ ≤ T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (k : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i) := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set R₀ : ℝ := deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super with hR₀_def
  have hR₀_pos : 0 < R₀ := deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super
  have hmass0 : ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 (Nat.zero_le k) σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have := hBle i t ht
    rwa [iteratedDeriv_zero] at this
  have hsum_pt : ∀ t, t ∈ Set.Icc (0 : ℝ) d₂ →
      ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2) := by
    intro t ht σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => hBle i t ht) hBs
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  set ct : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => φ i t with hct_def
  have hreconstruct : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = φ i t := by
    intro t ht
    obtain ⟨B0, hB0s, hB0le⟩ := hmass0 0 le_rfl
    set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
      tensorHs_of_spectralMass_majorant (I := I) (M := M) (ct t) B0 hB0s
        (fun i => by
          have := hB0le i t ht
          simpa [hct_def] using this) with hv0_def
    set u : TensorL2 0 2 g₀ :=
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
    have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = φ i t := by
      intro i
      rw [hu_def, tensorHsToL2_tensorL2Coeff]
      simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff, hct_def]
    have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
      intro σ hσ
      refine (hsum_pt t ht σ hσ).congr (fun i => ?_)
      rw [hu_coeff i]
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
      allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
    refine ⟨S, fun i => ?_⟩
    have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
      rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
          = (S : TensorL2 0 2 g₀) from rfl, hS]
    rw [hSL2, hu_coeff i]
  choose! S₀ hS₀ using hreconstruct
  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Icc (0 : ℝ) d₂ then S₀ t else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    simp only [hF_def, ht, if_pos]
    exact hS₀ t ht i
  have hF_smoothCc_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hF_coeff t ht i
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) d₂) := by
    set σ : ℝ := (a : ℝ) + 2 with hσ_def
    set σ' : ℝ := σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) with hσ'_def
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmass0 σ' (by
      rw [hσ'_def, hσ_def]; positivity)
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g₀
      (σ := σ) (σ' := σ') ?_ (s := Set.Icc (0 : ℝ) d₂)
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)) φ
      hF_smoothCc_coeff (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum
      (fun i t ht => hCmaj_le i t ht)
    have : σ' - σ = ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by rw [hσ'_def]; ring
    rw [this]; linarith
  have hball_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (w t).coeff i = φ i t := by
      rw [MeasureTheory.ae_all_iff]
      intro i
      exact hw i
    have hae_mem : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        t ∈ Set.Icc (0 : ℝ) d₂ := MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hw_ball, hae_all, hae_mem] with t hwball_t htall htmem
    have heq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) = w t := by
      refine tensorHs.ext (funext fun i => ?_)
      rw [hF_smoothCc_coeff t htmem i, ← htall i]
    rw [heq]; exact hwball_t
  have hcont_norm : ContinuousOn
      (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖)
      (Set.Icc (0 : ℝ) d₂) := continuous_norm.comp_continuousOn hfield_cont
  have hball_pt : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    have hae_le : ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) d₂)),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ≤ R₀ := hball_ae
    have hg_cont : ContinuousOn
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ⊓ R₀)
        (Set.Icc (0 : ℝ) d₂) := hcont_norm.inf continuousOn_const
    have hfg : (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) d₂)]
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ⊓ R₀) := by
      filter_upwards [hae_le] with s hs
      exact (min_eq_left hs).symm
    have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hd₂_pos) hfg hcont_norm hg_cont
    intro t ht
    have hmin : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ⊓ R₀ := heq ht
    rw [hmin]; exact inf_le_right
  obtain ⟨δ, hδ_lt, hδ_all⟩ :
      ∃ δ : ℝ, δ < 1 ∧ ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (F t)) δ := by
    obtain ⟨hp_pos, hp_lt, hp_ball⟩ := Classical.choose_spec
      (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)
    have hsmoothZero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h0 : (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2) :=
        (zero_smul ℝ _).symm
      rw [h0, smoothCcToTensorHs_smul, zero_smul]
    refine ⟨(Classical.choose (deTurckSobolevNHa2_exists_of_super
      (I := I) (M := M) g₀ a ha_super)).2,
      lt_of_le_of_lt hp_lt (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)), fun t => ?_⟩
    by_cases ht : t ∈ Set.Icc (0 : ℝ) d₂
    · exact hp_ball (F t) (hball_pt t ht)
    · have hF0 : F t = 0 := by simp only [hF_def, ht, if_neg, not_false_iff]
      refine hp_ball (F t) ?_
      rw [hF0, hsmoothZero, norm_zero]
      exact hp_pos.le
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super hd₂_pos k F hδ_lt hδ_all φ hφ_smooth
      hF_coeff hφ_mass
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ j, (w t).coeff j = φ j t := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact hw j
  have hae_mem : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      t ∈ Set.Icc (0 : ℝ) d₂ := MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hae_all, hae_mem] with t htall htmem
  have hwF : w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, ← hF_smoothCc_coeff t htmem j]
  rw [hwF,
    deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super
      (F t) hδ_lt (hδ_all t) (by
        have hle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ :=
          hball_pt t htmem
        have hpf : (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1 = R₀ := rfl
        rw [hpf]; exact hle)]
  exact hψ_coeff t htmem i

theorem deTurckForcing_finiteOrderSmoothDriver
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T ∧
      ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
        (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
        (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
              tensorSobolevWeight (I := I) (M := M) i τ *
                  (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
        (∀ i, (fun t => (gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hs_cont, hs_mass, hball, hcoeff_id⟩ :=
    deTurckForcing_solCoeff_continuous_smallTimeBase (I := I) (M := M)
      g₀ a ha_super hT hT1 gforce hspatial
  choose c hc_cont hc_ae using hs_cont
  have hae_d : ∀ i, c i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) := fun i =>
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd_le) (hc_ae i)
  have hcont_pmc : ∀ i, ContinuousOn
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    (continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) gforce i) hT.le).mono (Set.Icc_subset_Icc le_rfl hd_le)
  have heqOn_d : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (ne_of_lt hd_pos) (hae_d i) (hc_cont i).continuousOn (hcont_pmc i)
  refine ⟨d, hd_pos, hd_le, ?_⟩
  have hsub : Set.Icc (0 : ℝ) d ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hd_le
  have hforce_coeff : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun t => (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  have hgforce_tmc : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  intro k
  induction k with
  | zero =>
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hT hd_pos hd_le
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball 0
        c
        (fun i => by rw [Nat.cast_zero, contDiff_zero]; exact hc_cont i)
        (fun j hj τ hτ => by
          obtain rfl := Nat.le_zero.mp hj
          obtain ⟨B, hBs, hBle⟩ := hs_mass τ hτ
          refine ⟨B, hBs, fun i t ht => ?_⟩
          rw [iteratedDeriv_zero, heqOn_d i ht]
          exact hBle i t ht)
        (fun i => (hcoeff_id i).trans (hae_d i).symm)
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩
  | succ k ih =>
    obtain ⟨fk, hfk_cont, hfk_mass, hfk_ae⟩ := ih
    obtain ⟨hφ_cont, hφ_mass⟩ :=
      perModeConv_finiteOrder_timeJet_spectralMass_gain (I := I) (M := M)
        g₀ hd_pos.le k fk hfk_cont hfk_mass
    have hw_coeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
      intro i
      have hfk_tmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (fk i) :=
        (hgforce_tmc i).symm.trans (hfk_ae i)
      have hbridge : (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
        exact perModeConv_timeL2_congr (T := d) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hfk_tmc ht
      exact (hcoeff_id i).trans hbridge
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hT hd_pos hd_le
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball (k + 1)
        (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
        hφ_cont hφ_mass hw_coeff
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
