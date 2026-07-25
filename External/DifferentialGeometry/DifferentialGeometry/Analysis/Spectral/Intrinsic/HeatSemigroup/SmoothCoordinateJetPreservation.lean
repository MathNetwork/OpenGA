import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel

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

theorem contDiffOn_Icc_scalar_globalExtend
    {T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ ∞ φ (Set.Icc (0 : ℝ) T)) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Set.EqOn φ ψ (Set.Icc (0 : ℝ) T) := by
  classical
  set K : Set ℝ := Metric.closedBall (0 : ℝ) 1 with hK_def
  have hK_cpt : IsCompact K := isCompact_closedBall (0 : ℝ) 1
  have hz₀ : (0 : ℝ) ∈ interior K := by
    rw [hK_def, interior_closedBall' (0 : ℝ) 1]
    exact Metric.mem_ball_self (by norm_num)
  have huncurry : ContDiffOn ℝ ∞ (Function.uncurry (fun (t : ℝ) (_ : ℝ) => φ t))
      (Set.Icc (0 : ℝ) T ×ˢ K) := by
    have hcomp : ContDiffOn ℝ ∞ (φ ∘ (Prod.fst : ℝ × ℝ → ℝ)) (Set.Icc (0 : ℝ) T ×ˢ K) :=
      hφ.comp contDiff_fst.contDiffOn Set.mapsTo_fst_prod
    exact hcomp
  obtain ⟨gext, V, hV_nhds, hgext_smooth, hgext_eq⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      (fun (t : ℝ) (_ : ℝ) => φ t) T hT K hK_cpt (0 : ℝ) hz₀ huncurry
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds hV_nhds
  refine ⟨fun t => gext t 0, ?_, ?_⟩
  · have hmaps : Set.MapsTo (fun t : ℝ => (t, (0 : ℝ))) (Set.univ : Set ℝ)
        ((Set.univ : Set ℝ) ×ˢ V) :=
      fun t _ => Set.mk_mem_prod (Set.mem_univ t) h0V
    have hpair : ContDiffOn ℝ ∞ (fun t : ℝ => (t, (0 : ℝ)))
        (Set.univ : Set ℝ) := (contDiff_fun_id.prodMk contDiff_const).contDiffOn
    have hcomp : ContDiffOn ℝ ∞ (Function.uncurry gext ∘ (fun t : ℝ => (t, (0 : ℝ))))
        (Set.univ : Set ℝ) := hgext_smooth.comp hpair hmaps
    refine contDiffOn_univ.mp ?_
    refine hcomp.congr (fun t _ => ?_)
    simp [Function.uncurry_apply_pair]
  · intro t ht
    have h := hgext_eq t ht 0 h0V
    exact h.symm

def JetSpectralMassControl
    (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ) (T : ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (φ i)) ∧
    (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)

noncomputable def deTurckRealizabilityRadius
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1

theorem deTurckRealizabilityRadius_pos
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    0 < deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super :=
  (Classical.choose_spec
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1

theorem perModeConv_sq_le_time_mul_integral' (lam : ℝ) (hlam : 0 ≤ lam)
    {c : ℝ → ℝ} (hc : Continuous c) {t : ℝ} (ht : 0 ≤ t) :
    (perModeConv lam c t) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 := by
  set k : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s))) * c s with hk_def
  have hk_cont : Continuous k := by fun_prop
  have hconv_eq : perModeConv lam c t = ∫ s in (0 : ℝ)..t, k s := by
    rw [perModeConv]
  have hCS : (∫ s in (0 : ℝ)..t, (1 : ℝ) * k s) ^ 2
      ≤ (∫ s in (0 : ℝ)..t, (1 : ℝ)) * ∫ s in (0 : ℝ)..t, (1 : ℝ) * (k s) ^ 2 :=
    weighted_cauchy_schwarz ht continuous_const hk_cont (fun _ _ => zero_le_one)
  simp only [one_mul] at hCS
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hCS
  have hk_sq_le : ∀ s ∈ Set.Icc (0 : ℝ) t, (k s) ^ 2 ≤ (c s) ^ 2 := by
    intro s hs
    have hexp : Real.exp (-(lam * (t - s))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs.1, hs.2, mul_nonneg hlam (sub_nonneg.mpr hs.2)])
    have hexp_nonneg : 0 ≤ Real.exp (-(lam * (t - s))) := (Real.exp_pos _).le
    rw [hk_def, mul_pow]
    have hsq_le_one : Real.exp (-(lam * (t - s))) ^ 2 ≤ 1 := by
      nlinarith [hexp, hexp_nonneg]
    nlinarith [sq_nonneg (c s), hsq_le_one]
  have hk_sq_int : (∫ s in (0 : ℝ)..t, (k s) ^ 2) ≤ ∫ s in (0 : ℝ)..t, (c s) ^ 2 := by
    refine intervalIntegral.integral_mono_on ht ?_ ?_ ?_
    · exact (hk_cont.pow 2).intervalIntegrable 0 t
    · exact (hc.pow 2).intervalIntegrable 0 t
    · exact hk_sq_le
  calc (perModeConv lam c t) ^ 2
      = (∫ s in (0 : ℝ)..t, k s) ^ 2 := by rw [hconv_eq]
    _ ≤ t * ∫ s in (0 : ℝ)..t, (k s) ^ 2 := hCS
    _ ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 :=
        mul_le_mul_of_nonneg_left hk_sq_int ht

theorem deTurckRemainder_path_timeJet_section
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
            (Set.Icc (0 : ℝ) T)) ∧
        (∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
              (Set.Icc (0 : ℝ) T) t =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
        (∀ (j q : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ K) := by
  classical
  obtain ⟨Rjet, hsmooth, hjet, hmass⟩ :=
    deTurckRemainder_path_coeff_timeJet_withMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  refine ⟨Rjet, hsmooth, hjet, ?_⟩
  intro j q
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q ≤ 2 * k := ⟨q, by omega⟩
  set σ' : ℝ := ((2 * k : ℕ) : ℝ) with hσ'_def
  have hσ'_nn : (0 : ℝ) ≤ σ' := by rw [hσ'_def]; positivity
  obtain ⟨B, hB_sum, hBle⟩ := hmass j σ' hσ'_nn
  obtain ⟨Csum, hCsum_nn, hCsum⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
  have hBtsum_nn : 0 ≤ ∑' i, B i :=
    tsum_nonneg (fun i =>
      le_trans (mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ') (sq_nonneg _))
        (hBle i 0 ⟨le_rfl, hT.le⟩))
  refine ⟨Csum * Real.sqrt (∑' i, B i), by positivity, ?_⟩
  intro t ht
  set N : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hNsq_le : N ^ 2 ≤ ∑' i, B i := by
    have heq : N ^ 2 = ∑' i, tensorSobolevWeight (I := I) (M := M) i σ' *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).coeff i) ^ 2 := by
      rw [hN_def, tensorHs.norm_sq_eq_tsum]
    rw [heq]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).weighted_summable) hB_sum
    rw [smoothCcToTensorHs_coeff]
    exact hBle i t ht
  have hN_le : N ≤ Real.sqrt (∑' i, B i) := by
    rw [← Real.sqrt_sq hN_nn]
    exact Real.sqrt_le_sqrt hNsq_le
  have hcovsum := hCsum (Rjet j t)
  have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤
      ∑ j' ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖ :=
    Finset.single_le_sum
      (f := fun j' => ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖)
      (fun j' _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖
      ≤ ∑ j' ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖ := hsingle
    _ ≤ Csum * N := by rw [hN_def]; exact hcovsum
    _ ≤ Csum * Real.sqrt (∑' i, B i) :=
        mul_le_mul_of_nonneg_left hN_le hCsum_nn

private theorem deTurckSmoothN_path_coeff_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ T ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
          (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a (F t) hδ_lt (hδ t)).coeff i = ψ i t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set Rem : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t) with hRem_def
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rem t)) i with hcpath_def
  obtain ⟨Rjet, hsmooth, hjet, hcovbnd⟩ :=
    deTurckRemainder_path_timeJet_section (I := I) (M := M)
      g₀ g_bg a ha_super hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (cpath i) ψi (Set.Icc (0 : ℝ) T) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hT (hsmooth i)
  choose ψ hψ_smooth hψ_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) T →
      iteratedDeriv j (ψ i) t = iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hψ_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
      ((hψ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  refine ⟨ψ, ⟨fun i => hψ_smooth i, ?_⟩, ?_⟩
  · intro j σ hσ
    obtain ⟨k, hk⟩ : ∃ k : ℕ, σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) ≤ (2 * k : ℕ) := by
      obtain ⟨k, hk⟩ := exists_nat_gt
        (σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1))
      exact ⟨k, by push_cast; linarith⟩
    set σ' : ℝ := ((2 * k : ℕ) : ℝ) with hσ'_def
    have hσσ' : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by
      rw [hσ'_def]; linarith
    obtain ⟨C, hC_nn, hCle⟩ :=
      exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum (I := I) (M := M) g₀ k
    have hcovsum_bnd : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ≤ K := by
      have hbnds : ∀ q ∈ Finset.range (2 * k + 1), ∃ Kq : ℝ, 0 ≤ Kq ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ Kq :=
        fun q _ => hcovbnd j q
      choose! Kq hKq_nn hKq using hbnds
      refine ⟨C * ∑ q ∈ Finset.range (2 * k + 1), Kq q,
        mul_nonneg hC_nn (Finset.sum_nonneg (fun q hq => hKq_nn q hq)), ?_⟩
      intro t ht
      refine le_trans (hCle (Rjet j t)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hC_nn
      refine Finset.sum_le_sum (fun q hq => ?_)
      exact hKq q hq t ht
    obtain ⟨K, hK_nn, hKle⟩ := hcovsum_bnd
    refine ⟨fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2,
      ?_, ?_⟩
    · exact (tensorEigen_summable_negpow (I := I) (M := M) g₀ (σ' - σ) hσσ').mul_right (K ^ 2)
    · intro i t ht
      rw [hjetEq j i t ht, hjet j i t ht]
      set u : ℝ := tensorL2Coeff (I := I) (M := M) hc
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
          have hsummable := (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).weighted_summable
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
    exact hψ_eqOn i ht

theorem deTurckSobolevNHa2_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (_hT : 0 < T) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (_hd₂_le : d₂ ≤ T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ : JetSpectralMassControl (I := I) (M := M) g₀ φ d₂)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ d₂ ∧
        ∀ i, (fun t => (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set R₀ : ℝ := deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super with hR₀_def
  have hR₀_pos : 0 < R₀ := deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super
  obtain ⟨hφ_smooth, hφ_mass⟩ := hφ
  have hmass0 : ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 σ hσ
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
  obtain ⟨ψ, hψ_ctrl, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super hd₂_pos F hδ_lt hδ_all φ hφ_smooth
      hF_coeff hφ_mass
  refine ⟨ψ, hψ_ctrl, fun i => ?_⟩
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

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
