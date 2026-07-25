import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeL2EigenProjection
import DifferentialGeometry.Analysis.ProjectedContractionFixedPoint
import Mathlib.Analysis.ODE.Gronwall


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

omit [BoundarylessManifold I M] in
theorem galerkinForcing_eq_galerkinCoordEmbed
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N t) ((a : ℝ) + 2) =
      galerkinCoordEmbed (I := I) (M := M) g₀ a (eigenIdxFinset (I := I) (M := M) g₀ N)
        ((EuclideanSpace.equiv {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
          (fun j => U N t j.1)) := by
  apply tensorHs.ext
  funext i
  rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · rw [if_pos hi, dif_pos hi]
    rfl
  · rw [if_neg hi, dif_neg hi]

omit [BoundarylessManifold I M] in
theorem continuousOn_galerkinForcing_field
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))
      (Set.Icc (0 : ℝ) T) := by
  have hcoord : ContinuousOn
      (fun t => (EuclideanSpace.equiv
          {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
        (fun j => U N t j.1)) (Set.Icc (0 : ℝ) T) := by
    apply (EuclideanSpace.equiv
      {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm.continuous.comp_continuousOn
    refine continuousOn_pi.2 (fun j => hUcont j.1 j.2)
  have hcomp : ContinuousOn
      (fun t => galerkinCoordEmbed (I := I) (M := M) g₀ a
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        ((EuclideanSpace.equiv
            {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
          (fun j => U N t j.1))) (Set.Icc (0 : ℝ) T) :=
    (galerkinCoordEmbed (I := I) (M := M) g₀ a
      (eigenIdxFinset (I := I) (M := M) g₀ N)).continuous.comp_continuousOn hcoord
  refine hcomp.congr (fun t _ => ?_)
  rw [galerkinForcing_eq_galerkinCoordEmbed]

theorem continuousOn_galerkinForcing
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hfield := continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N hUcont
    have hcoeff : ContinuousOn
        (fun t => (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)))
          (Set.Icc (0 : ℝ) T) :=
        hK.continuous.comp_continuousOn hfield
      have hcoeff_cont : ContinuousOn
          (fun t => tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))))
          (Set.Icc (0 : ℝ) T) :=
        (tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).continuous.comp_continuousOn hN_cont
      simpa only [tensorHsCoeffL_apply] using hcoeff_cont
    refine hcoeff.congr (fun t _ => ?_)
    rw [deTurckGalerkinForcing_apply, if_pos hi]
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun t _ => ?_)
    rw [deTurckGalerkinForcing_apply, if_neg hi]

theorem galerkinPerMode_eq_perModeConv
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    U N t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i)) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set fForce : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i) with hfForce_def
  have hfForce_cont : Continuous fForce := by
    refine Continuous.Icc_extend' ?_
    exact (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N hUcont i).restrict
  have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      fForce x = deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N x i := by
    intro x hx
    rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
  set v : ℝ → ℝ → ℝ := fun s y => -lam * y + fForce s with hv_def
  have hv_lip : ∀ s ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith ⟨|lam|, abs_nonneg lam⟩
      (v s) (Set.univ : Set ℝ) := by
    intro s _
    have hlip : LipschitzWith ⟨|lam|, abs_nonneg lam⟩ (fun y : ℝ => -lam * y + fForce s) := by
      refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
      rw [Real.dist_eq, Real.dist_eq]
      have heq : -lam * y₁ + fForce s - (-lam * y₂ + fForce s) = -lam * (y₁ - y₂) := by ring
      rw [heq, abs_mul, abs_neg]
      simp only [NNReal.coe_mk, le_refl]
    exact hlip.lipschitzOnWith
  set gG : ℝ → ℝ := fun s => U N s i with hgG_def
  set gP : ℝ → ℝ := fun s => perModeConv lam fForce s with hgP_def
  have hgG_cont : ContinuousOn gG (Set.Icc (0 : ℝ) T) := hUcont i hi
  have hgP_cont : ContinuousOn gP (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hfForce_cont).continuousOn
  have hgG_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gG (v s (gG s)) (Set.Ici s) s := by
    intro s hs
    have hd := hUderiv s hs i hi
    have hforce_eq : fForce s = deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i :=
      hfForce_mem ⟨hs.1, le_of_lt hs.2⟩
    have hval : v s (gG s) =
        -(lam) * U N s i + deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i := by
      simp only [hv_def, hgG_def, hforce_eq]
    rw [hval]
    exact hd
  have hgP_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gP (v s (gP s)) (Set.Ici s) s := by
    intro s _
    have hd := (perModeConv_hasDerivAt lam hfForce_cont s).hasDerivWithinAt (s := Set.Ici s)
    have hval : v s (gP s) = fForce s - lam * perModeConv lam fForce s := by
      simp only [hv_def, hgP_def]; ring
    rw [hval]
    exact hd
  have hinit : gG 0 = gP 0 := by
    simp only [hgG_def, hgP_def, hUinit i hi, perModeConv_zero_left]
  have heqOn : Set.EqOn gG gP (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hgG_cont
      (fun s hs => hgG_deriv s hs) (fun s _ => Set.mem_univ _)
      hgP_cont (fun s hs => hgP_deriv s hs) (fun s _ => Set.mem_univ _) hinit
  exact heqOn ht

theorem perModeConv_timeL2_sub (lam : ℝ) (f₁ f₂ : timeL2 ℝ T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    perModeConv lam (fun s => f₁ s) t - perModeConv lam (fun s => f₂ s) t =
      perModeConv lam (fun s => (f₁ - f₂) s) t := by
  have hcongr : perModeConv lam (fun s => (f₁ - f₂) s) t =
      perModeConv lam (fun s => f₁ s - f₂ s) t :=
    perModeConv_timeL2_congr lam
      (by filter_upwards [Lp.coeFn_sub f₁ f₂] with r hr using hr) ht
  rw [hcongr]
  unfold perModeConv
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_kernel_mul_timeL2 lam t f₁ 0 t
      ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)
    (intervalIntegrable_kernel_mul_timeL2 lam t f₂ 0 t
      ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem tendsto_perModeConv_of_tendsto_timeL2 (lam : ℝ) (hlam : 0 ≤ lam)
    {fseq : ℕ → timeL2 ℝ T} {flim : timeL2 ℝ T}
    (hconv : Tendsto fseq atTop (𝓝 flim))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => perModeConv lam (fun s => (fseq N) s) t) atTop
      (𝓝 (perModeConv lam (fun s => flim s) t)) := by
  rcases le_or_gt 0 T with hT0 | hT0
  · rw [Metric.tendsto_atTop] at hconv ⊢
    intro ε hε
    rcases eq_or_lt_of_le hT0 with hT00 | hTpos
    · have htval : t = 0 := by
        obtain ⟨ht1, ht2⟩ := ht
        rw [← hT00] at ht2
        exact le_antisymm ht2 ht1
      refine ⟨0, fun N _ => ?_⟩
      rw [htval]
      simp only [perModeConv_zero_left, dist_self]
      exact hε
    · set δ : ℝ := ε / (Real.sqrt T + 1) with hδ_def
      have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
      have hδ_pos : 0 < δ := by
        rw [hδ_def]; positivity
      obtain ⟨Nε, hNε⟩ := hconv δ hδ_pos
      refine ⟨Nε, fun N hN => ?_⟩
      have hdist : dist (fseq N) flim < δ := hNε N hN
      have hsub_eq :
          perModeConv lam (fun s => (fseq N) s) t - perModeConv lam (fun s => flim s) t =
            perModeConv lam (fun s => (fseq N - flim) s) t :=
        perModeConv_timeL2_sub lam (fseq N) flim ht
      have hbound : |perModeConv lam (fun s => (fseq N - flim) s) t| ≤
          Real.sqrt T * ‖fseq N - flim‖ :=
        abs_perModeConv_timeL2_le lam hlam (fseq N - flim) ht
      have hnorm : ‖fseq N - flim‖ < δ := by
        rw [← dist_eq_norm]; exact hdist
      rw [Real.dist_eq, hsub_eq]
      calc |perModeConv lam (fun s => (fseq N - flim) s) t|
          ≤ Real.sqrt T * ‖fseq N - flim‖ := hbound
        _ ≤ Real.sqrt T * δ :=
            mul_le_mul_of_nonneg_left (le_of_lt hnorm) hsqrt_nn
        _ < ε := by
            have hden : (0 : ℝ) < Real.sqrt T + 1 := by positivity
            rw [hδ_def,
              show Real.sqrt T * (ε / (Real.sqrt T + 1))
                = (Real.sqrt T * ε) / (Real.sqrt T + 1) by ring,
              div_lt_iff₀ hden]
            nlinarith [hsqrt_nn, hε]
  · have htval : t = 0 := by
      obtain ⟨ht1, ht2⟩ := ht
      have : t ≤ 0 := le_trans ht2 (le_of_lt hT0)
      exact le_antisymm this ht1
    rw [htval]
    simp only [perModeConv_zero_left]
    exact tendsto_const_nhds

theorem unifIntegrable_of_uniform_norm_bound {α β : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [NormedAddCommGroup β] [IsFiniteMeasure μ]
    {f : ℕ → α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) :
    UnifIntegrable f 2 μ := by
  refine unifIntegrable_of (by norm_num) (by norm_num) hf (fun ε hε => ?_)
  refine ⟨(max C 0).toNNReal + 1, fun n => ?_⟩
  have hzero : { x | (max C 0).toNNReal + 1 ≤ ‖f n x‖₊ }.indicator (f n) =ᵐ[μ] 0 := by
    filter_upwards [hC n] with x hx
    have hle : ‖f n x‖₊ < (max C 0).toNNReal + 1 := by
      have hxle : ‖f n x‖ ≤ (max C 0) := le_trans hx (le_max_left _ _)
      have : (‖f n x‖₊ : ℝ) ≤ (max C 0).toNNReal := by
        rw [Real.coe_toNNReal _ (le_max_right _ _)]; exact hxle
      have hlt : (‖f n x‖₊ : ℝ) < ((max C 0).toNNReal : ℝ) + 1 := by linarith
      exact_mod_cast hlt
    rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_le]; exact hle)]
    rfl
  rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
  exact zero_le _

omit [BoundarylessManifold I M] in
private theorem tensorHs_norm_tendsto_zero_of_coeff_tendsto_of_uniform
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ' σ'' : ℝ}
    (hσ'σ'' : σ' < σ'')
    (d : ℕ → tensorHs (I := I) (M := M) g r s σ'')
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ n, ‖d n‖ ≤ C)
    (hcoeff0 : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0)) :
    Tendsto (fun n => ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖) atTop (𝓝 0) := by
  classical
  set ι := TensorEigenIdx (I := I) (M := M) g r s
  have hnormsq : ∀ n,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ ^ 2 =
        ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' *
          ((d n).coeff i) ^ 2 := by
    intro n
    have h := tensorHs.norm_sq_eq_tsum (I := I) (M := M)
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n))
    rwa [tensorHsInclusion_coeff] at h
  have hsumm' : ∀ n, Summable (fun i : ι =>
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) :=
    fun n => tensorHs.weighted_summable_of_le (I := I) (M := M) hσ'σ''.le (d n)
  have hmass'' : ∀ n,
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2
        = ‖d n‖ ^ 2 :=
    fun n => (tensorHs.norm_sq_eq_tsum (I := I) (M := M) (d n)).symm
  suffices hsq : Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖ ^ 2) atTop (𝓝 0) by
    have hnn : ∀ n,
        0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ := fun n => norm_nonneg _
    have hsqrt :
        Tendsto (fun n => Real.sqrt
          (‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            hσ'σ''.le (d n)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr (fun n => ?_)
    rw [Real.sqrt_sq (hnn n)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hexp : σ' - σ'' < 0 := by linarith
  obtain ⟨Λ, hΛgt1, hΛtail⟩ :
      ∃ Λ : ℝ, 1 < Λ ∧ Λ ^ (σ' - σ'') * C ^ 2 < ε / 2 := by
    set δ : ℝ := (ε / 2) / (C ^ 2 + 1) with hδ_def
    have hδ_pos : 0 < δ := by
      have : (0 : ℝ) < C ^ 2 + 1 := by positivity
      rw [hδ_def]; positivity
    have htend : Tendsto (fun x : ℝ => x ^ (σ' - σ'')) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := σ'' - σ') (by linarith)
      rwa [show -(σ'' - σ') = σ' - σ'' by ring] at h
    have hev : ∀ᶠ x : ℝ in atTop, x ^ (σ' - σ'') < δ :=
      htend.eventually_lt_const hδ_pos
    obtain ⟨Λ, hΛ1, hΛδ⟩ := ((eventually_gt_atTop 1).and hev).exists
    refine ⟨Λ, hΛ1, ?_⟩
    have hΛδ_nn : 0 ≤ Λ ^ (σ' - σ'') := Real.rpow_nonneg (by linarith) _
    have hCsq_nn : 0 ≤ C ^ 2 := sq_nonneg C
    have h1 : Λ ^ (σ' - σ'') * C ^ 2 ≤ δ * C ^ 2 :=
      mul_le_mul_of_nonneg_right hΛδ.le hCsq_nn
    have h2 : δ * C ^ 2 < ε / 2 := by
      rw [hδ_def]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
      have hεpos : 0 < ε / 2 := by linarith
      nlinarith [hεpos, hCsq_nn]
    linarith
  set F : Finset ι :=
    (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g r s Λ).toFinset
    with hF_def
  have hmemF : ∀ i : ι, i ∈ F ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
    intro i; rw [hF_def, Set.Finite.mem_toFinset]; rfl
  have hcompl_bd : ∀ (n : ℕ) (i : ι), i ∉ F →
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
    intro n i hi
    have hΛle : Λ ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      by_contra hcon
      exact hi ((hmemF i).2 (lt_of_not_ge hcon))
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ' =
        tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
          tensorSobolevWeight (I := I) (M := M) i σ'' := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M)]
      congr 1; ring
    have hratio : tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') ≤
        Λ ^ (σ' - σ'') := by
      unfold tensorSobolevWeight
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hΛle hexp.le
    have hw''_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
    have hcoeff_nn : 0 ≤ ((d n).coeff i) ^ 2 := sq_nonneg _
    calc
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
            rw [hsplit]; ring
      _ ≤ Λ ^ (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
  have htail : ∀ n,
      ∑' i : { i : ι // i ∉ F },
          tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') * C ^ 2 := by
    intro n
    have hsub_summ' : Summable (fun i : { i : ι // i ∉ F } =>
        tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2) :=
      (hsumm' n).subtype _
    have hsub_summ'' : Summable (fun i : { i : ι // i ∉ F } =>
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2)) :=
      ((d n).weighted_summable.subtype _).mul_left _
    calc
      ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2
          ≤ ∑' i : { i : ι // i ∉ F },
              Λ ^ (σ' - σ'') *
                (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
                  ((d n).coeff i) ^ 2) :=
            hsub_summ'.tsum_le_tsum
              (fun i => hcompl_bd n i.1 i.2) hsub_summ''
      _ = Λ ^ (σ' - σ'') *
            ∑' i : { i : ι // i ∉ F },
              tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2 :=
            (tsum_mul_left)
      _ ≤ Λ ^ (σ' - σ'') *
            ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' *
              ((d n).coeff i) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            refine ((d n).weighted_summable.subtype _).tsum_le_tsum_of_inj
              Subtype.val Subtype.val_injective (fun i _ => ?_) (fun i => le_refl _)
              (d n).weighted_summable
            have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
              tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
            positivity
      _ ≤ Λ ^ (σ' - σ'') * C ^ 2 := by
            rw [hmass'' n]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            have hnn : (0 : ℝ) ≤ ‖d n‖ := norm_nonneg _
            nlinarith [hCbd n, hnn, hC]
  have hfin0 : Tendsto (fun n =>
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum (s := F)
      (f := fun i n => tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      (a := fun _ : ι => (0 : ℝ))
      (fun i _ => by
        have hc : Tendsto (fun n => ((d n).coeff i) ^ 2) atTop (𝓝 (0 ^ 2)) :=
          (hcoeff0 i).pow 2
        rw [show (0 : ℝ) ^ 2 = 0 by ring] at hc
        have := hc.const_mul (tensorSobolevWeight (I := I) (M := M) i σ')
        simpa using this)
    simpa using h
  rw [Metric.tendsto_atTop] at hfin0
  obtain ⟨N, hN⟩ := hfin0 (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hsplit_sum :
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) +
          ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 :=
    ((hsumm' n).sum_add_tsum_subtype_compl F).symm
  have hfin_lt : ∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 < ε / 2 := by
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
        ≤ |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2| :=
          le_abs_self _
      _ < ε / 2 := hd
  have htail_lt : ∑' i : { i : ι // i ∉ F },
      tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 < ε / 2 :=
    lt_of_le_of_lt (htail n) hΛtail
  have hbound : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 < ε := by
    rw [hnormsq n, hsplit_sum]
    linarith
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 := sq_nonneg _
  rwa [abs_of_nonneg hnn]

omit [BoundarylessManifold I M] in
theorem tendsto_finiteEigenComboHs_of_coeff_tendsto_of_succWeighted_bound
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (W : tensorHs (I := I) (M := M) g 0 2 σ) (B : ℝ)
    (hbound : ∀ N, ∑ i ∈ S N,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 ≤ B)
    (hcoeff : ∀ i, Tendsto
        (fun N => (finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ).coeff i)
        atTop (𝓝 (W.coeff i))) :
    Tendsto (fun N => finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ)
      atTop (𝓝 W) := by
  classical
  set u : ℕ → tensorHs (I := I) (M := M) g 0 2 (σ + 1) :=
    fun N => finiteEigenComboHs (I := I) (M := M) g (S N) (c N) (σ + 1) with hu_def
  have hu_coeff : ∀ N i, (u N).coeff i =
      (finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ).coeff i := by
    intro N i
    simp only [hu_def, finiteEigenComboHs_coeff]
  have hconv_coeff : ∀ i, Tendsto (fun N => (u N).coeff i) atTop (𝓝 (W.coeff i)) := by
    intro i
    exact (hcoeff i).congr (fun N => (hu_coeff N i).symm)
  have hu_normSq_le : ∀ N, ‖u N‖ ^ 2 ≤ B := by
    intro N
    have heq : ‖u N‖ ^ 2 = ∑ i ∈ S N,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 := by
      simp only [hu_def]
      rw [finiteEigenCombo_spectral_normSq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rfl
    rw [heq]; exact hbound N
  have hbd_finset : ∀ t : Finset (TensorEigenIdx (I := I) (M := M) g 0 2),
      ∑ i ∈ t, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2 ≤ B := by
    intro t
    have hlim : Tendsto
        (fun N => ∑ i ∈ t,
          tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2)
        atTop
        (𝓝 (∑ i ∈ t,
          tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2)) := by
      refine tendsto_finset_sum t (fun i _ => ?_)
      exact ((hconv_coeff i).pow 2).const_mul _
    have hle : ∀ N, ∑ i ∈ t,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2 ≤ B := by
      intro N
      calc ∑ i ∈ t,
            tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2
          = ∑ i ∈ t, (if i ∈ S N then
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 else 0) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hu_coeff, finiteEigenComboHs_coeff]
            by_cases hi : i ∈ S N <;> simp [hi]
        _ = ∑ i ∈ t ∩ S N,
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 :=
            Finset.sum_ite_mem t (S N) _
        _ ≤ ∑ i ∈ S N,
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
              (fun i _ _ => mul_nonneg
                (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
        _ ≤ B := hbound N
    exact le_of_tendsto' hlim hle
  have hnn : (0 : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) ≤
      fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2 :=
    fun i => mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _)
  have hWp_summ : Summable
      (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2) :=
    summable_of_sum_le hnn hbd_finset
  set Wp : tensorHs (I := I) (M := M) g 0 2 (σ + 1) :=
    ⟨W.coeff, hWp_summ⟩ with hWp_def
  have hWp_coeff : ∀ i, Wp.coeff i = W.coeff i := by
    intro i; rw [hWp_def]
  have hWp_normSq_le : ‖Wp‖ ^ 2 ≤ B := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) Wp]
    simp only [hWp_coeff]
    exact Real.tsum_le_of_sum_le hnn hbd_finset
  have hsubcoeff : ∀ (a b : tensorHs (I := I) (M := M) g 0 2 (σ + 1)) i,
      (a - b).coeff i = a.coeff i - b.coeff i := by
    intro a b i
    simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
  have hCbd : ∀ N, ‖u N - Wp‖ ≤ 2 * Real.sqrt B := by
    intro N
    have huN : ‖u N‖ ≤ Real.sqrt B := by
      calc ‖u N‖ = Real.sqrt (‖u N‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt (hu_normSq_le N)
    have hWpn : ‖Wp‖ ≤ Real.sqrt B := by
      calc ‖Wp‖ = Real.sqrt (‖Wp‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hWp_normSq_le
    calc ‖u N - Wp‖ ≤ ‖u N‖ + ‖Wp‖ := norm_sub_le _ _
      _ ≤ Real.sqrt B + Real.sqrt B := add_le_add huN hWpn
      _ = 2 * Real.sqrt B := by ring
  have hcoeff0 : ∀ i, Tendsto (fun N => (u N - Wp).coeff i) atTop (𝓝 0) := by
    intro i
    have h := (hconv_coeff i).sub_const (W.coeff i)
    rw [sub_self] at h
    refine h.congr (fun N => ?_)
    rw [hsubcoeff (u N) Wp i, hWp_coeff i]
  have hlt : (σ : ℝ) < σ + 1 := by linarith
  have hsqrtB_nn : (0 : ℝ) ≤ 2 * Real.sqrt B := by positivity
  have hhelper := tensorHs_norm_tendsto_zero_of_coeff_tendsto_of_uniform
    (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ' := σ) (σ'' := σ + 1)
    hlt (fun N => u N - Wp) hsqrtB_nn hCbd hcoeff0
  have hincl_uN : ∀ N,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hlt.le (u N) = finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ := by
    intro N
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hu_coeff N i]
  have hincl_Wp :
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hlt.le Wp = W := by
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hWp_coeff i]
  have hincl_eq : ∀ N,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hlt.le (u N - Wp) =
        finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ - W := by
    intro N
    rw [map_sub, hincl_uN N, hincl_Wp]
  have hNorm : Tendsto
      (fun N => ‖finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ - W‖)
      atTop (𝓝 0) := by
    refine hhelper.congr (fun N => ?_)
    rw [hincl_eq N]
  have hSub := tendsto_zero_iff_norm_tendsto_zero.mpr hNorm
  exact tendsto_sub_nhds_zero_iff.mp hSub

theorem galerkinForcing_field_eq_maxRegDuhamel_projTruncation
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (N : ℕ) :
    TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (timeL2EigenProj (I := I) (M := M) (g := g₀) (a : ℝ) T N
          (nemytskii (I := I) (M := M)
            (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
              a ha_super)
            (TimeSobolev.ofContinuousOn
              (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))))) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set hLipC := deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set gforceN := nemytskii (I := I) (M := M) hLipC VN with hgforceN_def
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  refine Lp.ext ?_
  have hLco := timeModeCoeff_coeFn (I := I) (M := M) VN i
  have hVco : ⇑VN =ᵐ[timeMeasure T]
      (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hRco := timeModeCoeff_coeFn (I := I) (M := M)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN)) i
  have hRpm := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
    hT hT1 (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPNco := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) =ᵐ[timeMeasure T]
      fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforceN s) :=
    ContinuousLinearMap.coeFn_compLpL _ gforceN
  have hgco : ⇑gforceN =ᵐ[timeMeasure T]
      (fun s => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (VN s)) :=
    nemytskii_coeFn (I := I) (M := M) hLipC VN
  have hPNforcing : ⇑(timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) =ᵐ[timeMeasure T]
      (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) := by
    filter_upwards [hPNco, hPproj, hgco, hVco] with s hs1 hs2 hs3 hs4
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff, deTurckGalerkinForcing_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hi, if_pos hi, hs3, hs4]
    · rw [if_neg hi, if_neg hi]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun t => U N t i := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_pos hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam
          (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) t :=
      perModeConv_timeL2_congr lam hPNforcing htmem'
    have hgp := galerkinPerMode_eq_perModeConv (I := I) (M := M) g₀ g_bg a ha_super hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hi htmem'
    rw [← hlam_def] at hgp
    rw [hgp, hcongr1]
    refine perModeConv_timeL2_congr lam ?_ htmem'
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
    rw [Set.IccExtend_of_mem hT.le _ hs]
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun _ => (0 : ℝ) := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_neg hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam (fun _ => (0 : ℝ)) t := by
      refine perModeConv_timeL2_congr lam ?_ htmem'
      filter_upwards [hPNforcing] with s hs
      rw [hs, deTurckGalerkinForcing_apply, if_neg hi]
    rw [hcongr1]
    unfold perModeConv
    simp

theorem galerkinODE_solution_unique
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (_hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (V V' : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hVcont : ∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T))
    (hVderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hV'cont : ∀ i ∈ S, ContinuousOn (fun t => V' t i) (Set.Icc (0 : ℝ) T))
    (hV'deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V' r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V' t i +
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V' t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hinit : ∀ i ∈ S, V 0 i = V' 0 i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (hi : i ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    V t i = V' t i := by
  classical
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordField_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  set e := EuclideanSpace.equiv {i // i ∈ S} ℝ with he_def
  set γ : (ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) →
      ℝ → EuclideanSpace ℝ {i // i ∈ S} :=
    fun W t => e.symm (fun j => W t j.1) with hγ_def
  have hcomp_j : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ)
      (j : {i // i ∈ S}), (γ W t) j = W t j.1 := by
    intro W t j; rfl
  have hembed : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ),
      galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ W t) =
        finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2) := by
    intro W t
    apply tensorHs.ext
    funext i'
    rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
    by_cases hi' : i' ∈ S
    · rw [dif_pos hi', if_pos hi']; rfl
    · rw [dif_neg hi', if_neg hi']
  have hγcont : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ i ∈ S, ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T)) →
      ContinuousOn (γ W) (Set.Icc (0 : ℝ) T) := by
    intro W hWcont
    exact e.symm.continuous.comp_continuousOn (continuousOn_pi.2 (fun j => hWcont j.1 j.2))
  have hγderiv : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => W r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff i)
          (Set.Ici t) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (γ W)
          (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) (Set.Ici t) t := by
    intro W hWderiv t ht
    have hpi : HasDerivWithinAt (fun s => (fun j : {i // i ∈ S} => W s j.1))
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun j => hWderiv t ht j.1 j.2)
    have hcomp := (e.symm.hasFDerivAt (x := (fun j : {i // i ∈ S} => W t j.1))).comp_hasDerivWithinAt
      t hpi
    rw [ContinuousLinearEquiv.coe_coe] at hcomp
    have hval : e.symm
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1) =
        galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t) := by
      apply e.injective
      ext j
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change _ = (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) j
      rw [galerkinCoordField_apply, hcomp_j, hembed]
    rw [hval] at hcomp
    exact hcomp
  have hlip_univ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith Klip (galerkinCoordField (I := I) (M := M) g₀ g_bg a S)
        (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})) :=
    fun _ _ => hKlip.lipschitzOnWith
  have heqOn : Set.EqOn (γ V) (γ V') (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => galerkinCoordField (I := I) (M := M) g₀ g_bg a S)
      (s := fun _ => (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})))
      hlip_univ (hγcont V hVcont) (fun s hs => hγderiv V hVderiv s hs)
      (fun _ _ => Set.mem_univ _) (hγcont V' hV'cont) (fun s hs => hγderiv V' hV'deriv s hs)
      (fun _ _ => Set.mem_univ _) ?_
    apply e.injective
    ext j
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact hinit j.1 j.2
  have := heqOn ht
  have hj : (γ V t) ⟨i, hi⟩ = (γ V' t) ⟨i, hi⟩ := by rw [this]
  rw [hcomp_j, hcomp_j] at hj
  exact hj

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
