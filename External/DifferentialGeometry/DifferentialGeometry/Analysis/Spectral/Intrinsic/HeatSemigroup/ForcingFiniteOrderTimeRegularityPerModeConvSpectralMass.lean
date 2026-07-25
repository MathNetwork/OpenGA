import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Calculus.ContDiffExtendInterval

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

private theorem perModeConv_contDiff_succ_of_contDiff (lam : ℝ) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (k : ℕ) f) : ContDiff ℝ ((k + 1 : ℕ)) (perModeConv lam f) := by
  have hfcont : Continuous f := hf.continuous
  have hphi_low : ContDiff ℝ (k : ℕ) (perModeConv lam f) :=
    perModeConv_contDiff_of_contDiff (k : ℕ∞) lam f hf
  have hderiv_eq : deriv (perModeConv lam f)
      = fun t => f t - lam * perModeConv lam f t :=
    deriv_eq (fun t => perModeConv_hasDerivAt lam hfcont t)
  have hdiff : Differentiable ℝ (perModeConv lam f) :=
    fun t => (perModeConv_hasDerivAt lam hfcont t).differentiableAt
  rw [Nat.cast_succ, contDiff_succ_iff_deriv]
  refine ⟨hdiff, fun hω => absurd hω (by simp), ?_⟩
  rw [hderiv_eq]
  exact hf.sub (contDiff_const.mul hphi_low)

private theorem perModeConv_iteratedDeriv_succ_finiteOrder (lam : ℝ) {f : ℝ → ℝ}
    (p : ℕ) (hf : ContDiff ℝ (p : ℕ) f) :
    iteratedDeriv (p + 1) (perModeConv lam f)
      = fun t => iteratedDeriv p f t - lam * iteratedDeriv p (perModeConv lam f) t := by
  have hfcont : Continuous f := hf.continuous
  have hphi_smooth : ContDiff ℝ (p : ℕ) (perModeConv lam f) :=
    perModeConv_contDiff_of_contDiff (p : ℕ∞) lam f hf
  have hderiv_eq : deriv (perModeConv lam f)
      = fun t => f t - lam * perModeConv lam f t :=
    deriv_eq (fun t => perModeConv_hasDerivAt lam hfcont t)
  rw [iteratedDeriv_succ', hderiv_eq]
  funext t
  have hcd_f : ContDiffAt ℝ (p : WithTop ℕ∞) f t := hf.contDiffAt
  have hcd_phi : ContDiffAt ℝ (p : WithTop ℕ∞) (perModeConv lam f) t :=
    hphi_smooth.contDiffAt
  have hcd_lp : ContDiffAt ℝ (p : WithTop ℕ∞)
      (fun t => lam * perModeConv lam f t) t :=
    hcd_phi.const_smul lam
  have hsub :
      iteratedDeriv p (fun t => f t - lam * perModeConv lam f t) t
        = iteratedDeriv p f t
          - iteratedDeriv p (fun t => lam * perModeConv lam f t) t := by
    have hshow :
        (fun t => f t - lam * perModeConv lam f t)
          = f - fun t => lam * perModeConv lam f t := by
      funext u; simp
    rw [hshow, iteratedDeriv_sub hcd_f hcd_lp]
  rw [hsub]
  have hconst :
      iteratedDeriv p (fun t => lam * perModeConv lam f t) t
        = lam * iteratedDeriv p (perModeConv lam f) t := by
    have hsmul := iteratedDeriv_const_smul (𝕜 := ℝ) (F := ℝ) (R := ℝ)
      (n := p) (f := perModeConv lam f) hcd_phi lam
    simp only [smul_eq_mul] at hsmul
    exact hsmul
  rw [hconst]

private theorem perModeConv_sq_le_T_mul_int (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ}
    {c : ℝ → ℝ} (hc : Continuous c) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (perModeConv lam c t) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, (c s) ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hbase : (perModeConv lam c t) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 :=
    perModeConv_sq_le_time_mul_integral' lam hlam hc ht0
  have hint_t_nn : 0 ≤ ∫ s in (0 : ℝ)..t, (c s) ^ 2 :=
    intervalIntegral.integral_nonneg ht0 (fun s _ => sq_nonneg _)
  have hint_le : (∫ s in (0 : ℝ)..t, (c s) ^ 2) ≤ ∫ s in (0 : ℝ)..T, (c s) ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := t) (c := T)
        ((hc.pow 2).intervalIntegrable 0 t)
        ((hc.pow 2).intervalIntegrable t T)]
    have htail : 0 ≤ ∫ s in t..T, (c s) ^ 2 :=
      intervalIntegral.integral_nonneg htT (fun s _ => sq_nonneg _)
    linarith
  calc (perModeConv lam c t) ^ 2
      ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 := hbase
    _ ≤ T * ∫ s in (0 : ℝ)..T, (c s) ^ 2 := by
        exact mul_le_mul htT hint_le hint_t_nn hT

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem perModeConv_finiteOrder_timeDeriv_spectralMass_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {T : ℝ} (hT : 0 ≤ T) (k : ℕ)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ (k : ℕ) (f i))
    (hf_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i) :
    ∀ (m : ℕ), m ≤ k + 1 → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv m
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i)) t) ^ 2
            ≤ Cmaj i := by
  intro m
  induction m with
  | zero =>
      intro _ σ hσ
      obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (Nat.zero_le k) σ hσ
      refine ⟨fun i => T * (T * B i), (hB_sum.mul_left T).mul_left T, ?_⟩
      intro i t ht
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      have hcont : Continuous (f i) := (hf_smooth i).continuous
      have hbound : (perModeConv lam (f i) t) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, f i s ^ 2 :=
        perModeConv_sq_le_T_mul_int lam hlam_nn hcont hT ht
      have hintegral_le :
          tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2
            ≤ T * B i := by
        have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2 ≤ B i := by
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2)
            volume 0 T :=
          ((hcont.pow 2).const_mul _).intervalIntegrable 0 T
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) volume 0 T :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..T,
              tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2
            ≤ ∫ _s in (0 : ℝ)..T, B i := by
          refine intervalIntegral.integral_mono_on hT hi_lhs hi_const ?_
          intro s hs
          exact hpoint s hs
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
        calc tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2
            ≤ (T - 0) * B i := hmono
          _ = T * B i := by ring
      calc tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv 0 (perModeConv lam (f i)) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ * (perModeConv lam (f i) t) ^ 2 := by
            rw [iteratedDeriv_zero]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ * (T * ∫ s in (0 : ℝ)..T, f i s ^ 2) :=
            mul_le_mul_of_nonneg_left hbound hwt_nn
        _ = T * (tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2) := by
            ring
        _ ≤ T * (T * B i) := by
            apply mul_le_mul_of_nonneg_left hintegral_le hT
  | succ p ih =>
      intro hm σ hσ
      have hp_le_k : p ≤ k := by omega
      obtain ⟨Bf, hBf_sum, hBf_le⟩ := hf_mass p hp_le_k σ hσ
      obtain ⟨Cprev, hCprev_sum, hCprev_le⟩ := ih (by omega) (σ + 2) (by linarith)
      refine ⟨fun i => 2 * Bf i + 2 * Cprev i,
        (hBf_sum.mul_left 2).add (hCprev_sum.mul_left 2), ?_⟩
      intro i t ht
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      have hwtσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      have hfp : ContDiff ℝ (p : ℕ) (f i) := (hf_smooth i).of_le (by exact_mod_cast hp_le_k)
      have hrec := perModeConv_iteratedDeriv_succ_finiteOrder lam p hfp
      have hval : iteratedDeriv (p + 1) (perModeConv lam (f i)) t
          = iteratedDeriv p (f i) t - lam * iteratedDeriv p (perModeConv lam (f i)) t := by
        rw [hrec]
      have hexpand_sq :
          (iteratedDeriv (p + 1) (perModeConv lam (f i)) t) ^ 2
            ≤ 2 * (iteratedDeriv p (f i) t) ^ 2
              + 2 * (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by
        rw [hval]
        nlinarith [sq_nonneg (iteratedDeriv p (f i) t
            + lam * iteratedDeriv p (perModeConv lam (f i)) t),
          sq_nonneg (iteratedDeriv p (f i) t
            - lam * iteratedDeriv p (perModeConv lam (f i)) t)]
      have hforce_term :
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv p (f i) t) ^ 2 ≤ Bf i :=
        hBf_le i t ht
      have hphi_term :
          tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 ≤ Cprev i :=
        hCprev_le i t ht
      have hweight_step :
          tensorSobolevWeight (I := I) (M := M) i σ * lam ^ 2
            ≤ tensorSobolevWeight (I := I) (M := M) i (σ + 2) := by
        have h1le : (1 : ℝ) ≤ 1 + lam := by linarith
        have hlamsq_le : lam ^ 2 ≤ (1 + lam) ^ 2 := by nlinarith [hlam_nn]
        have hwtσ_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
          tensorSobolevWeight_pos (I := I) (M := M) i σ
        have hsplit : tensorSobolevWeight (I := I) (M := M) i (σ + 2)
            = tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam) ^ 2 := by
          unfold tensorSobolevWeight
          rw [hlam_def] at *
          rw [Real.rpow_add (by linarith)]
          congr 1
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hlamsq_le hwtσ_nn
      have hlam_sq_term :
          tensorSobolevWeight (I := I) (M := M) i σ *
              (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2
            ≤ Cprev i := by
        have heq : (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2
            = lam ^ 2 * (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by ring
        calc tensorSobolevWeight (I := I) (M := M) i σ *
              (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2
            = (tensorSobolevWeight (I := I) (M := M) i σ * lam ^ 2) *
                (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by
              rw [heq]; ring
          _ ≤ tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
                (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by
              apply mul_le_mul_of_nonneg_right hweight_step (sq_nonneg _)
          _ ≤ Cprev i := hphi_term
      calc tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv (p + 1) (perModeConv lam (f i)) t) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (2 * (iteratedDeriv p (f i) t) ^ 2
                + 2 * (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2) :=
            mul_le_mul_of_nonneg_left hexpand_sq hwtσ_nn
        _ = 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv p (f i) t) ^ 2)
              + 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2) := by ring
        _ ≤ 2 * Bf i + 2 * Cprev i := by
            have h1 := mul_le_mul_of_nonneg_left hforce_term (by norm_num : (0 : ℝ) ≤ 2)
            have h2 := mul_le_mul_of_nonneg_left hlam_sq_term (by norm_num : (0 : ℝ) ≤ 2)
            linarith

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem perModeConv_finiteOrder_timeJet_spectralMass_gain
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {T : ℝ} (hT : 0 ≤ T) (k : ℕ)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ (k : ℕ) (f i))
    (hf_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiff ℝ ((k + 1 : ℕ))
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i))) ∧
    (∀ (j : ℕ), j ≤ k + 1 → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i)) t) ^ 2 ≤ B i) := by
  refine ⟨fun i =>
    perModeConv_contDiff_succ_of_contDiff (TensorEigenIdx.lambda (I := I) (M := M) i) k
      (hf_smooth i), ?_⟩
  intro j hj τ hτ
  exact perModeConv_finiteOrder_timeDeriv_spectralMass_le (I := I) (M := M)
    g hT k f hf_smooth hf_mass j hj τ hτ


end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
