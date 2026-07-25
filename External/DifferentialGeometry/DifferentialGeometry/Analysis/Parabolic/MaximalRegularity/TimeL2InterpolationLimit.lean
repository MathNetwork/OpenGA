import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit

noncomputable section

open Filter MeasureTheory
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def timeL2Inclusion {τ σ : ℝ} {T : ℝ} (hτσ : τ ≤ σ) :
    timeL2 (tensorHs (I := I) (M := M) g r s σ) T →L[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g r s τ) T :=
  (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ).compLpL 2
    (timeMeasure T)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_timeL2Inclusion {τ σ : ℝ} {T : ℝ} (hτσ : τ ≤ σ)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s σ) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ f) i =
      timeModeCoeff (I := I) (M := M) f i := by
  refine MeasureTheory.Lp.ext ?_
  have h1 := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ f) i
  have h2 := timeModeCoeff_coeFn (I := I) (M := M) f i
  have hincl :
      (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ f)
        =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            hτσ (f t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) f
  refine h1.trans ?_
  refine (Filter.EventuallyEq.trans ?_ h2.symm)
  filter_upwards [hincl] with t ht
  rw [ht, tensorHsInclusion_coeff_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma weight_mul_norm_timeModeCoeff_sq_le_normSq {a : ℝ} {T : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [norm_sq_eq_tsum_timeModeCoeff (I := I) (M := M) h_compact (f := f)]
  refine Summable.le_tsum
    (summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) h_compact (f := f))
    i (fun j _ => ?_)
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) j a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) j a
  positivity

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma norm_timeModeCoeff_tendsto_zero_of_norm_tendsto_zero {a : ℝ} {T : ℝ}
    (d : ℕ → timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (hd : Tendsto (fun n => ‖d n‖) atTop (𝓝 0))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Tendsto (fun n => ‖timeModeCoeff (I := I) (M := M) (d n) i‖) atTop (𝓝 0) := by
  have hbd : ∀ n, ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ≤
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ * ‖d n‖ :=
    fun n => norm_timeModeCoeff_le (I := I) (M := M) (d n) i
  have hupper :
      Tendsto (fun n => (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ *
        ‖d n‖) atTop (𝓝 0) := by
    have := hd.const_mul
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _) hbd hupper

theorem timeL2_norm_tendsto_zero_of_low_tendsto_of_uniform
    {σ σ' σ'' : ℝ} {T : ℝ}
    (hσσ' : σ ≤ σ') (hσ'σ'' : σ' < σ'')
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (d : ℕ → timeL2 (tensorHs (I := I) (M := M) g r s σ'') T)
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ n, ‖d n‖ ≤ C)
    (hlow : Tendsto (fun n =>
      ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hσσ'.trans hσ'σ''.le) (d n)‖) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖) atTop (𝓝 0) := by
  classical
  set ι := TensorEigenIdx (I := I) (M := M) g r s

  have hnormsq : ∀ n,
      ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ ^ 2 =
        ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' *
          ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 := by
    intro n
    rw [norm_sq_eq_tsum_timeModeCoeff (I := I) (M := M) h_compact
      (f := timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n))]
    exact tsum_congr (fun i => by
      rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) hσ'σ''.le (d n) i])

  have hsumm' : ∀ n, Summable (fun i : ι =>
      tensorSobolevWeight (I := I) (M := M) i σ' *
        ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2) := by
    intro n
    have h := summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) h_compact
      (f := timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n))
    refine h.congr (fun i => ?_)
    rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) hσ'σ''.le (d n) i]

  have hsumm'' : ∀ n, Summable (fun i : ι =>
      tensorSobolevWeight (I := I) (M := M) i σ'' *
        ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2) :=
    fun n => summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := d n)

  have hmass'' : ∀ n,
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' *
          ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 = ‖d n‖ ^ 2 :=
    fun n => (norm_sq_eq_tsum_timeModeCoeff (I := I) (M := M) h_compact (f := d n)).symm

  suffices hsq : Tendsto (fun n =>
      ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖ ^ 2) atTop (𝓝 0) by
    have hnn : ∀ n,
        0 ≤ ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ := fun n => norm_nonneg _
    have hsqrt :
        Tendsto (fun n => Real.sqrt
          (‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
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
      tensorSobolevWeight (I := I) (M := M) i σ' *
          ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 ≤
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) i σ'' *
            ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2) := by
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
    have hcoeff_nn : 0 ≤ ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 := sq_nonneg _
    calc
      tensorSobolevWeight (I := I) (M := M) i σ' *
            ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' *
                ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2) := by
            rw [hsplit]; ring
      _ ≤ Λ ^ (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' *
                ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)

  have htail : ∀ n,
      ∑' i : { i : ι // i ∉ F },
          tensorSobolevWeight (I := I) (M := M) (i : ι) σ' *
            ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2 ≤
        Λ ^ (σ' - σ'') * C ^ 2 := by
    intro n
    have hsub_summ' : Summable (fun i : { i : ι // i ∉ F } =>
        tensorSobolevWeight (I := I) (M := M) (i : ι) σ' *
          ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2) :=
      (hsumm' n).subtype _
    have hsub_summ'' : Summable (fun i : { i : ι // i ∉ F } =>
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
            ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2)) :=
      ((hsumm'' n).subtype _).mul_left _
    calc
      ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' *
              ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2
          ≤ ∑' i : { i : ι // i ∉ F },
              Λ ^ (σ' - σ'') *
                (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
                  ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2) :=
            hsub_summ'.tsum_le_tsum
              (fun i => hcompl_bd n i.1 i.2) hsub_summ''
      _ = Λ ^ (σ' - σ'') *
            ∑' i : { i : ι // i ∉ F },
              tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
                ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2 :=
            tsum_mul_left
      _ ≤ Λ ^ (σ' - σ'') *
            ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' *
              ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            refine ((hsumm'' n).subtype _).tsum_le_tsum_of_inj
              Subtype.val Subtype.val_injective (fun i _ => ?_) (fun i => le_refl _)
              (hsumm'' n)
            have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
              tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
            positivity
      _ ≤ Λ ^ (σ' - σ'') * C ^ 2 := by
            rw [hmass'' n]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            have hnn : (0 : ℝ) ≤ ‖d n‖ := norm_nonneg _
            nlinarith [hCbd n, hnn, hC]

  have hcoeff0 : ∀ i : ι,
      Tendsto (fun n => ‖timeModeCoeff (I := I) (M := M) (d n) i‖) atTop (𝓝 0) := by
    intro i
    have h := norm_timeModeCoeff_tendsto_zero_of_norm_tendsto_zero (I := I) (M := M)
      (fun n => timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hσσ'.trans hσ'σ''.le) (d n)) hlow i
    refine h.congr (fun n => ?_)
    rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) (hσσ'.trans hσ'σ''.le) (d n) i]
  have hfin0 : Tendsto (fun n =>
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' *
        ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2)
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum (s := F)
      (f := fun i n => tensorSobolevWeight (I := I) (M := M) i σ' *
        ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2)
      (a := fun _ : ι => (0 : ℝ))
      (fun i _ => by
        have hc : Tendsto
            (fun n => ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2)
            atTop (𝓝 (0 ^ 2)) :=
          (hcoeff0 i).pow 2
        rw [show (0 : ℝ) ^ 2 = 0 by ring] at hc
        have := hc.const_mul (tensorSobolevWeight (I := I) (M := M) i σ')
        simpa using this)
    simpa using h

  rw [Metric.tendsto_atTop] at hfin0
  obtain ⟨N, hN⟩ := hfin0 (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩

  have hsplit_sum :
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' *
          ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' *
            ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2) +
          ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' *
              ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2 :=
    ((hsumm' n).sum_add_tsum_subtype_compl F).symm
  have hfin_lt : ∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i σ' *
        ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2 < ε / 2 := by
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' *
            ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2
        ≤ |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' *
            ‖timeModeCoeff (I := I) (M := M) (d n) i‖ ^ 2| := le_abs_self _
      _ < ε / 2 := hd
  have htail_lt : ∑' i : { i : ι // i ∉ F },
      tensorSobolevWeight (I := I) (M := M) (i : ι) σ' *
        ‖timeModeCoeff (I := I) (M := M) (d n) (i : ι)‖ ^ 2 < ε / 2 :=
    lt_of_le_of_lt (htail n) hΛtail
  have hbound : ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 < ε := by
    rw [hnormsq n, hsplit_sum]
    linarith
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 := sq_nonneg _
  rwa [abs_of_nonneg hnn]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma norm_le_sqrt_of_weightedMass_le {σ'' : ℝ} {T : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s σ'') T) {B : ℝ}
    (hB : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i σ'' *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 ≤ B) :
    ‖f‖ ≤ Real.sqrt B := by
  have hsq : ‖f‖ ^ 2 ≤ B := by
    rw [norm_sq_eq_tsum_timeModeCoeff (I := I) (M := M) h_compact (f := f)]; exact hB
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg f)] at h

theorem timeL2_tendsto_of_tendsto_of_uniform_weightedMass
    {σ σ' σ'' : ℝ} {T : ℝ}
    (hσσ' : σ ≤ σ') (hσ'σ'' : σ' < σ'')
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u : ℕ → timeL2 (tensorHs (I := I) (M := M) g r s σ'') T)
    (ulim : timeL2 (tensorHs (I := I) (M := M) g r s σ'') T) {B : ℝ}
    (hconv : Tendsto (fun n =>
        timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) (u n)) atTop
        (𝓝 (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) ulim)))
    (humass : ∀ n, ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i σ'' *
        ‖timeModeCoeff (I := I) (M := M) (u n) i‖ ^ 2 ≤ B)
    (hlmass : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i σ'' *
        ‖timeModeCoeff (I := I) (M := M) ulim i‖ ^ 2 ≤ B) :
    Tendsto (fun n =>
      ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (u n - ulim)‖) atTop (𝓝 0) := by
  set d : ℕ → timeL2 (tensorHs (I := I) (M := M) g r s σ'') T :=
    fun n => u n - ulim with hd_def
  have hBnn : 0 ≤ B :=
    le_trans (tsum_nonneg (fun i => by
      have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
      positivity)) hlmass
  have hCbd : ∀ n, ‖d n‖ ≤ 2 * Real.sqrt B := by
    intro n
    have hu : ‖u n‖ ≤ Real.sqrt B :=
      norm_le_sqrt_of_weightedMass_le (I := I) (M := M) h_compact (u n) (humass n)
    have hl : ‖ulim‖ ≤ Real.sqrt B :=
      norm_le_sqrt_of_weightedMass_le (I := I) (M := M) h_compact ulim hlmass
    calc ‖d n‖ = ‖u n - ulim‖ := by rw [hd_def]
      _ ≤ ‖u n‖ + ‖ulim‖ := norm_sub_le _ _
      _ ≤ Real.sqrt B + Real.sqrt B := add_le_add hu hl
      _ = 2 * Real.sqrt B := by ring
  have hlow : Tendsto (fun n =>
      ‖timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hσσ'.trans hσ'σ''.le) (d n)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n =>
        timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) (u n) -
        timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) ulim) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hconv
    have heq : ∀ n,
        timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (hσσ'.trans hσ'σ''.le) (u n) -
          timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (hσσ'.trans hσ'σ''.le) ulim =
          timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (hσσ'.trans hσ'σ''.le) (d n) := by
      intro n; rw [hd_def, map_sub]
    rw [tendsto_zero_iff_norm_tendsto_zero] at hsub
    exact hsub.congr (fun n => by rw [heq n])
  exact timeL2_norm_tendsto_zero_of_low_tendsto_of_uniform (I := I) (M := M)
    hσσ' hσ'σ'' h_compact d (by positivity) hCbd hlow

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
