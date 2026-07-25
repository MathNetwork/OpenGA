import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MildSolutionTimeH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DuhamelSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingTimeBootstrap
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.PointwiseDeriv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorL2_ext_of_tensorL2Coeff_jsmooth
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator
      (Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g r s))
    {S T : TensorL2 r s g}
    (h : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact S i =
      tensorL2Coeff (I := I) (M := M) h_compact T i) :
    S = T := by
  classical
  set b := Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hb
  apply b.repr.injective
  ext i
  have hS : (b.repr S) i = tensorL2Coeff (I := I) (M := M) h_compact S i := rfl
  have hT : (b.repr T) i = tensorL2Coeff (I := I) (M := M) h_compact T i := rfl
  rw [hS, hT, h i]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem ccTensorBilinSymm_zero_apply_jsmooth (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
    (zero_smul ℝ _).symm
  rw [h0, ccTensorBilinSymm_smul]
  ring


private theorem realizedSolField_continuousOn_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T₁ : ℝ} (_hT₁_pos : 0 < T₁)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    ContinuousOn
      (fun t : ℝ => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T₁) := by
  classical

  set σ : ℝ := (a : ℝ) + 2 with hσ_def
  set p : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hp_def
  set σ' : ℝ := σ + p with hσ'_def
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmodemass 0 σ' (by
    rw [hσ'_def, hσ_def, hp_def]; positivity)

  have hmass : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      tensorSobolevWeight (I := I) (M := M) i σ' * (φ i t) ^ 2 ≤ Cmaj i := by
    intro i t ht
    have := hCmaj_le i t ht
    rwa [iteratedDeriv_zero] at this

  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T₁, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hcoeff t ht i

  have hwthr : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by
    rw [hσ'_def, hp_def]; ring_nf; linarith
  exact tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g₀ hwthr
    (s := Set.Icc (0 : ℝ) T₁)
    (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)) φ hcoeff'
    (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum hmass


private theorem realizedFamily_flowDeriv_of_repr
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
      SmoothCcTensor g₀ 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w)
    {T : ℝ} (_hT : 0 < T) (_hT1 : T ≤ 1)
    {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (_hd₂F_le : d₂F ≤ T) (hT₁_le_d2F : T₁ ≤ d₂F)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Nat.cast_nonneg a) (timeH1.toFun u t))
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (hForceRepr : ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Nsec (F t) hδ_lt (hδ t))) i) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
        (F_RHS
          (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
        (Set.Ici 0) t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc

  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)

  set φ' : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => f i s - TensorEigenIdx.lambda (I := I) (M := M) i * φ i s with hφ'_def
  have hφ_deriv : ∀ i (s : ℝ), HasDerivAt (φ i) (φ' i s) s := by
    intro i s
    exact perModeConv_hasDerivAt (TensorEigenIdx.lambda (I := I) (M := M) i)
      (hf_smooth i).continuous s

  have hφ_mass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    exact perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ

  have hcoeff : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) i = φ i s := by
    intro s hs i
    rw [h_pin s hs, tensorHsToL2_tensorL2Coeff]
    have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
    have hid := hf_id s hs_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]

  have hu_mem : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vH =
          SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s) := by
    intro s hs σ hσ
    refine allHs_of_weighted_summable_pub (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) (fun τ hτ => ?_) σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj⟩ := hφ_mass 0 τ hτ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hCmaj_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i τ) (sq_nonneg _)
    · have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
      have h := hCmaj i s hs_icc
      rw [iteratedDeriv_zero] at h
      rw [hcoeff s hs i]
      exact h

  have hforcing := hForceRepr

  have ha_lossy : 2 * Module.finrank ℝ E + 4 ≤ a := by omega

  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) :=
    tensorEigen_summable_negpow (I := I) (M := M) g₀ (sW : ℝ) hsW_gt

  intro t ht x v w

  obtain ⟨C, hC_pos, hC_bd⟩ :=
    abs_eigenBilinScalar_le (I := I) (M := M) g₀ a ha_lossy x v w
  set K : ℝ := Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) with hK_def
  have hK_nn : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

  have hψ_bd : ∀ i, |eigenBilinScalar (I := I) g₀ x v w i| ≤
      (C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) := by
    intro i
    have := hC_bd i
    rw [hK_def]
    calc |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ C * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) *
            (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := this
      _ = C * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) := by ring

  have hprod_summable : ∀ (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) *
          (c i) ^ 2) →
      Summable (fun i => c i * eigenBilinScalar (I := I) g₀ x v w i) := by
    intro c hc_sum

    have hdom : Summable (fun i =>
        (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) *
            (c i) ^ 2)) +
          (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) :=
      ((hc_sum.mul_left (C * K)).mul_left (1 / 2)).add
        ((hweyl.mul_left (C * K)).mul_left (1 / 2))
    refine Summable.of_norm_bounded hdom (fun i => ?_)
    have hCK_nn : 0 ≤ C * K := mul_nonneg hC_pos.le hK_nn
    have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)
    have hwasW_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _

    have hsqrt_split : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) =
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      rw [← Real.sqrt_mul hwasW_nn]
      congr 1
      unfold tensorSobolevWeight
      rw [← Real.rpow_add (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i))]
      congr 1; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |c i| * |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ |c i| * ((C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))) :=
          mul_le_mul_of_nonneg_left (hψ_bd i) (abs_nonneg _)
      _ = (C * K) * (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [hsqrt_split]; ring
      _ ≤ (C * K) * ((1 / 2) * ((|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ)))) ^ 2 +
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) ^ 2)) := by
          have hAB : (C * K) * (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
                ((a : ℝ) + (sW : ℝ)))) *
              Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              (C * K) * ((|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
                ((a : ℝ) + (sW : ℝ)))) *
                Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) := by ring
          rw [hAB]
          refine mul_le_mul_of_nonneg_left ?_ hCK_nn
          nlinarith [sq_nonneg (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ))) -
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))]
      _ = (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ)) * (c i) ^ 2)) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt hwasW_nn, Real.sq_sqrt hwneg_nn, sq_abs]; ring

  have hsum_series : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      Summable (fun i => φ i s * eigenBilinScalar (I := I) g₀ x v w i) := by
    intro s hs
    refine hprod_summable (fun i => φ i s) ?_
    obtain ⟨B, hB_sum, hB_le⟩ := hφ_mass 0 ((a : ℝ) + (sW : ℝ)) (by positivity)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _) (sq_nonneg _)
    · have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
      have h := hB_le i s hs_icc
      rwa [iteratedDeriv_zero] at h

  obtain ⟨Bφ', hBφ'_sum, hBφ'_le⟩ := hφ_mass 1 ((a : ℝ) + (sW : ℝ)) (by positivity)

  set u_bd : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => (1 / 2 : ℝ) * ((C * K) * Bφ' i) +
      (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))
    with hu_bd_def
  have hu_bd_sum : Summable u_bd :=
    ((hBφ'_sum.mul_left (C * K)).mul_left (1 / 2)).add
      ((hweyl.mul_left (C * K)).mul_left (1 / 2))

  have hφ'_term_bd : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      ‖φ' i s * eigenBilinScalar (I := I) g₀ x v w i‖ ≤ u_bd i := by
    intro i s hs
    have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
    have hCK_nn : 0 ≤ C * K := mul_nonneg hC_pos.le hK_nn
    have hwasW_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hsqrt_split : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) =
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      rw [← Real.sqrt_mul hwasW_nn]
      congr 1
      unfold tensorSobolevWeight
      rw [← Real.rpow_add (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i))]
      congr 1; ring
    have hbd1 : tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) *
        (φ' i s) ^ 2 ≤ Bφ' i := by
      have h := hBφ'_le i s hs_icc
      rwa [iteratedDeriv_one, show deriv (φ i) s = φ' i s from (hφ_deriv i s).deriv] at h
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ' i s| * |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ |φ' i s| * ((C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))) :=
          mul_le_mul_of_nonneg_left (hψ_bd i) (abs_nonneg _)
      _ = (C * K) * ((|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)))) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) := by
          rw [hsqrt_split]; ring
      _ ≤ (C * K) * ((1 / 2) * ((|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)))) ^ 2 +
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCK_nn
          nlinarith [sq_nonneg (|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ))) -
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))]
      _ = (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)) * (φ' i s) ^ 2)) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt hwasW_nn, Real.sq_sqrt hwneg_nn, sq_abs]; ring
      _ ≤ (1 / 2 : ℝ) * ((C * K) * Bφ' i) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (le_refl _)
          exact mul_le_mul_of_nonneg_left hbd1 hCK_nn

  have hG_deriv : HasDerivWithinAt
      (fun s : ℝ => ∑' i, φ i s * eigenBilinScalar (I := I) g₀ x v w i)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Icc (0 : ℝ) T₁) t := by
    have ht_icc : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, le_of_lt ht.2⟩
    refine hasDerivWithinAt_tsum
      (f := fun i s => φ i s * eigenBilinScalar (I := I) g₀ x v w i)
      (f' := fun i s => φ' i s * eigenBilinScalar (I := I) g₀ x v w i)
      (u := u_bd) (s := Set.Icc (0 : ℝ) T₁)
      (fun i z _hz => ?_) (fun i z hz => hφ'_term_bd i z hz) hu_bd_sum
      (convex_Icc 0 T₁) ht_icc (hsum_series t ht_icc) ht_icc
    exact ((hφ_deriv i z).hasDerivWithinAt).mul_const _

  have hG_eq : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      ccTensorBilinSymm (I := I) g₀ (F s) x v w =
        ∑' i, φ i s * eigenBilinScalar (I := I) g₀ x v w i := by
    intro s hs
    have heig := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) (hu_mem s hs) (F s)
      (SmoothCcTensor.toL2_apply (F s)) x v w ?_
    · rw [heig]
      exact tsum_congr (fun i => by rw [hcoeff s hs i])
    · refine (hsum_series s hs).congr (fun i => ?_)
      rw [hcoeff s hs i]

  have hG_deriv' : HasDerivWithinAt
      (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Icc (0 : ℝ) T₁) t := by
    refine hG_deriv.congr (fun s hs => hG_eq s hs) ?_
    exact hG_eq t ⟨ht.1, le_of_lt ht.2⟩
  have hIci : HasDerivWithinAt
      (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Ici (0 : ℝ)) t := by
    have hmem : Set.Icc (0 : ℝ) T₁ ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      have hsub : Set.Ici (0 : ℝ) ∩ Set.Iio T₁ ⊆ Set.Icc (0 : ℝ) T₁ :=
        fun s hs => ⟨hs.1, le_of_lt hs.2⟩
      exact Filter.mem_of_superset
        (inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)) hsub
    exact (hG_deriv'.mono_of_mem_nhdsWithin hmem)

  have hval : (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) =
      F_RHS
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w := by
    set gDT := tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgDT_def

    set R : SmoothCcTensor g₀ 0 2 :=
      Nsec (F t) hδ_lt (hδ t) + rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t)
      with hR_def

    have hR_split : R = Nsec (F t) hδ_lt (hδ t) +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t) := rfl

    have hcoord : ∀ i, φ' i t =
        tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i := by
      intro i
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, le_of_lt ht.2⟩

      have hf_coord := hforcing t ht i

      have hraw : tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i =
          -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i :=
        tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F t) i
      rw [hcoeff t ht_icc i] at hraw
      rw [hR_split, ContinuousLinearMap.map_add, tensorL2Coeff_add, ← hf_coord, hraw, hφ'_def]
      ring

    have hR_mem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vH : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vH =
            SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R := by
      intro σ hσ
      refine allHs_of_weighted_summable_pub (I := I) (M := M) g₀
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) (fun τ _hτ => ?_) σ hσ
      exact smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ τ R hc

    have hR_sum : Summable (fun i => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i *
        eigenBilinScalar (I := I) g₀ x v w i) := by
      refine (hprod_summable (fun i => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i) ?_)
      exact smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
        ((a : ℝ) + (sW : ℝ)) R hc
    have heig := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) hR_mem R
      (SmoothCcTensor.toL2_apply R) x v w hR_sum

    rw [show (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) =
        ∑' i, tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i *
            eigenBilinScalar (I := I) g₀ x v w i from
      tsum_congr (fun i => by rw [hcoord i])]
    rw [← heig, hR_def]
    exact hRepr (F t) hδ_lt (hδ t) x v w
  rw [← hval]
  exact hIci

private theorem realizedFamily_jointChartGramSmooth
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) :=
  jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
    g hT T_rep hδ_lt hδ φ hφ_smooth hcoeff hmodemass


private theorem forcingSmoothTimeCoordsSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) :=
  deTurckForcing_smoothTimeCoordinateFamilySymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
    hTT₀ gforce hforce hgforce


private theorem forcingSmoothCoordsRealizeSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (_htrace : timeH1.trace0 _ T u = 0) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩ :=
    forcingSmoothTimeCoordsSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce
      hgforce
  have hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
    intro i
    have hrep_coeff : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (F t).coeff i) := hF_rep.fun_comp (fun S => S.coeff i)
    refine hrep_coeff.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with s hs
    exact hF_coeff s hs i
  refine ⟨d₂, hd₂_pos, hd₂_le, f, hf_smooth, hf_mass, ?_, hforce_coord⟩
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  intro t ht i
  rw [hduh, tensorHsToL2_tensorL2Coeff (Nat.cast_nonneg a)]
  have hid := carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
    (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hT hT1 hd₂_pos hd₂_le h_compact gforce
    (F := F) hF_coord_cont hF_rep i ht
  rw [hid]
  refine perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
    (f₁ := Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F (p : ℝ)).coeff i))
    (f₂ := f i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with s hs
  rw [Set.IccExtend_of_mem hd₂_pos.le _ hs, hF_coeff s hs i]


private theorem realizedSol_solField_smallnessHorizon_Ha2Symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (htrace : timeH1.trace0 _ T u = 0)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ := by
  classical
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, _⟩ :=
    forcingSmoothCoordsRealizeSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ u gforce
      hduh hforce hgforce htrace
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le, hbound⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₂F_pos f
      (fun i => (hf_smooth i).continuous)
      (B := B) hB_sum
      (fun i s hs => by
        have h := hB_le i s hs
        rwa [iteratedDeriv_zero] at h)
      hR₀
  refine ⟨d₂, hd₂_pos, le_trans hd₂_le hd₂F_le, ?_⟩
  intro t ht S hS
  have ht_d2F : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hd₂_le⟩
  set W : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) :=
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S with hW_def
  have hWcoeff : ∀ i, W.coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t := by
    intro i
    rw [hW_def, smoothCcToTensorHs_coeff, hS, ← hf_id t ht_d2F i]
  have := hbound t ht W hWcoeff
  rwa [hW_def] at this

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm) in

private theorem realizedForcingCoord_eq_smoothNSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (_hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a ha_super)
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a ha_super)).choose)
    {T₁ : ℝ} (hT₁_pos : 0 < T₁) (hT₁_le : T₁ ≤ T)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (_hd₂F_le : d₂F ≤ T) (hT₁_le_d2F : T₁ ≤ d₂F)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)] f i)
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Nat.cast_nonneg a) (timeH1.toFun u t))
    (hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
        (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a
          ha_super)).1) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ_lt
              (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t) (hδ t)))) i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ i, tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [h_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]
  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
  have hfield_cont : ContinuousOn
      (fun t : ℝ => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T₁) :=
    realizedSolField_continuousOn_smoothCcToTensorHs (I := I) (M := M) g₀ a hT₁_pos F φ hφ_smooth
      hcoeff hmodemass
  have hu_eq : u = recentredCarrier (I := I) (M := M) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce := by
    refine timeH1.ext ?_ ?_
    · have hinit : u.init = 0 := by
        rw [← timeH1.trace0_apply (X := tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) (T := T) u]
        exact htrace
      rw [hinit]
      simp only [recentredCarrier, timeH1.init_mk]
    · rw [hduh]
      simp only [recentredCarrier, timeH1.deriv_mk]
  have hfield_ae : (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)) := by
    have hper : ∀ i, ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T₁)),
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)).coeff i := by
      intro i
      have hsub : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hT₁_le
      have hsol := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (maxRegDuhamelSolField_coeff_ae (I := I) (M := M)
          (h_compact := hc) (a := (a : ℝ)) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce i)
      filter_upwards [hsol, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc]
        with t htsol htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := hsub htmem
      rw [htsol, tensorHs.zero_coeff, zero_add]
      have hcarr : (timeH1.toFun u t).coeff i =
          ∫ s in (0 : ℝ)..t, ((maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce).deriv s).coeff i := by
        rw [hu_eq]
        exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce i htmem'
      rw [← hcarr, smoothCcToTensorHs_coeff, h_pin t htmem, tensorHsToL2_tensorL2Coeff]
    rw [← MeasureTheory.ae_all_iff] at hper
    filter_upwards [hper] with t ht
    exact tensorHs.ext (funext fun i => ht i)
  intro t₀ ht₀ i
  set RHS : ℝ → ℝ := fun t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ_lt
          (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t) (hδ t)))) i
    with hRHS_def
  have hRHS_smoothN : ∀ t, RHS t =
      (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t) (hδ t))).coeff i := by
    intro t; rw [hRHS_def, deTurckSmoothN_coeff]
  have heqN : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i = RHS t := by
    intro t ht
    rw [hRHS_smoothN t,
      deTurckSobolevNHa2Symm_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super (F t)
        hδ_lt (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t) (hδ t)) (hball t ht)]
  obtain ⟨KN, hKN⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hRHS_cont : ContinuousOn RHS (Set.Ico (0 : ℝ) T₁) := by
    have hcomp : ContinuousOn
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i)
        (Set.Icc (0 : ℝ) T₁) := by
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)))
          (Set.Icc (0 : ℝ) T₁) :=
        hKN.continuous.comp_continuousOn hfield_cont
      exact (coeffCLM (I := I) (M := M) (g := g₀) (r := 0) (s := 2) (σ := (a : ℝ)) i).continuous
        |>.comp_continuousOn hN_cont
    refine (hcomp.mono Set.Ico_subset_Icc_self).congr (fun t ht => ?_)
    exact (heqN t ht).symm
  have hLHS_cont : ContinuousOn (f i) (Set.Ico (0 : ℝ) T₁) :=
    (hf_smooth i).continuous.continuousOn
  have hae : (f i) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico (0 : ℝ) T₁)] RHS := by
    have h1 : f i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)]
        (fun t => (gforce t).coeff i) := (hforce_coord i).symm
    have h2 : (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      hforce.fun_comp (fun S => S.coeff i)
    have hsub₁ : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hT₁_le
    have hsub₁F : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) d₂F :=
      Set.Icc_subset_Icc le_rfl hT₁_le_d2F
    have h1' : f i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (gforce t).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub₁F h1
    have h2' : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub₁ h2
    have h12 : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      h1'.trans h2'
    have h3 : (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      hfield_ae.fun_comp (fun S =>
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a S).coeff i)
    have hchain : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      h12.trans h3
    have hchain' : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self hchain
    refine hchain'.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ico] with t ht
    exact heqN t ht
  have heqOn : Set.EqOn (f i) RHS (Set.Ico (0 : ℝ) T₁) :=
    MeasureTheory.Measure.eqOn_Ico_of_ae_eq (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hae hLHS_cont hRHS_cont
  exact heqOn ht₀

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm) in

theorem deTurckRicci_forcingBootstrap_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) :
    ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
        (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
          (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
            (g_bg := g_bg) a (by omega))
          (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
            (g_bg := g_bg) a (by omega))).choose)
        (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
        (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
        (hforce : gforce =ᵐ[timeMeasure T]
          (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
        (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
        (htrace : timeH1.trace0 _ T u = 0),
      ∃ (d₂F : ℝ), 0 < d₂F ∧ d₂F ≤ T ∧
        ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ),
          (∀ i, ContDiff ℝ ∞ (f i)) ∧
          (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
            ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
              ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
                tensorSobolevWeight (I := I) (M := M) i τ *
                    (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
            tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
              perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
          ∃ (R₀ : ℝ), 0 < R₀ ∧
            (∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
              ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
                SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
                  tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Nat.cast_nonneg a) (timeH1.toFun u t) →
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀) ∧
            (∀ {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
                (_hT₁_le_d2F : T₁ ≤ d₂F)
                (Ffam : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
                (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
                  (ccTensorBilinSymm (I := I) g₀ (Ffam t)) δ)
                (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
                  SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Ffam t) =
                    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                      (Nat.cast_nonneg a) (timeH1.toFun u t))
                (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Ffam t)‖ ≤ R₀),
              ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
                f i t = tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                      (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
                        (ccTensor02Symm (I := I) (M := M) g₀ (Ffam t)) hδ_lt
                        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (Ffam t) (hδ t)))) i) := by
  classical
  intro T hT hT1 hTT₀ u gforce hduh hforce hgforce htrace
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, hforce_coord⟩ :=
    forcingSmoothCoordsRealizeSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ u gforce
      hduh hforce hgforce htrace
  refine ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, ?_⟩
  set R₀ : ℝ := (Classical.choose
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a (by omega))).1 with hR₀_def
  have hR₀_pos : 0 < R₀ :=
    (Classical.choose_spec
      (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a (by omega))).1
  refine ⟨R₀, hR₀_pos, ?_, ?_⟩
  · exact realizedSol_solField_smallnessHorizon_Ha2Symm (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 hTT₀ u gforce hduh hforce hgforce htrace hR₀_pos
  · intro T₁ hT₁_pos hT₁_le hT₁_le_d2F Ffam δ hδ_lt hδ h_pin hball
    exact realizedForcingCoord_eq_smoothNSymm (I := I) (M := M) g₀ g_bg a (by omega)
      hT hT1 hTT₀ hT₁_pos hT₁_le hd₂F_pos hd₂F_le hT₁_le_d2F u gforce hduh hforce htrace
      Ffam hδ_lt hδ f hf_id hf_smooth hf_mass hforce_coord h_pin hball


theorem maxreg_solution_jointly_smooth_representative_of_nemytskii
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (ha_eq : a = 4 * Module.finrank ℝ E + 10)
    (_Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
      SmoothCcTensor g₀ 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (htrace : timeH1.trace0 _ T u = 0)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (hd₂F_le : d₂F ≤ T)
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    {R₀ : ℝ} (_hR₀_pos : 0 < R₀)
    (hHorizon : ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀)
    (hForceRepr_fam : ∀ {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
        (_hT₁_le_d2F : T₁ ≤ d₂F)
        (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
        (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t))
        (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀),
      ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
        f i t = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (Nsec (F t) hδ_lt (hδ t))) i) :
    ∃ (T₁ : ℝ), 0 < T₁ ∧ T₁ ≤ T ∧
      ∃ (F : ℝ → SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T₁,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T₁
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc

  have hinit : u.init = 0 := by have := htrace; rwa [timeH1.trace0_apply] at this
  have hu0 : timeH1.toFun u 0 = 0 := by rw [timeH1.toFun_zero, hinit]

  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hφ_cont : ∀ i, Continuous (φ i) := fun i => (hφ_smooth i).continuous

  have hf_endpoint_sum : ∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (f i s) ^ 2) := by
    intro c hc t ht
    obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 c hc
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hB_sum.mul_left d₂F)
    · refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i c
      have hcont_sq : Continuous (fun s => (f i s) ^ 2) := ((hf_smooth i).continuous).pow 2
      have htint : (∫ s in (0 : ℝ)..t, (f i s) ^ 2) ≤ ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le hd₂F_pos.le,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set hcont_sq.integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      have hbig : tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 ≤ d₂F * B i := by

        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2)
            MeasureTheory.volume 0 d₂F :=
          (hcont_sq.const_mul _).intervalIntegrable 0 d₂F
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) MeasureTheory.volume 0 d₂F :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..d₂F,
              tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2
            ≤ ∫ _s in (0 : ℝ)..d₂F, B i := by
          refine intervalIntegral.integral_mono_on hd₂F_pos.le hi_lhs hi_const ?_
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
        exact hmono
      calc tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..t, (f i s) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 :=
            mul_le_mul_of_nonneg_left htint hwt_nn
        _ ≤ d₂F * B i := hbig

  have hF₀_exists : ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
      ∃ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht

    obtain ⟨uDuh, huDuh_coeff, huDuh_mem⟩ :=
      duhamel_into_all_tensorHs (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (t := t) ht.1 h_compact f (fun i => (hf_smooth i).continuous)
        (fun c hc => hf_endpoint_sum c hc t ht)

    have hval : uDuh = tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
      refine tensorL2_ext_of_tensorL2Coeff_jsmooth (I := I) (M := M) h_compact (fun i => ?_)
      rw [huDuh_coeff i]
      exact (hf_id t ht i).symm

    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              h_compact hσ v = uDuh := huDuh_mem
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) uDuh hmem
    refine ⟨S, ?_⟩
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = (S : TensorL2 0 2 g₀) from rfl,
      hS, hval]

  choose F₀ hF₀ using hF₀_exists
  set Fdef : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) d₂F then F₀ t ht else 0 with hFdef_def
  have hFdef_pin : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) d₂F),
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Fdef t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    simp only [hFdef_def, dif_pos ht]
    exact hF₀ t ht

  have ha_lossy : 2 * Module.finrank ℝ E + 4 ≤ a := by omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_metricCauchySchwarzBound_le_sobolevHsNorm_lossy_order (I := I) (M := M) g₀ a ha_lossy
  have hcontU : ContinuousOn (timeH1.toFun u) (Set.Icc (0 : ℝ) T) :=
    timeH1.continuousOn_toFun u
  have hwithin : ContinuousWithinAt (timeH1.toFun u) (Set.Icc (0 : ℝ) T) 0 :=
    hcontU.continuousWithinAt ⟨le_refl 0, hT.le⟩
  rw [Metric.continuousWithinAt_iff] at hwithin
  obtain ⟨d, hd_pos, hd⟩ := hwithin (1 / (2 * C)) (by positivity)

  obtain ⟨d₂, hd₂_pos, hd₂_le, hd₂⟩ := hHorizon
  set T₁ : ℝ := min (min (min T (d / 2)) d₂) d₂F with hT₁_def
  have hT₁_pos : 0 < T₁ := lt_min (lt_min (lt_min hT (by positivity)) hd₂_pos) hd₂F_pos
  have hT₁_le : T₁ ≤ T :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hT₁_le_d2 : T₁ ≤ d₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hT₁_le_d2F : T₁ ≤ d₂F := min_le_right _ _
  have hT₁_le_d : T₁ ≤ d / 2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))

  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Ioc (0 : ℝ) T₁ then Fdef t else 0 with hF_def

  have hF_zero : F 0 = 0 := by
    simp only [hF_def]
    rw [if_neg]
    intro hmem; exact absurd hmem.1 (lt_irrefl 0)

  have hF_small : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) (1 / 2) := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) T₁
    · have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T :=
        ⟨ht.1.le, le_trans ht.2 hT₁_le⟩
      have ht_icc_d2F : t ∈ Set.Icc (0 : ℝ) d₂F :=
        ⟨ht.1.le, le_trans ht.2 hT₁_le_d2F⟩
      have hpin := hFdef_pin t ht_icc_d2F
      have heq : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t) =
          timeH1.toFun u t := by
        refine tensorHs.ext (funext (fun i => ?_))
        rw [smoothCcToTensorHs_coeff, hpin, tensorHsToL2_tensorL2Coeff]
      have hdist : dist t (0 : ℝ) < d := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_le_of_lt (le_trans ht.2 hT₁_le_d) (by linarith)
      have hnorm_lt : dist (timeH1.toFun u t) (timeH1.toFun u 0) < 1 / (2 * C) :=
        hd ht_icc hdist
      have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤
          1 / (2 * C) := by
        rw [hu0, dist_eq_norm, sub_zero] at hnorm_lt
        rw [heq]
        exact hnorm_lt.le
      intro x v w
      rw [hFt]
      refine le_trans (hC (Fdef t) x v w) ?_
      have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤ 1 / 2 := by
        calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖
            ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hnorm_le hC_pos.le
          _ = 1 / 2 := by field_simp
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
        mul_nonneg hsv_nn hsw_nn
      calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
            Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
          = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
              (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
        _ ≤ (1 / 2 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
            mul_le_mul_of_nonneg_right hCN_le hmul_nn
        _ = (1 / 2 : ℝ) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring
    · have hFt : F t = 0 := by simp only [hF_def, if_neg ht]
      intro x v w
      rw [hFt, ccTensorBilinSymm_zero_apply_jsmooth]
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      rw [abs_zero]
      positivity

  have hF_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hF_zero, hu0]
      simp only [map_zero]
    · have ht_ioc : t ∈ Set.Ioc (0 : ℝ) T₁ := ⟨h0, ht.2⟩
      have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht_ioc]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
      rw [hFt]
      exact hFdef_pin t ht_icc

  have hF_cont : ContinuousOn
      (fun t : ℝ => (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)))
      (Set.Icc (0 : ℝ) T₁) := by
    have hcontU₁ : ContinuousOn (timeH1.toFun u) (Set.Icc (0 : ℝ) T₁) :=
      hcontU.mono (Set.Icc_subset_Icc le_rfl hT₁_le)
    have hcomp : ContinuousOn
        (fun t : ℝ => tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t)) (Set.Icc (0 : ℝ) T₁) :=
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a)).continuous.comp_continuousOn hcontU₁
    refine hcomp.congr (fun t ht => ?_)
    exact hF_pin t ht

  have hδ_lt : (1 / 2 : ℝ) < 1 := by norm_num

  have hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    intro t ht
    have ht_d2 : t ∈ Set.Icc (0 : ℝ) d₂ :=
      ⟨ht.1, le_trans ht.2.le hT₁_le_d2⟩
    have ht_icc₁ : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, ht.2.le⟩
    exact hd₂ t ht_d2 (F t) (hF_pin t ht_icc₁)

  have hForceRepr : ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Nsec (F t) hδ_lt (hF_small t))) i :=
    hForceRepr_fam hT₁_pos hT₁_le hT₁_le_d2F F hδ_lt hF_small hF_pin hball

  have hF_flow := realizedFamily_flowDeriv_of_repr (I := I) (M := M) g₀ a ha_super
    F_RHS Nsec hRepr hT hT1 hT₁_pos hT₁_le hd₂F_pos hd₂F_le hT₁_le_d2F u F hδ_lt hF_small
    hF_pin f hf_smooth hf_mass hf_id hForceRepr

  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [hF_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]

  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    exact hCmaj_le i t ht_icc

  have hF_joint : JointChartGramSmooth (I := I) T₁
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hF_small t)) :=
    realizedFamily_jointChartGramSmooth (I := I) (M := M) g₀ hT₁_pos F hδ_lt hF_small
      φ hφ_smooth hcoeff hmodemass
  exact ⟨T₁, hT₁_pos, hT₁_le, F, 1 / 2, hδ_lt, hF_small, hF_zero, hF_pin, hF_flow,
    hF_joint⟩

end DifferentialGeometry.PDE.RicciFlow
