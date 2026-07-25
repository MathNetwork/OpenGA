import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RankRReadingDominationUniformSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormDiscreteLogConvex
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormHolderIntegrability
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GagliardoNirenbergLpFiberNormCovGradFrameSum
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormKatoSecondCovDerivBound
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormWeightedCovIBP
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormSecondOrderInterp


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section GeneralValenceRS

open Bundle Tensor0SBundle Tensor0SNabla TensorRSNabla TensorMultilinear

private noncomputable def lpFiberJetLadder_rs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (u : Integral.L2.SmoothCcTensor g r s)
    (Λ₀ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then
    Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
  else if i = k then
    Integral.L2.tensorL2Norm (I := I) g r (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g r s k u).toFun
  else
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
      (M := M) (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact Integral.Connection.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g r s _

private theorem lpFiberJet_logConvex_iteratedCovGrad_rs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (u : Integral.L2.SmoothCcTensor g r s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ i : ℕ, i + 1 < k →
          (lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ (i + 1)) ^ 2 ≤
            K * lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ i *
              lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ (i + 2) := by
  classical
  obtain ⟨Kf, hKf1, hfin⟩ := secondOrderInterp_lpFiberJet_fin_rs (I := I) (M := M) g k r hk
  obtain ⟨Ks, hKs1, hsupc⟩ := secondOrderInterp_lpFiberJet_sup_rs (I := I) (M := M) g k r hk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _

  refine ⟨max (max Kf 1) (Ks * (1 / V) + Ks), ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro u Λ₀ hΛ₀ hsup
  set K : ℝ := max (max Kf 1) (Ks * (1 / V) + Ks) with hKdef
  have hKf_le : Kf ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKsV_le : Ks * (1 / V) + Ks ≤ K := le_max_right _ _

  set J : ℕ → ℝ := fun i =>
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k)) with hJdef
  have hJnn : ∀ i, 0 ≤ J i := by
    intro i; rw [hJdef]
    exact Real.rpow_nonneg (integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + i) x _) _)) _

  have hread : ∀ i, 1 ≤ i → lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ i = J i := by
    intro i hi1
    rcases eq_or_ne i k with hik | hik
    · subst hik
      rw [hJdef]
      simp only [lpFiberJetLadder_rs, if_neg (show i ≠ 0 by omega), if_true]
      set t : ℝ := Integral.L2.tensorL2Norm (I := I) g r (s + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u).toFun with ht
      have htnn : 0 ≤ t := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _
      have hbridge : (∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u).toSection x)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) = t ^ 2 := by
        rw [ht, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r (s + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u)]
      have hii : (i : ℝ) / i = 1 := by
        rw [div_self]; exact_mod_cast (show i ≠ 0 by omega)
      symm
      calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u).toSection x)) ^ ((i : ℝ) / i)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * i))
          = (∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u).toSection x)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((1 : ℝ) / 2) := by
              rw [hii]
              simp only [Real.rpow_one]
              rw [show (i : ℝ) / (2 * i) = 1 / 2 by field_simp]
        _ = (t ^ 2) ^ ((1 : ℝ) / 2) := by rw [hbridge]
        _ = t := by
              rw [← Real.rpow_natCast t 2, ← Real.rpow_mul htnn]
              norm_num
    · rw [hJdef]
      simp only [lpFiberJetLadder_rs, if_neg (show i ≠ 0 by omega), if_neg hik]

  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · have hmuzero : (Integral.Measure.riemannianVolumeMeasure I M g) = 0 := by
      have hfin : (Integral.Measure.riemannianVolumeMeasure I M g) Set.univ ≠ ⊤ := by
        haveI := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
          (I := I) (M := M) g
        exact (MeasureTheory.measure_ne_top _ _)
      have htoReal0 : ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal = 0 := by
        have hsqrt0 : Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
            = 0 := by rw [← hV]; exact hV0.symm
        have hle := Real.sqrt_eq_zero'.mp hsqrt0
        exact le_antisymm hle ENNReal.toReal_nonneg
      have huniv0 : (Integral.Measure.riemannianVolumeMeasure I M g) Set.univ = 0 := by
        rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at htoReal0
      exact MeasureTheory.Measure.measure_univ_eq_zero.mp huniv0
    have hJ0 : ∀ i, 1 ≤ i → J i = 0 := by
      intro i hi
      simp only [hJdef, hmuzero, MeasureTheory.integral_zero_measure]
      apply Real.zero_rpow
      have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      positivity
    intro i _hik
    have h1 : lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ (i + 1) = 0 := by
      rw [hread (i + 1) (by omega), hJ0 (i + 1) (by omega)]
    have h3 : lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ (i + 2) = 0 := by
      rw [hread (i + 2) (by omega), hJ0 (i + 2) (by omega)]
    rw [h1, h3]; ring_nf
    positivity
  · have hVne : V ≠ 0 := ne_of_gt hVpos
    intro i hik
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [hread 1 (by omega), hread 2 (by omega)]
      have hc0eq : lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ 0 = Λ₀ * V := by
        rw [show lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ 0
              = Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
            from by unfold lpFiberJetLadder_rs; rw [if_pos rfl], ← hV]
      rw [hc0eq]

      have hstep := hsupc s u Λ₀ hΛ₀ hsup

      have e1 : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [show ((k : ℝ) / 1) = ((k : ℝ) / ((1 : ℕ) : ℝ)) by norm_num,
          show ((1 : ℝ) / (2 * k)) = (((1 : ℕ) : ℝ) / (2 * k)) by norm_num,
          show ((k : ℝ) / 2) = ((k : ℝ) / ((2 : ℕ) : ℝ)) by norm_num,
          show ((2 : ℝ) / (2 * k)) = (((2 : ℕ) : ℝ) / (2 * k)) by norm_num] at hstep

      have hstep' : (J 1) ^ 2 ≤ Ks * Λ₀ * J 2 := hstep
      refine le_trans hstep' ?_
      have hJ2nn : 0 ≤ J 2 := hJnn 2
      have hreconc : Ks * Λ₀ ≤ K * (Λ₀ * V) := by
        have hKsKV : Ks ≤ K * V := by
          have hKsdivV : Ks / V ≤ K := by
            have hKsle : Ks ≤ Ks * (1 / V) + Ks := by
              have : 0 ≤ Ks * (1 / V) := by positivity
              linarith
            have : Ks * (1 / V) ≤ K := le_trans (by linarith) hKsV_le
            rw [div_eq_mul_one_div]; exact le_trans this (le_refl _)
          calc Ks = (Ks / V) * V := by field_simp
            _ ≤ K * V := mul_le_mul_of_nonneg_right hKsdivV hVnn
        nlinarith [hKsKV, hΛ₀, mul_nonneg (le_trans zero_le_one hKs1) hΛ₀]
      exact mul_le_mul_of_nonneg_right hreconc hJ2nn
    · rw [hread (i + 1) (by omega), hread i hipos, hread (i + 2) (by omega)]
      have hstep := hfin (s + i) (PDE.RicciFlow.iteratedCovGrad (I := I) g r s i u) i hipos hik

      have e1 : ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      have e2 : ((i : ℝ) + 2) = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [e1, e2] at hstep

      refine le_trans hstep ?_
      have hJinn : 0 ≤ J i := hJnn i
      have hJi2nn : 0 ≤ J (i + 2) := hJnn (i + 2)
      have hbase : Kf * J i * J (i + 2) ≤ K * J i * J (i + 2) := by
        apply mul_le_mul_of_nonneg_right _ hJi2nn
        apply mul_le_mul_of_nonneg_right hKf_le hJinn
      exact le_trans (le_of_eq (by rfl)) hbase

theorem exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g r s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s j u).toSection x)) ^ ((k : ℝ) / j)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
            C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
              (Integral.L2.tensorL2Norm (I := I) g r (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g r s k u).toFun) ^ (2 * (j : ℝ) / k) := by
  classical
  obtain ⟨K, hK1, hlc⟩ := lpFiberJet_logConvex_iteratedCovGrad_rs (I := I) (M := M) g r s k _hk
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _
  have hmax1 : (1 : ℝ) ≤ max 1 V := le_max_left _ _
  have hmaxV : V ≤ max 1 V := le_max_right _ _
  have hmax_nn : 0 ≤ max 1 V := le_trans zero_le_one hmax1

  set C : ℝ := K ^ (2 * k ^ 2) * (max 1 V) ^ 2 with hC
  have hKnn : 0 ≤ K := le_trans zero_le_one hK1
  have hC_nn : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity

  set c : ℕ → ℝ := fun i => lpFiberJetLadder_rs (I := I) (M := M) g r s k u Λ₀ i with hc_def

  have hc_nn : ∀ i, 0 ≤ c i := by
    intro i
    rw [hc_def]
    simp only [lpFiberJetLadder_rs]
    split_ifs with hi0 hik
    · exact mul_nonneg hΛ₀ hVnn
    · exact Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + k) _
    · exact Real.rpow_nonneg (integral_nonneg (fun x =>
        Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + i) x _) _)) _

  have hc_lc : ∀ i, i + 1 < k → (c (i + 1)) ^ 2 ≤ K * c i * c (i + 2) := by
    intro i hik; rw [hc_def]; exact hlc u Λ₀ hΛ₀ hsup i hik

  have hpow : (c j) ^ k ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j :=
    discrete_log_convex_power_interpolation c hc_nn K hK1 j k hc_lc hj0 hjk

  have hc0_eq : c 0 = Λ₀ * V := by
    simp only [hc_def, lpFiberJetLadder_rs, if_pos rfl]
    rw [hV]
  have hck_eq : c k = Integral.L2.tensorL2Norm (I := I) g r (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g r s k u).toFun := by
    simp only [hc_def, lpFiberJetLadder_rs, if_neg (show k ≠ 0 by omega), if_true]
  have hcj_sq : (c j) ^ 2 =
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) := by
    simp only [hc_def, lpFiberJetLadder_rs, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ k by omega)]
    set Iint : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s j u).toSection x)) ^ ((k : ℝ) / j)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g) with hIint
    have hIint_nn : 0 ≤ Iint := integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + j) x _) _)
    have hexp : (j : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (j : ℝ) / k := by
      push_cast
      rw [mul_comm, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.rpow_natCast (Iint ^ ((j : ℝ) / (2 * k))) 2,
        ← Real.rpow_mul hIint_nn, hexp]

  have hc0_nn : 0 ≤ c 0 := hc_nn 0
  have hck_nn : 0 ≤ c k := hc_nn k
  have hcj_nn : 0 ≤ c j := hc_nn j

  have hpow_sq : ((c j) ^ 2) ^ k ≤
      (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
    have hrw : ((c j) ^ 2) ^ k = ((c j) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hrw]
    have hbase_nn : 0 ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j := by positivity
    calc ((c j) ^ k) ^ 2 ≤ (K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hpow 2
      _ = (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf

  have hcj2_nn : 0 ≤ (c j) ^ 2 := by positivity
  have hmono : (((c j) ^ 2) ^ k) ^ ((k : ℝ)⁻¹) ≤
      ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hpow_sq (by positivity)
  rw [Real.pow_rpow_inv_natCast hcj2_nn hk0] at hmono

  have hcast_sub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
  have hrhs : ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) =
      (K ^ (2 * k ^ 2)) * ((c 0) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * ((c k) ^ 2) ^ ((j : ℝ) / k) := by
    have hKpow_nn : 0 ≤ (K ^ (k ^ 3)) ^ 2 := by positivity
    have hc02_nn : 0 ≤ ((c 0) ^ 2) ^ (k - j) := by positivity
    have hck2_nn : 0 ≤ ((c k) ^ 2) ^ j := by positivity
    rw [Real.mul_rpow (by positivity) hck2_nn, Real.mul_rpow hKpow_nn hc02_nn]
    congr 1
    · congr 1
      · have hexpK : ((k ^ 3 * 2 : ℕ) : ℝ) * (k : ℝ)⁻¹ = ((2 * k ^ 2 : ℕ) : ℝ) := by
          push_cast
          field_simp
        rw [← pow_mul, ← Real.rpow_natCast K (k ^ 3 * 2), ← Real.rpow_mul hKnn, hexpK,
          Real.rpow_natCast K (2 * k ^ 2)]
      · have hexp0 : ((k - j : ℕ) : ℝ) * (k : ℝ)⁻¹ = (1 : ℝ) - (j : ℝ) / k := by
          rw [hcast_sub]
          field_simp
        rw [← Real.rpow_natCast ((c 0) ^ 2) (k - j), ← Real.rpow_mul (by positivity), hexp0]
    · rw [← Real.rpow_natCast ((c k) ^ 2) j, ← Real.rpow_mul (by positivity), div_eq_mul_inv]
  rw [hrhs] at hmono

  rw [hcj_sq] at hmono
  rw [hc0_eq, hck_eq] at hmono

  set ak : ℝ := Integral.L2.tensorL2Norm (I := I) g r (s + k)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g r s k u).toFun with hak_def
  have hak_nn : 0 ≤ ak := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + k) _

  have hak_pow : (ak ^ 2) ^ ((j : ℝ) / k) = ak ^ (2 * (j : ℝ) / k) := by
    rw [← Real.rpow_natCast ak 2, ← Real.rpow_mul hak_nn]
    congr 1
    push_cast; ring

  have hweight_nn : 0 ≤ (1 : ℝ) - (j : ℝ) / k := by
    have : (j : ℝ) / k ≤ 1 := by
      rw [div_le_one hkRpos]; exact_mod_cast le_of_lt hjk
    linarith
  have hweight_le1 : (1 : ℝ) - (j : ℝ) / k ≤ 1 := by
    have : 0 ≤ (j : ℝ) / k := by positivity
    linarith
  have hLV_pow : ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) =
      Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast Λ₀ 2, ← Real.rpow_mul hΛ₀]
    norm_num

  have hV2_le : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (max 1 V) ^ 2 := by
    have hV2_nn : 0 ≤ V ^ 2 := by positivity
    have h2max : (1 : ℝ) ≤ (max 1 V) ^ 2 := by
      have := pow_le_pow_left₀ (zero_le_one) hmax1 2
      rwa [one_pow] at this
    rcases le_total (V ^ 2) 1 with hle | hge
    · have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ 1 :=
        Real.rpow_le_one hV2_nn hle hweight_nn
      linarith
    · have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (V ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hge hweight_le1
      rw [Real.rpow_one] at h1
      have hV2_le_max : V ^ 2 ≤ (max 1 V) ^ 2 := pow_le_pow_left₀ hVnn hmaxV 2
      linarith

  calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g r s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k)
      ≤ K ^ (2 * k ^ 2) * ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * (ak ^ 2) ^ ((j : ℝ) / k) :=
        hmono
    _ = K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by rw [hLV_pow, hak_pow]
    _ ≤ K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (max 1 V) ^ 2) *
          ak ^ (2 * (j : ℝ) / k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hV2_le (by positivity)
    _ = (K ^ (2 * k ^ 2) * (max 1 V) ^ 2) * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by ring
    _ = C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) * ak ^ (2 * (j : ℝ) / k) := by rw [hC]

end GeneralValenceRS

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
