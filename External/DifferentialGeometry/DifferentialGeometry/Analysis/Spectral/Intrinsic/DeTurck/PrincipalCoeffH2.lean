import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower










noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def h2JetGrid
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (x : M) : ℝ :=
  ∑ n ∈ Finset.range 3, ∑ e ∈ Finset.Nat.antidiagonalTuple n 2,
    ∏ m : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x)

private theorem h2_grid_two
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 →
      MeasureTheory.Integrable (h2JetGrid (I := I) (M := M) g T)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, h2JetGrid (I := I) (M := M) g T x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g 2
  obtain ⟨Cjet, hCjet, hjet⟩ := hs2_low2 (I := I) (M := M) g 2
  obtain ⟨Cgn, hCgn, hgn⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g 0 2 2 (by omega)
  let B : ℝ := max Cpt (max Cgn 1)
  let Q : ℝ := ∑ n ∈ Finset.range 3,
    ((Finset.Nat.antidiagonalTuple n 2).card : ℝ)
  let K : ℝ := Q * (2 * B ^ 14) * Cjet ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_trans zero_le_one (le_trans (le_max_right Cgn 1) (le_max_right Cpt _))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro T hT
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let Lam : ℝ := Cpt * N
  let R : ℝ := ‖iteratedCovGrad (I := I) g 0 2 2 T‖
  have hN : 0 ≤ N := norm_nonneg _
  have hN1 : N ≤ 1 := by simpa [N] using hT
  have hLam : 0 ≤ Lam := by dsimp [Lam]; positivity
  have hLam_sup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤ Lam ^ 2 := by
    intro x
    simpa [Lam, N, mul_pow] using hpt T x
  have hLam_le : Lam ≤ Cpt := by
    dsimp [Lam]
    nlinarith [mul_nonneg hCpt hN]
  have hmax_le : max Lam (max Cgn 1) ≤ B := by
    dsimp [B]
    exact max_le_max hLam_le (le_refl _)
  have hR : 0 ≤ R := norm_nonneg _
  have hR_sq : R ^ 2 ≤ (Cjet * N) ^ 2 := by
    have hsingle : ‖iteratedCovGrad (I := I) g 0 2 2 T‖ ^ 2 ≤
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
      exact Finset.single_le_sum (s := Finset.range 3)
        (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
        (fun j _ => sq_nonneg _)
        (show 2 ∈ Finset.range 3 by norm_num)
    exact hsingle.trans (hjet T)
  have hGNP : ∀ j : ℕ, 0 < j → j < 2 →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j T).toSection x)) ^ ((2 : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ ((j : ℝ) / (2 : ℝ)) ≤
        Cgn * Lam ^ (2 * (1 - (j : ℝ) / (2 : ℝ))) *
          R ^ (2 * (j : ℝ) / (2 : ℝ)) := by
    intro j hj0 hj2
    have hb := hgn T Lam hLam hLam_sup j hj0 hj2
    have hnorm : tensorL2Norm (I := I) g 0 4
        (iteratedCovGrad (I := I) g 0 2 2 T).toFun = R := by
      exact (SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g 0 2 2 T)).symm
    simpa [hnorm] using hb
  have hterm : ∀ n ∈ Finset.range 3,
      ∀ e ∈ Finset.Nat.antidiagonalTuple n 2,
        MeasureTheory.Integrable
            (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            2 * B ^ 14 * R ^ 2 := by
    intro n hn e he
    have hn2 : n ≤ 2 := by have := Finset.mem_range.mp hn; omega
    have hsum : ∑ m, e m = 2 := Finset.Nat.mem_antidiagonalTuple.mp he
    have hres := DifferentialGeometry.Integral.Connection.grid_prod_int_le
      (I := I) (M := M) g T hR 2 (by omega) hLam hLam_sup (le_refl R)
      hCgn hGNP n hn2 e hsum
    refine ⟨hres.1, hres.2.trans ?_⟩
    have hp : (max Lam (max Cgn 1)) ^ 14 ≤ B ^ 14 :=
      pow_le_pow_left₀ (by positivity) hmax_le 14
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by norm_num)) (sq_nonneg R)
  have hgrid_int : MeasureTheory.Integrable
      (h2JetGrid (I := I) (M := M) g T)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp [h2JetGrid]
    apply MeasureTheory.integrable_finset_sum
    intro n hn
    apply MeasureTheory.integrable_finset_sum
    intro e he
    exact (hterm n hn e he).1
  refine ⟨hgrid_int, ?_⟩
  rw [show (∫ x, h2JetGrid (I := I) (M := M) g T x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ n ∈ Finset.range 3, ∑ e ∈ Finset.Nat.antidiagonalTuple n 2,
        ∫ x, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) by
    dsimp [h2JetGrid]
    rw [MeasureTheory.integral_finset_sum _
      (fun n hn => MeasureTheory.integrable_finset_sum _
        (fun e he => (hterm n hn e he).1))]
    apply Finset.sum_congr rfl
    intro n hn
    exact MeasureTheory.integral_finset_sum _ (fun e he => (hterm n hn e he).1)]
  calc
    ∑ n ∈ Finset.range 3, ∑ e ∈ Finset.Nat.antidiagonalTuple n 2,
        ∫ x, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ n ∈ Finset.range 3, ∑ _e ∈ Finset.Nat.antidiagonalTuple n 2,
          2 * B ^ 14 * R ^ 2 := by
            apply Finset.sum_le_sum
            intro n hn
            apply Finset.sum_le_sum
            intro e he
            exact (hterm n hn e he).2
    _ = Q * (2 * B ^ 14 * R ^ 2) := by
          dsimp [Q]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Q * (2 * B ^ 14 * (Cjet * N) ^ 2) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hR_sq (mul_nonneg (by norm_num) (pow_nonneg hB _))) hQ
    _ = (Real.sqrt K * N) ^ 2 := by
          calc
            Q * (2 * B ^ 14 * (Cjet * N) ^ 2) = K * N ^ 2 := by
              dsimp [K]
              ring
            _ = (Real.sqrt K) ^ 2 * N ^ 2 := by rw [Real.sq_sqrt hK]
            _ = (Real.sqrt K * N) ^ 2 := by ring

set_option maxHeartbeats 1600000 in



theorem inv_coeff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) ^ 2) ∧
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 2 2 j
              (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨Cop, hCop, hop⟩ := hs2_op_bound (I := I) (M := M) hDim g₀
  obtain ⟨Cjet, hCjet, hjet⟩ := hs2_low2 (I := I) (M := M) g₀ 2
  obtain ⟨Cgrid, hCgrid, hgrid⟩ := h2_grid_two (I := I) (M := M) hDim g₀
  obtain ⟨Cgrad, hCgrad, hgrad⟩ :=
    riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le
      (I := I) (M := M) g₀
  obtain ⟨Cinv, hCinv, hinv⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le
      (I := I) (M := M) g₀ (show (1 / 2 : ℝ) < 1 by norm_num)
  let ρ : ℝ := min 1 (4 * Cop)⁻¹
  let vol : ℝ :=
    (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal
  let n : ℝ := Module.finrank ℝ E
  let Kpt : ℝ := (2 * n * Cop) ^ 2
  let K₀ : ℝ := Kpt * vol
  let K₁ : ℝ := Cgrad ^ 2 * Cjet ^ 2
  let K₂ : ℝ := Cinv 2 * Cgrid ^ 2
  let K : ℝ := Kpt + K₀ + K₁ + K₂
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by norm_num) (inv_pos.mpr (mul_pos (by norm_num) hCop))
  have hvol : 0 ≤ vol := by dsimp [vol]; exact ENNReal.toReal_nonneg
  have hn : 0 ≤ n := by dsimp [n]; exact Nat.cast_nonneg _
  have hKpt : 0 ≤ Kpt := by dsimp [Kpt]; positivity
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by
    dsimp [K₂]
    exact mul_nonneg (hCinv 2) (sq_nonneg Cgrid)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨ρ, Real.sqrt K, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T g₁ hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
  let δ : ℝ := Cop * N
  have hN : 0 ≤ N := norm_nonneg _
  have hNρ : N ≤ ρ := by simpa [N] using hT
  have hN1 : N ≤ 1 := hNρ.trans (by dsimp [ρ]; exact min_le_left _ _)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδfour : δ ≤ 1 / 4 := by
    calc
      δ = Cop * N := rfl
      _ ≤ Cop * ρ := mul_le_mul_of_nonneg_left hNρ (le_of_lt hCop)
      _ ≤ Cop * (4 * Cop)⁻¹ := by
        exact mul_le_mul_of_nonneg_left (by dsimp [ρ]; exact min_le_right _ _) (le_of_lt hCop)
      _ = 1 / 4 := by field_simp [ne_of_gt hCop]
  have hδhalf : δ < 1 / 2 := by linarith
  have hδone : δ < 1 := by linarith
  have hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ := by
    simpa [δ, N] using hop T
  have hratio : δ / (1 - δ) ≤ 2 * δ := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).2
    nlinarith [mul_nonneg hδ (show 0 ≤ 1 - 2 * δ by linarith)]
  have hratio_nn : 0 ≤ δ / (1 - δ) :=
    div_nonneg hδ (by linarith)
  have hinv₀_pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
        Kpt * N ^ 2 := by
    intro x
    have hb := riemannianFiberNormSq_gInvDiffSlotEndo_le
      (I := I) (M := M) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T) htie hδone hδ hbound x
    have hmul : n * (δ / (1 - δ)) ≤ 2 * n * Cop * N := by
      calc
        n * (δ / (1 - δ)) ≤ n * (2 * δ) :=
          mul_le_mul_of_nonneg_left hratio hn
        _ = 2 * n * Cop * N := by dsimp [δ]; ring
    calc
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)
          ≤ (n * (δ / (1 - δ))) ^ 2 := by simpa [n] using hb
      _ ≤ (2 * n * Cop * N) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hn hratio_nn) hmul 2
      _ = Kpt * N ^ 2 := by dsimp [Kpt]; ring
  have hinv₀ : ‖iteratedCovGrad (I := I) g₀ 2 2 0
        (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤ K₀ * N ^ 2 := by
    rw [iteratedCovGrad_zero]
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 2 2
      (gInvDiffSlotCoeff (I := I) g₀ g₁) (Kpt * N ^ 2) hinv₀_pt).trans ?_
    dsimp [K₀, vol]
    ring_nf
    exact le_rfl
  letI inst3 : Bundle.RiemannianBundle
      (fun x : M => TensorRSSpace 0 3 I x) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  have hgrad_pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((iteratedCovGrad (I := I) g₀ 2 2 1
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        Cgrad ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
    intro x
    have hb := hgrad g₁ T hδhalf hδ htie hbound x
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq
      (I := I) (M := M) g₀ 0 3 x
      (iteratedCovGrad (I := I) g₀ 0 2 1 T),
      Real.sq_sqrt (riemannianFiberNormSq_nonneg
        (I := I) (M := M) g₀ 0 3 x _)] at hb
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hb
  have hgrad_int : MeasureTheory.Integrable
      (fun x => Cgrad ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 3
      (iteratedCovGrad (I := I) g₀ 0 2 1 T)).const_mul (Cgrad ^ 2)
  have hgrad_sq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 2 3
    (iteratedCovGrad (I := I) g₀ 2 2 1
      (gInvDiffSlotCoeff (I := I) g₀ g₁)) _ hgrad_int hgrad_pt
  have hinv₁ : ‖iteratedCovGrad (I := I) g₀ 2 2 1
        (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤ K₁ * N ^ 2 := by
    refine hgrad_sq.trans ?_
    rw [MeasureTheory.integral_const_mul,
      ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g₀ 0 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 T),
      DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm]
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 1 T‖ ^ 2 ≤
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 :=
      Finset.single_le_sum (s := Finset.range 3)
        (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        (fun j _ => sq_nonneg _)
        (show 1 ∈ Finset.range 3 by norm_num)
    calc
      Cgrad ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 1 T‖ ^ 2
          ≤ Cgrad ^ 2 * (Cjet * N) ^ 2 :=
        mul_le_mul_of_nonneg_left (hsingle.trans (hjet T)) (sq_nonneg _)
      _ = K₁ * N ^ 2 := by dsimp [K₁]; ring
  have hgridT := hgrid T hN1
  have hinv₂_pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
          ((iteratedCovGrad (I := I) g₀ 2 2 2
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        Cinv 2 * h2JetGrid (I := I) (M := M) g₀ T x := by
    intro x
    simpa only [h2JetGrid] using
      hinv g₁ T htie (show δ ≤ (1 / 2 : ℝ) by linarith) hδ hbound 2 x
  have hinv₂ : ‖iteratedCovGrad (I := I) g₀ 2 2 2
        (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤ K₂ * N ^ 2 := by
    have hscaled : MeasureTheory.Integrable
        (fun x => Cinv 2 * h2JetGrid (I := I) (M := M) g₀ T x)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      hgridT.1.const_mul (Cinv 2)
    refine (normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 2 4
      (iteratedCovGrad (I := I) g₀ 2 2 2
        (gInvDiffSlotCoeff (I := I) g₀ g₁)) _ hscaled hinv₂_pt).trans ?_
    rw [MeasureTheory.integral_const_mul]
    calc
      Cinv 2 * (∫ x, h2JetGrid (I := I) (M := M) g₀ T x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
          ≤ Cinv 2 * (Cgrid * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hgridT.2 (hCinv 2)
      _ = K₂ * N ^ 2 := by dsimp [K₂]; ring
  have hsum : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j
        (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) ≤
        (K₀ + K₁ + K₂) * N ^ 2 := by
    let f : ℕ → ℝ := fun j => ‖iteratedCovGrad (I := I) g₀ 2 2 j
      (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
    change (∑ j ∈ Finset.range 3, f j) ≤ (K₀ + K₁ + K₂) * N ^ 2
    have hf₀ : f 0 ≤ K₀ * N ^ 2 := by simpa [f] using hinv₀
    have hf₁ : f 1 ≤ K₁ * N ^ 2 := by simpa [f] using hinv₁
    have hf₂ : f 2 ≤ K₂ * N ^ 2 := by simpa [f] using hinv₂
    calc
      ∑ j ∈ Finset.range 3, f j = f 0 + f 1 + f 2 := by
        norm_num [Finset.sum_range_succ]
      _ ≤ K₀ * N ^ 2 + K₁ * N ^ 2 + K₂ * N ^ 2 :=
        add_le_add (add_le_add hf₀ hf₁) hf₂
      _ = (K₀ + K₁ + K₂) * N ^ 2 := by ring
  have hpt_final : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
        (Real.sqrt K * N) ^ 2 := by
    intro x
    refine (hinv₀_pt x).trans ?_
    rw [mul_pow, Real.sq_sqrt hK]
    dsimp [K]
    nlinarith [mul_nonneg hKpt (sq_nonneg N),
      mul_nonneg hK₀ (sq_nonneg N), mul_nonneg hK₁ (sq_nonneg N),
      mul_nonneg hK₂ (sq_nonneg N)]
  refine ⟨by simpa [N] using hpt_final, ?_⟩
  refine hsum.trans ?_
  rw [mul_pow, Real.sq_sqrt hK]
  dsimp [K]
  nlinarith [mul_nonneg hKpt (sq_nonneg N),
    mul_nonneg hK₀ (sq_nonneg N), mul_nonneg hK₁ (sq_nonneg N),
    mul_nonneg hK₂ (sq_nonneg N)]




theorem principal_coeff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) ^ 2) ∧
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 4 2 j
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ := inv_coeff_h2 (I := I) (M := M) hDim g₀
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff
      (I := I) (M := M) g₀
  obtain ⟨Cl2, hCl2, hl2⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeff_jet_l2_sq
      (I := I) (M := M) g₀
  let S : ℝ := Cpt 0 + ∑ j ∈ Finset.range 3, Cl2 j
  let K : ℝ := S * Cinv ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (hCpt 0) (Finset.sum_nonneg (fun j _ => hCl2 j))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨ρ, Real.sqrt K, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T g₁ hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
  have hN : 0 ≤ N := norm_nonneg _
  obtain ⟨hinv_pt, hinv_l2⟩ := hinv T g₁ (by simpa [N] using hT) htie
  have hcoeff_pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
        Cpt 0 * (Cinv * N) ^ 2 := by
    intro x
    have hb := hpt g₁ 0 x
    simp only [Finset.sum_range_one, iteratedCovGrad_zero, Nat.zero_add] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hinv_pt x) (hCpt 0))
  have hcoeff_j : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 j
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        Cl2 j * (Cinv * N) ^ 2 := by
    intro j hj
    have hj3 : j + 1 ≤ 3 := by have := Finset.mem_range.mp hj; omega
    have hpartial : (∑ k ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 k
          (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) ≤
          ∑ k ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 2 2 k
              (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hj3) ?_
      intro k _ _
      exact sq_nonneg _
    exact (hl2 g₁ j).trans
      (mul_le_mul_of_nonneg_left (hpartial.trans hinv_l2) (hCl2 j))
  have hcoeff_sum : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 j
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
        (∑ j ∈ Finset.range 3, Cl2 j) * (Cinv * N) ^ 2 := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 j
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
          ≤ ∑ j ∈ Finset.range 3, Cl2 j * (Cinv * N) ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            exact hcoeff_j j hj
      _ = (∑ j ∈ Finset.range 3, Cl2 j) * (Cinv * N) ^ 2 := by
            rw [Finset.sum_mul]
  have htarget : (Real.sqrt K * N) ^ 2 = K * N ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
  have hCl2sum : 0 ≤ ∑ j ∈ Finset.range 3, Cl2 j :=
    Finset.sum_nonneg (fun j _ => hCl2 j)
  refine ⟨fun x => (hcoeff_pt x).trans ?_, hcoeff_sum.trans ?_⟩
  · rw [htarget]
    dsimp [K, S]
    nlinarith [mul_nonneg (hCpt 0) (mul_nonneg (sq_nonneg Cinv) (sq_nonneg N)),
      mul_nonneg hCl2sum
        (mul_nonneg (sq_nonneg Cinv) (sq_nonneg N))]
  · rw [htarget]
    dsimp [K, S]
    nlinarith [mul_nonneg (hCpt 0) (mul_nonneg (sq_nonneg Cinv) (sq_nonneg N)),
      mul_nonneg hCl2sum
        (mul_nonneg (sq_nonneg Cinv) (sq_nonneg N))]

private theorem convex_hs_le
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {s R : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hT : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R)
    (hT' : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R) :
    ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  rw [show convexPerturbation (I := I) g₀ T T' s =
      (1 - s) • T' + s • T from rfl,
    ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
  calc
    ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T' +
        s • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
        ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ +
          ‖s • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := norm_add_le _ _
    _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ +
          s * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
      add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
        (mul_le_mul_of_nonneg_left hT hs0)
    _ = R := by ring

set_option linter.unusedVariables false in



theorem principal_path_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {delta : ℝ} (hdelta_lt : delta < 1)
        (hdelta : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) delta)
        {delta' : ℝ} (hdelta'_lt : delta' < 1)
        (hdelta' : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') delta')
        {R : ℝ}, 0 ≤ R → R ≤ rho →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
                ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hdelta hdelta' s)).toSection x) ≤
              (C * R) ^ 2) ∧
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 4 2 j
                (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hdelta hdelta' s))‖ ^ 2) ≤
              (C * R) ^ 2 := by
  obtain ⟨rho, C, hrho, hC, hcoeff⟩ := principal_coeff_h2 (I := I) (M := M) hDim g₀
  refine ⟨rho, C, hrho, hC, ?_⟩
  intro T T' delta hdelta_lt hdelta delta' hdelta'_lt hdelta' R hR hRrho hT hT' s hs0 hs1
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  have hP : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) P‖ ≤ R := by
    simpa [P] using convex_hs_le (I := I) (M := M) g₀ T T' hs0 hs1 hT hT'
  have hs_mem : s ∈ realizedSmallSet (δ := delta) (δ' := delta') :=
    Icc_subset_realizedSmallSet hdelta_lt hdelta'_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hdelta hdelta' s).inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa [P] using realizedFam_inner_of_mem
      (I := I) g₀ T T' hdelta hdelta' hs_mem y v w
  obtain ⟨hpt, hjet⟩ := hcoeff P
    (realizedFam (I := I) g₀ T T' hdelta hdelta' s) (hP.trans hRrho) htie
  have hscale :
      (C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) P‖) ^ 2 ≤
        (C * R) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hP hC) 2
  exact ⟨fun x => (hpt x).trans hscale, hjet.trans hscale⟩



theorem principal_arm_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M)
        (U : SmoothCcTensor g₀ 0 2),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ U)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ := by
  obtain ⟨ρ, Ccoeff, hρ, hCcoeff, hcoeff⟩ :=
    principal_coeff_h2 (I := I) (M := M) hDim g₀
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h2_h3_h1 (I := I) (M := M) hDim g₀ 2 2
  refine ⟨ρ, Capp * Ccoeff, hρ, mul_nonneg hCapp hCcoeff, ?_⟩
  intro T g₁ U hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
  let A : ℝ := Ccoeff * N
  have hN : 0 ≤ N := norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg hCcoeff hN
  obtain ⟨hpt, hjet⟩ := hcoeff T g₁ (by simpa [N] using hT) htie
  have hbound := happ
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) U A
    hA (by simpa [A, N] using hpt) (by simpa [A, N] using hjet)
  simpa [deTurckPrincipalCometricArm, A, N, mul_assoc] using hbound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
