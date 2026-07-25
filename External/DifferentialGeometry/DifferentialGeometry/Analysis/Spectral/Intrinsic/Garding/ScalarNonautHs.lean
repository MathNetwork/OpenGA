import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E




theorem lapDiff_hs_unif
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
            ‖ccTensorToHs (I := I) (M := M) (G.metric (T : ℝ)) 0 (m : ℝ)
                (scalarLapDiffCc (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)) U)‖ ≤
              C * ‖ccTensorToHs (I := I) (M := M) (G.metric (T : ℝ)) 0
                ((m + 2 : ℕ) : ℝ) U‖ := by
  classical
  obtain ⟨tau, htau, htau_one, B₂, B₁, hB₂_nn, hB₁_nn, hcoeff⟩ :=
    lapCoeff_slab (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let A : Set ℝ := Set.Icc (0 : ℝ) tau
  let gm : ℝ → SmoothRiemannianMetric I M := fun s => G.metric ((T : ℝ) - s)
  let Phi₂ : ℝ → SmoothCcTensor q 2 0 := fun s =>
    scalarTraceCoeff (I := I) q (gm s)
  let Phi₁ : ℝ → SmoothCcTensor q 1 0 := fun s =>
    connTraceCoeff (I := I) q (gm s)
  have hreg : ∀ s ∈ A, (T : ℝ) - s ∈ D.regular := by
    intro s hs
    exact (hcoeff s hs).1
  have hPhi₂ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
        ((iteratedCovGrad (I := I) q 2 0 i (Phi₂ s)).toSection x) ≤ B₂ i := by
    intro i s hs x
    simpa only [q, gm, Phi₂] using (hcoeff s hs).2.1 i x
  have hPhi₁ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i (Phi₁ s)).toSection x) ≤ B₁ i := by
    intro i s hs x
    simpa only [q, gm, Phi₁] using (hcoeff s hs).2.2 i x
  refine ⟨tau, htau, htau_one, ?_, fun m => ?_⟩
  · intro s hs
    exact hreg s hs
  · obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
      app_hs_unif (I := I) (M := M) q 2 0 Phi₂ A B₂ hB₂_nn hPhi₂ m
    obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
      app_hs_unif (I := I) (M := M) q 1 0 Phi₁ A B₁ hB₁_nn hPhi₁ m
    obtain ⟨G₂, hG₂_nn, hG₂⟩ := ccGrad_le (I := I) (M := M) q 0 2 m
    obtain ⟨G₁, hG₁_nn, hG₁⟩ := ccGrad_le (I := I) (M := M) q 0 1 m
    refine ⟨C₂ * G₂ + C₁ * G₁, by positivity, ?_⟩
    intro s hs U
    let X : SmoothCcTensor q 0 0 :=
      operatorFieldApply (I := I) (M := M) q 2 0 (Phi₂ s)
        (iteratedCovGrad (I := I) q 0 0 2 U)
    let Y : SmoothCcTensor q 0 0 :=
      operatorFieldApply (I := I) (M := M) q 1 0 (Phi₁ s)
        (iteratedCovGrad (I := I) q 0 0 1 U)
    let Hhi : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0
      ((m + 2 : ℕ) : ℝ) U‖
    have hmono :
        ‖ccTensorToHs (I := I) (M := M) q 0 ((m + 1 : ℕ) : ℝ) U‖ ≤
          Hhi := by
      have hm : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show m + 1 ≤ m + 2 by omega)
      simpa only [Hhi] using ccToHs_norm_mono (I := I) (M := M) q 0 hm U
    have hgrad₁ :
        ‖ccTensorToHs (I := I) (M := M) q 1 (m : ℝ)
            (iteratedCovGrad (I := I) q 0 0 1 U)‖ ≤ G₁ * Hhi := by
      exact (hG₁ U).trans (mul_le_mul_of_nonneg_left hmono hG₁_nn)
    have hX : ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X‖ ≤
        (C₂ * G₂) * Hhi := by
      calc
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X‖ ≤
            C₂ * ‖ccTensorToHs (I := I) (M := M) q 2 (m : ℝ)
              (iteratedCovGrad (I := I) q 0 0 2 U)‖ := by
                simpa only [X] using hC₂ s hs (iteratedCovGrad (I := I) q 0 0 2 U)
        _ ≤ C₂ * (G₂ * Hhi) :=
          mul_le_mul_of_nonneg_left (by simpa only [Hhi] using hG₂ U) hC₂_nn
        _ = (C₂ * G₂) * Hhi := by ring
    have hY : ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ ≤
        (C₁ * G₁) * Hhi := by
      calc
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ ≤
            C₁ * ‖ccTensorToHs (I := I) (M := M) q 1 (m : ℝ)
              (iteratedCovGrad (I := I) q 0 0 1 U)‖ := by
                simpa only [Y] using hC₁ s hs (iteratedCovGrad (I := I) q 0 0 1 U)
        _ ≤ C₁ * (G₁ * Hhi) := mul_le_mul_of_nonneg_left hgrad₁ hC₁_nn
        _ = (C₁ * G₁) * Hhi := by ring
    have hsub :
        ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) (X - Y) =
          ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X -
            ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y := by
      calc
        ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) (X - Y) =
            ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) (X + (-1 : ℝ) • Y) := by
              rw [neg_one_smul, sub_eq_add_neg]
        _ = ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X +
              ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) ((-1 : ℝ) • Y) := by
                rw [ccTensorToHs_add]
        _ = ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X +
              (-1 : ℝ) • ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y := by
                rw [ccTensorToHs_smul]
        _ = ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X -
              ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y := by
                rw [neg_one_smul, sub_eq_add_neg]
    have hsplit : scalarLapDiffCc (I := I) q (gm s) U = X - Y := by
      rfl
    rw [show scalarLapDiffCc (I := I) q (gm s) U = X - Y by exact hsplit, hsub]
    calc
      ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X -
          ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ ≤
          ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X‖ +
            ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ := norm_sub_le _ _
      _ ≤ (C₂ * G₂) * Hhi + (C₁ * G₁) * Hhi := add_le_add hX hY
      _ = (C₂ * G₂ + C₁ * G₁) * Hhi := by ring
      _ = (C₂ * G₂ + C₁ * G₁) *
          ‖ccTensorToHs (I := I) (M := M) q 0 ((m + 2 : ℕ) : ℝ) U‖ := by
            rfl

private noncomputable def lapDiffCcLin
    (q h : SmoothRiemannianMetric I M) :
    SmoothCcTensor q 0 0 →ₗ[ℝ] SmoothCcTensor q 0 0 where
  toFun := scalarLapDiffCc (I := I) q h
  map_add' := scalarLapDiff_add (I := I) (M := M) q h
  map_smul' := scalarLapDiff_smul (I := I) (M := M) q h



noncomputable def lapDiffHs
    (q h : SmoothRiemannianMetric I M) (m : ℕ) :
    tensorHs (I := I) (M := M) q 0 0 ((m : ℝ) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) q 0 0 (m : ℝ) :=
  ((ccToHsLin (I := I) (M := M) q 0 (m : ℝ)).comp
      (lapDiffCcLin (I := I) (M := M) q h)).extendOfNorm
    (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2))



theorem lapDiffHs_core
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ m s, s ∈ Set.Icc (0 : ℝ) tau →
        ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
          lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
              (G.metric ((T : ℝ) - s)) m
              (ccTensorToHs (I := I) (M := M) (G.metric (T : ℝ)) 0
                ((m : ℝ) + 2) U) =
            ccTensorToHs (I := I) (M := M) (G.metric (T : ℝ)) 0 (m : ℝ)
              (scalarLapDiffCc (I := I) (G.metric (T : ℝ))
                (G.metric ((T : ℝ) - s)) U) := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hbound⟩ :=
    lapDiff_hs_unif (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, ?_⟩
  intro m s hs U
  obtain ⟨C, hC_nn, hC⟩ := hbound m
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  change
    (((ccToHsLin (I := I) (M := M) q 0 (m : ℝ)).comp
        (lapDiffCcLin (I := I) (M := M) q h)).extendOfNorm
      (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)))
        ((ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)) U) =
      ((ccToHsLin (I := I) (M := M) q 0 (m : ℝ)).comp
        (lapDiffCcLin (I := I) (M := M) q h)) U
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C, ?_⟩
  intro W
  change
    ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
        (scalarLapDiffCc (I := I) q h W)‖ ≤
      C * ‖ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W‖
  rw [show ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) by norm_num]
  simpa only [q, h] using hC s hs W



theorem lapDiffHs_norm
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          ‖lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) m‖ ≤ C := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hbound⟩ :=
    lapDiff_hs_unif (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, fun m ↦ ?_⟩
  obtain ⟨C, hC_nn, hC⟩ := hbound m
  refine ⟨C, hC_nn, ?_⟩
  intro s hs
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  unfold lapDiffHs
  apply LinearMap.opNorm_extendOfNorm_le hdense hC_nn
  intro W
  change
    ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
        (scalarLapDiffCc (I := I) q h W)‖ ≤
      C * ‖ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W‖
  rw [show ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) by norm_num]
  simpa only [q, h] using hC s hs W



theorem lapDiffHs_small
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ),
      ‖lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
        (G.metric t) m‖ < ε := by
  classical
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  change ∀ᶠ t in 𝓝 (T : ℝ),
    ‖lapDiffHs (I := I) (M := M) q (G.metric t) m‖ < ε
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    app_hs_const (I := I) (M := M) q 2 0 m
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    app_hs_const (I := I) (M := M) q 1 0 m
  obtain ⟨G₂, hG₂_nn, hG₂⟩ := ccGrad_le (I := I) (M := M) q 0 2 m
  obtain ⟨G₁, hG₁_nn, hG₁⟩ := ccGrad_le (I := I) (M := M) q 0 1 m
  let K : ℝ := C₂ * G₂ + C₁ * G₁
  let R : ℝ := Real.sqrt (((m + 1 : ℕ) : ℝ))
  have hK_nn : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  obtain ⟨η, hη, hsmall⟩ := exists_pos_mul_lt hε (K * R)
  let δ : ℝ := η ^ 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have h₂ := scalarTrace_small (I := I) (M := M) G hG T m hδ
  have h₁ := connTrace_small (I := I) (M := M) G hG T m hδ
  filter_upwards [h₂, h₁] with t ht₂ ht₁
  let B : ℕ → ℝ := fun _ => δ
  have hB_nn : ∀ i, i ≤ m → 0 ≤ B i := by
    intro i hi
    simpa only [B] using hδ.le
  have hBsum :
      (∑ i ∈ Finset.range (m + 1), B i) =
        (((m + 1 : ℕ) : ℝ) * δ) := by
    simp only [B, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsqrt :
      Real.sqrt (∑ i ∈ Finset.range (m + 1), B i) = R * η := by
    have hm1_nn : 0 ≤ (((m + 1 : ℕ) : ℝ)) := by positivity
    rw [hBsum]
    dsimp only [δ]
    rw [Real.sqrt_mul hm1_nn, Real.sqrt_sq hη.le]
  have hcoef₂ : ∀ i, i ≤ m → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
        ((iteratedCovGrad (I := I) q 2 0 i
          (scalarTraceCoeff (I := I) q (G.metric t))).toSection x) ≤ B i := by
    intro i hi x
    simpa only [q, B, Nat.zero_add] using le_of_lt (ht₂ i hi x)
  have hcoef₁ : ∀ i, i ≤ m → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i
          (connTraceCoeff (I := I) q (G.metric t))).toSection x) ≤ B i := by
    intro i hi x
    simpa only [q, B, Nat.zero_add] using le_of_lt (ht₁ i hi x)
  have happ₂ := hC₂ (scalarTraceCoeff (I := I) q (G.metric t)) B hB_nn hcoef₂
  have happ₁ := hC₁ (connTraceCoeff (I := I) q (G.metric t)) B hB_nn hcoef₁
  have hcore : ∀ U : SmoothCcTensor q 0 0,
      ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
          (scalarLapDiffCc (I := I) q (G.metric t) U)‖ ≤
        ((K * R) * η) *
          ‖ccTensorToHs (I := I) (M := M) q 0
            ((m + 2 : ℕ) : ℝ) U‖ := by
    intro U
    let X : SmoothCcTensor q 0 0 :=
      operatorFieldApply (I := I) (M := M) q 2 0
        (scalarTraceCoeff (I := I) q (G.metric t))
        (iteratedCovGrad (I := I) q 0 0 2 U)
    let Y : SmoothCcTensor q 0 0 :=
      operatorFieldApply (I := I) (M := M) q 1 0
        (connTraceCoeff (I := I) q (G.metric t))
        (iteratedCovGrad (I := I) q 0 0 1 U)
    let Hhi : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0
      ((m + 2 : ℕ) : ℝ) U‖
    have hmono :
        ‖ccTensorToHs (I := I) (M := M) q 0
          ((m + 1 : ℕ) : ℝ) U‖ ≤ Hhi := by
      have hm : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show m + 1 ≤ m + 2 by omega)
      simpa only [Hhi] using ccToHs_norm_mono (I := I) (M := M) q 0 hm U
    have hgrad₁ :
        ‖ccTensorToHs (I := I) (M := M) q 1 (m : ℝ)
          (iteratedCovGrad (I := I) q 0 0 1 U)‖ ≤ G₁ * Hhi := by
      exact (hG₁ U).trans (mul_le_mul_of_nonneg_left hmono hG₁_nn)
    have hX :
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X‖ ≤
          (C₂ * G₂) * (R * η) * Hhi := by
      calc
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X‖ ≤
            C₂ * Real.sqrt (∑ i ∈ Finset.range (m + 1), B i) *
              ‖ccTensorToHs (I := I) (M := M) q 2 (m : ℝ)
                (iteratedCovGrad (I := I) q 0 0 2 U)‖ := by
                  simpa only [X] using
                    happ₂ (iteratedCovGrad (I := I) q 0 0 2 U)
        _ = C₂ * (R * η) *
              ‖ccTensorToHs (I := I) (M := M) q 2 (m : ℝ)
                (iteratedCovGrad (I := I) q 0 0 2 U)‖ := by rw [hsqrt]
        _ ≤ C₂ * (R * η) * (G₂ * Hhi) :=
          mul_le_mul_of_nonneg_left (by simpa only [Hhi] using hG₂ U)
            (mul_nonneg hC₂_nn (mul_nonneg hR_nn (le_of_lt hη)))
        _ = (C₂ * G₂) * (R * η) * Hhi := by ring
    have hY :
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ ≤
          (C₁ * G₁) * (R * η) * Hhi := by
      calc
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ ≤
            C₁ * Real.sqrt (∑ i ∈ Finset.range (m + 1), B i) *
              ‖ccTensorToHs (I := I) (M := M) q 1 (m : ℝ)
                (iteratedCovGrad (I := I) q 0 0 1 U)‖ := by
                  simpa only [Y] using
                    happ₁ (iteratedCovGrad (I := I) q 0 0 1 U)
        _ = C₁ * (R * η) *
              ‖ccTensorToHs (I := I) (M := M) q 1 (m : ℝ)
                (iteratedCovGrad (I := I) q 0 0 1 U)‖ := by rw [hsqrt]
        _ ≤ C₁ * (R * η) * (G₁ * Hhi) :=
          mul_le_mul_of_nonneg_left hgrad₁
            (mul_nonneg hC₁_nn (mul_nonneg hR_nn (le_of_lt hη)))
        _ = (C₁ * G₁) * (R * η) * Hhi := by ring
    have hsub :
        ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) (X - Y) =
          ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X -
            ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y := by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) q 0 (m : ℝ)) X Y
    rw [show scalarLapDiffCc (I := I) q (G.metric t) U = X - Y by rfl,
      hsub]
    calc
      ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X -
          ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ ≤
          ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X‖ +
            ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y‖ :=
        norm_sub_le _ _
      _ ≤ (C₂ * G₂) * (R * η) * Hhi +
          (C₁ * G₁) * (R * η) * Hhi := add_le_add hX hY
      _ = ((K * R) * η) * Hhi := by
        dsimp only [K]
        ring
      _ = ((K * R) * η) *
          ‖ccTensorToHs (I := I) (M := M) q 0
            ((m + 2 : ℕ) : ℝ) U‖ := by rfl
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  have hop : ‖lapDiffHs (I := I) (M := M) q (G.metric t) m‖ ≤
      (K * R) * η := by
    unfold lapDiffHs
    apply LinearMap.opNorm_extendOfNorm_le hdense
      (mul_nonneg (mul_nonneg hK_nn hR_nn) (le_of_lt hη))
    intro U
    change
      ‖ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
          (scalarLapDiffCc (I := I) q (G.metric t) U)‖ ≤
        (K * R) * η *
          ‖ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) U‖
    rw [show ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) by norm_num]
    exact hcore U
  exact lt_of_le_of_lt hop hsmall



theorem lapDiffHs_tendsto
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (m : ℕ) :
    Tendsto
      (fun t : ℝ => lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
        (G.metric t) m)
      (𝓝 (T : ℝ)) (𝓝 0) := by
  refine (NormedAddGroup.tendsto_nhds_zero
    (f := fun t : ℝ => lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
      (G.metric t) m) (l := 𝓝 (T : ℝ))).mpr ?_
  intro ε hε
  exact lapDiffHs_small (I := I) (M := M) G hG T m hε




theorem lapDiffHs_inc
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ {n m : ℕ} (hnm : n ≤ m) s, s ∈ Set.Icc (0 : ℝ) tau →
        (tensorHsInclusion (I := I) (M := M)
            (g := G.metric (T : ℝ)) (r := 0) (s := 0)
            (by exact_mod_cast hnm : (n : ℝ) ≤ (m : ℝ))).comp
          (lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) m) =
        (lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) n).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := G.metric (T : ℝ)) (r := 0) (s := 0)
            (by exact_mod_cast Nat.add_le_add_right hnm 2 :
              (n : ℝ) + 2 ≤ (m : ℝ) + 2)) := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hcore⟩ :=
    lapDiffHs_core (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, ?_⟩
  intro n m hnm s hs
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hnmR2 : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
    exact_mod_cast Nat.add_le_add_right hnm 2
  let L :=
    (tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) hnmR).comp
      (lapDiffHs (I := I) (M := M) q h m)
  let R :=
    (lapDiffHs (I := I) (M := M) q h n).comp
      (tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) hnmR2)
  change L = R
  apply ContinuousLinearMap.ext
  intro v
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  have heq :
      L ∘ ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2) =
        R ∘ ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2) := by
    funext U
    change
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0) hnmR
          (lapDiffHs (I := I) (M := M) q h m
            (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) U)) =
        lapDiffHs (I := I) (M := M) q h n
          (tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hnmR2
            (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) U))
    rw [show lapDiffHs (I := I) (M := M) q h m
          (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) U) =
        ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
          (scalarLapDiffCc (I := I) q h U) by
      simpa only [q, h] using hcore m s hs U]
    have hin :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hnmR2
            (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) U) =
          ccTensorToHs (I := I) (M := M) q 0 ((n : ℝ) + 2) U := by
      apply tensorHs.ext
      funext i
      simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    rw [hin]
    rw [show lapDiffHs (I := I) (M := M) q h n
          (ccTensorToHs (I := I) (M := M) q 0 ((n : ℝ) + 2) U) =
        ccTensorToHs (I := I) (M := M) q 0 (n : ℝ)
          (scalarLapDiffCc (I := I) q h U) by
      simpa only [q, h] using hcore n s hs U]
    apply tensorHs.ext
    funext i
    simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
  have hfun := hdense.equalizer L.continuous R.continuous heq
  exact congr_fun hfun v

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
