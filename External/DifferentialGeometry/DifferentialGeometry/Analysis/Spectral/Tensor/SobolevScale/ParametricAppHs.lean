import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricAppCcJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



theorem app_hs_unif
    (g : SmoothRiemannianMetric I M) (b c : ℕ) {α : Type*}
    (Φ : α → SmoothCcTensor g b c) (K : Set α) (B : ℕ → ℝ)
    (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ K → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i (Φ t)).toSection x) ≤ B i) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ∈ K → ∀ W : SmoothCcTensor g 0 b,
        ‖ccTensorToHs (I := I) (M := M) g c (n : ℝ)
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by
  classical
  obtain ⟨D, hD_nn, hD⟩ :=
    app_jet_of_bdd (I := I) (M := M) g b c Φ K B hB_nn hB
  intro n
  obtain ⟨Cout, hCout_nn, hCout⟩ := hs_le_jet (I := I) (M := M) g c n
  obtain ⟨Cin, hCin_nn, hCin⟩ := hsJet_le (I := I) (M := M) g b n
  let Dsum : ℝ := ∑ j ∈ Finset.range (n + 1), D j
  have hDsum_nn : 0 ≤ Dsum := by
    exact Finset.sum_nonneg fun j _ ↦ hD_nn j
  refine ⟨Cout * Dsum * Cin, by positivity, ?_⟩
  intro t ht W
  let Jin : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 b j W‖
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ‖iteratedCovGrad (I := I) g 0 c j
          (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ≤
        D j * Jin := by
    have hjn : j + 1 ≤ n + 1 :=
      Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hsmall :
        (∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖) ≤ Jin := by
      change
        (∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖) ≤
          ∑ l ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hjn) (fun l _ _ ↦ norm_nonneg _)
    exact (hD t ht W j).trans
      (mul_le_mul_of_nonneg_left hsmall (hD_nn j))
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖) ≤
        Dsum * Jin := by
    calc
      (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖) ≤
          ∑ j ∈ Finset.range (n + 1), D j * Jin := by
            exact Finset.sum_le_sum fun j hj ↦ hterm j hj
      _ = Dsum * Jin := by simp only [Dsum, Finset.sum_mul]
  have hJin : Jin ≤ Cin * ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by
    simpa only [Jin] using hCin W
  calc
    ‖ccTensorToHs (I := I) (M := M) g c (n : ℝ)
        (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ≤
        Cout * (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖) :=
      hCout _
    _ ≤ Cout * (Dsum * Jin) :=
      mul_le_mul_of_nonneg_left hsum hCout_nn
    _ ≤ Cout *
        (Dsum * (Cin * ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJin hDsum_nn) hCout_nn
    _ = (Cout * Dsum * Cin) *
        ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by ring




theorem app_hs_const
    (g : SmoothRiemannianMetric I M) (b c n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : SmoothCcTensor g b c) (B : ℕ → ℝ),
      (∀ i, i ≤ n → 0 ≤ B i) →
      (∀ i, i ≤ n → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i) →
      ∀ W : SmoothCcTensor g 0 b,
        ‖ccTensorToHs (I := I) (M := M) g c (n : ℝ)
            (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ≤
          C * Real.sqrt (∑ i ∈ Finset.range (n + 1), B i) *
            ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by
  classical
  obtain ⟨Cout, hCout_nn, hCout⟩ := hs_le_jet (I := I) (M := M) g c n
  obtain ⟨Cin, hCin_nn, hCin⟩ := hsJet_le (I := I) (M := M) g b n
  let Gsum : ℝ := ∑ j ∈ Finset.range (n + 1),
    Real.sqrt (diagonalGridGrowthFactor (E := E) j)
  have hGsum_nn : 0 ≤ Gsum := by
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  refine ⟨Cout * Gsum * Cin, by positivity, ?_⟩
  intro Φ B hB_nn hB W
  let Bsum : ℝ := ∑ i ∈ Finset.range (n + 1), B i
  have hBsum_nn : 0 ≤ Bsum := by
    exact Finset.sum_nonneg fun i hi =>
      hB_nn i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  let Jin : ℝ := ∑ l ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 b l W‖
  have hJin_nn : 0 ≤ Jin := by
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ‖iteratedCovGrad (I := I) g 0 c j
          (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ≤
        Real.sqrt (diagonalGridGrowthFactor (E := E) j) * Real.sqrt Bsum * Jin := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hsq := app_jet_sq_le (I := I) (M := M) g b c j Φ W B
      (fun i hi => hB_nn i (hi.trans hjn))
      (fun i hi x => hB i (hi.trans hjn) x)
    have hsmallB :
        (∑ i ∈ Finset.range (j + 1), B i) ≤ Bsum := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hjn))
        (fun i hi _ => hB_nn i
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    have hinner : ∀ i ∈ Finset.range (j + 1),
        (∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤ Jin ^ 2 := by
      intro i hi
      let Jsmall : ℝ := ∑ l ∈ Finset.range (j + 1 - i),
        ‖iteratedCovGrad (I := I) g 0 b l W‖
      have hJsmall_nn : 0 ≤ Jsmall := by
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hsubset : Finset.range (j + 1 - i) ⊆ Finset.range (n + 1) :=
        Finset.range_mono ((Nat.sub_le (j + 1) i).trans
          (Nat.succ_le_succ hjn))
      have hJsmall : Jsmall ≤ Jin := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun l _ _ => norm_nonneg _)
      have hsquares :
          (∑ l ∈ Finset.range (j + 1 - i),
              ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤ Jsmall ^ 2 := by
        exact Finset.sum_sq_le_sq_sum_of_nonneg
          (fun l _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 b l W))
      exact hsquares.trans (by nlinarith)
    have hgrid :
        (∑ i ∈ Finset.range (j + 1), B i *
          ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤
          Bsum * Jin ^ 2 := by
      calc
        _ ≤ ∑ i ∈ Finset.range (j + 1), B i * Jin ^ 2 := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hinner i hi) (hB_nn i
              ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hjn))
        _ = (∑ i ∈ Finset.range (j + 1), B i) * Jin ^ 2 := by
          rw [Finset.sum_mul]
        _ ≤ Bsum * Jin ^ 2 :=
          mul_le_mul_of_nonneg_right hsmallB (sq_nonneg Jin)
    have hsquare :
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
          (diagonalGridGrowthFactor (E := E) j * Bsum) * Jin ^ 2 := by
      refine hsq.trans ?_
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hgrid
          (appCcGdiag_nonneg (E := E) j))
    have htarget :
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
          (Real.sqrt (diagonalGridGrowthFactor (E := E) j * Bsum) * Jin) ^ 2 := by
      calc
        _ ≤ (diagonalGridGrowthFactor (E := E) j * Bsum) * Jin ^ 2 := hsquare
        _ = (Real.sqrt (diagonalGridGrowthFactor (E := E) j * Bsum) * Jin) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt]
          exact mul_nonneg (appCcGdiag_nonneg (E := E) j) hBsum_nn
    have hroot := le_of_sq_le_sq htarget
      (mul_nonneg (Real.sqrt_nonneg _) hJin_nn)
    rw [Real.sqrt_mul (appCcGdiag_nonneg (E := E) j)] at hroot
    exact hroot
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 c j
          (operatorFieldApply (I := I) (M := M) g b c Φ W)‖) ≤
        Gsum * (Real.sqrt Bsum * Jin) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          Real.sqrt (diagonalGridGrowthFactor (E := E) j) * Real.sqrt Bsum * Jin := by
        exact Finset.sum_le_sum fun j hj => hterm j hj
      _ = Gsum * (Real.sqrt Bsum * Jin) := by
        simp only [Gsum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
  have hJin : Jin ≤ Cin *
      ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by
    simpa only [Jin] using hCin W
  calc
    ‖ccTensorToHs (I := I) (M := M) g c (n : ℝ)
        (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ≤
        Cout * (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c Φ W)‖) := hCout _
    _ ≤ Cout * (Gsum * (Real.sqrt Bsum * Jin)) :=
      mul_le_mul_of_nonneg_left hsum hCout_nn
    _ ≤ Cout * (Gsum * (Real.sqrt Bsum *
        (Cin * ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hJin (Real.sqrt_nonneg Bsum)) hGsum_nn)
        hCout_nn
    _ = (Cout * Gsum * Cin) * Real.sqrt Bsum *
        ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by ring



theorem app_hs_small
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : SmoothCcTensor g b c) (B : ℕ → ℝ)
    (hB_nn : ∀ i, i ≤ n → 0 ≤ B i)
    (hB : ∀ i, i ≤ n → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : SmoothCcTensor g 0 b,
      ‖ccTensorToHs (I := I) (M := M) g c (n : ℝ)
          (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (n + 1), B i) *
          ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖ := by
  obtain ⟨C, hC, happ⟩ := app_hs_const (I := I) (M := M) g b c n
  exact ⟨C, hC, happ Φ B hB_nn hB⟩

private noncomputable def appCcLin
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    SmoothCcTensor g 0 b →ₗ[ℝ] SmoothCcTensor g 0 c where
  toFun := operatorFieldApply (I := I) (M := M) g b c Φ
  map_add' := appCc_add_right (I := I) (M := M) g b c Φ
  map_smul' := fun m W => by
    simpa only [RingHom.id_apply] using
      appCc_smul_right (I := I) (M := M) g b c m Φ W



noncomputable def appHs
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : SmoothCcTensor g b c) :
    tensorHs (I := I) (M := M) g 0 b (n : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 c (n : ℝ) :=
  ((ccToHsLin (I := I) (M := M) g c (n : ℝ)).comp
      (appCcLin g b c Φ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g b (n : ℝ))



theorem appHs_unif
    (g : SmoothRiemannianMetric I M) (b c n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : SmoothCcTensor g b c) (B : ℕ → ℝ),
      (∀ i, i ≤ n → 0 ≤ B i) →
      (∀ i, i ≤ n → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i) →
      ‖appHs g b c n Φ‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (n + 1), B i) := by
  obtain ⟨C, hC_nn, happ⟩ :=
    app_hs_const (I := I) (M := M) g b c n
  refine ⟨C, hC_nn, ?_⟩
  intro Φ B hB_nn hB
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g b (n : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g b (by positivity)
  unfold appHs
  apply LinearMap.opNorm_extendOfNorm_le hdense
    (mul_nonneg hC_nn (Real.sqrt_nonneg _))
  intro W
  change
    ‖ccTensorToHs (I := I) (M := M) g c (n : ℝ)
        (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ≤
      (C * Real.sqrt (∑ i ∈ Finset.range (n + 1), B i)) *
        ‖ccTensorToHs (I := I) (M := M) g b (n : ℝ) W‖
  exact happ Φ B hB_nn hB W



theorem appHs_norm
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : SmoothCcTensor g b c) (B : ℕ → ℝ)
    (hB_nn : ∀ i, i ≤ n → 0 ≤ B i)
    (hB : ∀ i, i ≤ n → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖appHs g b c n Φ‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (n + 1), B i) := by
  obtain ⟨C, hC_nn, hC⟩ := appHs_unif (I := I) (M := M) g b c n
  exact ⟨C, hC_nn, hC Φ B hB_nn hB⟩



theorem appHs_core
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b) :
    appHs g b c n Φ
        (ccTensorToHs (I := I) (M := M) g b (n : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g c (n : ℝ)
        (operatorFieldApply (I := I) (M := M) g b c Φ W) := by
  classical
  let B : ℕ → ℝ := fun i =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g b (c + i)
      (iteratedCovGrad (I := I) g b c i Φ)).choose
  have hB_nn (i : ℕ) : 0 ≤ B i :=
    (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g b (c + i)
      (iteratedCovGrad (I := I) g b c i Φ)).choose_spec.1
  have hB (i : ℕ) (x : M) :
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i :=
    (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g b (c + i)
      (iteratedCovGrad (I := I) g b c i Φ)).choose_spec.2 x
  obtain ⟨C, hC_nn, happ⟩ :=
    app_hs_small (I := I) (M := M) g b c n Φ B
      (fun i _ => hB_nn i) (fun i _ => hB i)
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g b (n : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g b (by positivity)
  change
    (((ccToHsLin (I := I) (M := M) g c (n : ℝ)).comp
        (appCcLin g b c Φ)).extendOfNorm
      (ccToHsLin (I := I) (M := M) g b (n : ℝ)))
        ((ccToHsLin (I := I) (M := M) g b (n : ℝ)) W) =
      ((ccToHsLin (I := I) (M := M) g c (n : ℝ)).comp
        (appCcLin g b c Φ)) W
  apply LinearMap.extendOfNorm_eq hdense
  exact ⟨C * Real.sqrt (∑ i ∈ Finset.range (n + 1), B i), happ⟩



theorem appHs_add
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c)
    (U : tensorHs (I := I) (M := M) g 0 b (n : ℝ)) :
    appHs g b c n (Φ₁ + Φ₂) U =
      appHs g b c n Φ₁ U + appHs g b c n Φ₂ U := by
  let ι := ccToHsLin (I := I) (M := M) g b (n : ℝ)
  let L := appHs g b c n (Φ₁ + Φ₂)
  let R := appHs g b c n Φ₁ + appHs g b c n Φ₂
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g b (by positivity)
  have hLR : (L : _ → _) = R := hdense.equalizer L.continuous R.continuous (by
    funext W
    simp only [Function.comp_apply, L, R, ι, ContinuousLinearMap.add_apply,
      ccToHsLin_apply]
    rw [appHs_core, appHs_core, appHs_core, appCc_add_left,
      ccTensorToHs_add])
  exact congrFun hLR U



theorem appHs_smul
    (g : SmoothRiemannianMetric I M) (b c n : ℕ) (a : ℝ)
    (Φ : SmoothCcTensor g b c)
    (U : tensorHs (I := I) (M := M) g 0 b (n : ℝ)) :
    appHs g b c n (a • Φ) U = a • appHs g b c n Φ U := by
  let ι := ccToHsLin (I := I) (M := M) g b (n : ℝ)
  let L := appHs g b c n (a • Φ)
  let R := a • appHs g b c n Φ
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g b (by positivity)
  have hLR : (L : _ → _) = R := hdense.equalizer L.continuous R.continuous (by
    funext W
    simp only [Function.comp_apply, L, R, ι, ContinuousLinearMap.smul_apply,
      ccToHsLin_apply]
    rw [appHs_core, appHs_core, appCc_smul_left, ccTensorToHs_smul])
  exact congrFun hLR U



theorem appHs_sub
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c)
    (U : tensorHs (I := I) (M := M) g 0 b (n : ℝ)) :
    appHs g b c n (Φ₁ - Φ₂) U =
      appHs g b c n Φ₁ U - appHs g b c n Φ₂ U := by
  rw [sub_eq_add_neg, appHs_add]
  calc
    appHs g b c n Φ₁ U + appHs g b c n (-Φ₂) U =
        appHs g b c n Φ₁ U +
          appHs g b c n ((-1 : ℝ) • Φ₂) U := by
      rw [neg_one_smul]
    _ = appHs g b c n Φ₁ U + (-1 : ℝ) • appHs g b c n Φ₂ U := by
      rw [appHs_smul]
    _ = appHs g b c n Φ₁ U - appHs g b c n Φ₂ U := by
      rw [neg_one_smul, sub_eq_add_neg]

end Connection
end Integral
end DifferentialGeometry

end
