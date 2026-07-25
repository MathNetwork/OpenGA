import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffFibreExtraction
import DifferentialGeometry.Geometry.Metric.MetricBounds

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem exists_norm_covGrad_connDiffSection_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∀ j : ℕ, j ≤ 2 →
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖) ≤ B) →
          letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
          ‖((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x :
              Tensor0SBundle.TensorRSSpace 1 3 I x)‖ ≤ Cw := by
  classical
  letI instW : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
  obtain ⟨Ck0, hCk00, hKos0⟩ := riemannianFiberNormSq_raisedKoszul_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  obtain ⟨Ck1, hCk10, hKos1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_one_raisedKoszul_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  obtain ⟨Cs1, hCs10, hSharp1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_one_sharpFlatEndoCc_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  set b0 : ℝ := Ck0 ^ 2 * B ^ 2 with hb0_def
  set b1 : ℝ := Ck1 ^ 2 * (1 + B) ^ 2 * (B ^ 2 + B ^ 2) with hb1_def
  set s0 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2 with hs0_def
  set s1 : ℝ := Cs1 ^ 2 * B ^ 2 with hs1_def
  set Bf : ℕ → ℝ := fun i => if i = 0 then b0 else b1 with hBf_def
  set Sf : ℕ → ℝ := fun l => if l = 0 then s0 else s1 with hSf_def
  have hb0_nn : 0 ≤ b0 := by rw [hb0_def]; positivity
  have hb1_nn : 0 ≤ b1 := by rw [hb1_def]; positivity
  have hs0_nn : 0 ≤ s0 := by rw [hs0_def]; positivity
  have hs1_nn : 0 ≤ s1 := by rw [hs1_def]; positivity
  have hSf_nn : ∀ l : ℕ, 0 ≤ Sf l := by
    intro l
    simp only [hSf_def]
    by_cases hl : l = 0
    · rw [if_pos hl]; exact hs0_nn
    · rw [if_neg hl]; exact hs1_nn
  refine ⟨Real.sqrt (diagonalGridGrowthFactor (E := E) 1 *
      ∑ i ∈ Finset.range 2, Bf i * ∑ l ∈ Finset.range (2 - i), Sf l), Real.sqrt_nonneg _, ?_⟩
  intro g₁ P δ hδ_le hδ0 hδ htie x henv
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  set N1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hN1_def
  set N2 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)‖ with hN2_def
  have hN1_nn : 0 ≤ N1 := norm_nonneg _
  have hN2_nn : 0 ≤ N2 := norm_nonneg _
  have hN1_le : N1 ≤ B := by
    have := henv 1 (by norm_num)
    rw [← hN1_def] at this
    exact this
  have hN2_le : N2 ≤ B := by
    have := henv 2 (by norm_num)
    rw [← hN2_def] at this
    exact this
  have hKos : ∀ i ≤ 1,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤ Bf i := by
    intro i hi
    interval_cases i
    · have h := hKos0 g₁ P htie hδ_le hδ0 hδ x
      simp only [hBf_def, reduceIte]
      rw [hb0_def]
      have hiter0 : (iteratedCovGrad (I := I) g₀ 1 2 0 (raisedKoszul (I := I) g₀ g₁)) =
          raisedKoszul (I := I) g₀ g₁ := iteratedCovGrad_zero (I := I) g₀ 1 2 _
      rw [hiter0]
      refine le_trans h ?_
      rw [← hN1_def]
      have : N1 ^ 2 ≤ B ^ 2 := by
        apply pow_le_pow_left₀ hN1_nn hN1_le
      nlinarith [sq_nonneg Ck0, this, hN1_nn]
    · have h := hKos1 g₁ P htie hδ_le hδ0 hδ x (R := B) hB (by
        rw [← hN1_def]; exact hN1_le)
      simp only [hBf_def]
      rw [hb1_def]
      refine le_trans h ?_
      rw [← hN1_def, ← hN2_def]
      have hN1sq : N1 ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hN1_nn hN1_le 2
      have hN2sq : N2 ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hN2_nn hN2_le 2
      have h1B_nn : 0 ≤ (1 + B) ^ 2 := by positivity
      have hCk1_nn : 0 ≤ Ck1 ^ 2 := sq_nonneg _
      have hfac_nn : 0 ≤ Ck1 ^ 2 * (1 + B) ^ 2 := mul_nonneg hCk1_nn h1B_nn
      have hsum_le : N1 ^ 2 + N2 ^ 2 ≤ B ^ 2 + B ^ 2 := add_le_add hN1sq hN2sq
      exact mul_le_mul_of_nonneg_left hsum_le hfac_nn
  have hSharp : ∀ l ≤ 1,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤ Sf l := by
    intro l hl
    interval_cases l
    · have h := riemannianFiberNormSq_sharpFlatEndoCc_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
        g₁ P htie hδ_le hδ0 hδ x
      simp only [hSf_def, reduceIte]
      rw [hs0_def]
      have hiter0 : (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
          sharpFlatEndoCc (I := I) g₀ g₁ := iteratedCovGrad_zero (I := I) g₀ 1 1 _
      rw [hiter0]
      exact h
    · have h := hSharp1 g₁ P htie hδ_le hδ0 hδ x
      simp only [hSf_def]
      rw [hs1_def]
      refine le_trans h ?_
      rw [← hN1_def]
      have hN1sq : N1 ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hN1_nn hN1_le 2
      exact mul_le_mul_of_nonneg_left hN1sq (sq_nonneg Cs1)
  have hjet := riemannianFiberNormSq_iteratedCovGrad_connDiffSection_le (I := I) (M := M) g₀ g₁ 1 x Bf Sf
    hKos hSharp hSf_nn
  have hiter1 : (iteratedCovGrad (I := I) g₀ 1 2 1 (connDiffSection (I := I) g₁ g₀)) =
      covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter1] at hjet
  have hWsq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 3 x
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) 1 *
        ∑ i ∈ Finset.range 2, Bf i * ∑ l ∈ Finset.range (2 - i), Sf l :=
    hjet
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 3 x] at hWsq
  have hWnn : 0 ≤ ‖((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x :
      Tensor0SBundle.TensorRSSpace 1 3 I x)‖ := norm_nonneg _
  rw [← Real.sqrt_sq hWnn]
  exact Real.sqrt_le_sqrt hWsq

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_connDiffSection_flat_eval_eq_inner
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          (g0FlatCLM (I := I) g₀ x
            (covDerivConnDiff (I := I) g₀ g₁
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)))
        (Fin.cons v (Fin.cons u ![w])) =
      g₀.inner x
        (covDerivConnDiff (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x) := by
  classical
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  set Xsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXsec_def
  set Ysec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec_def
  set Zsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hZsec_def
  have hXx : Xsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hA_bridge : covDerivConnDiff (I := I) g₀ g₁ Xsec Zsec Ysec x = A := by
    rw [hA_def]; rfl
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₀ x A)
  have hbridge := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g₁ g₀ om Xsec Ysec Zsec x
  rw [hom, hXx, hYx, hZx, hA_bridge] at hbridge
  have hflatA : (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) = g₀.inner x A A := by
    rw [show (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x A) A from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x A A]
  rw [hflatA] at hbridge
  rw [hA_def]
  exact hbridge

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ (v w u : TangentSpace I x),
            Real.sqrt (g₀.inner x
                (covDerivConnDiff (I := I) g₀ g₁
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w)
                    (smoothExtensionTangent (I := I) x u) x)
                (covDerivConnDiff (I := I) g₀ g₁
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w)
                    (smoothExtensionTangent (I := I) x u) x)) ≤
              C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
                Real.sqrt (g₀.inner x u u) := by
  classical
  letI instW : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
  have hm0 : (0 : ℝ) ≤ max δ₀ 0 := le_max_right _ _
  have hm1 : max δ₀ 0 < 1 := max_lt hδ₀ (by norm_num)
  obtain ⟨Cw, hCw_nn, hCw⟩ :=
    exists_norm_covGrad_connDiffSection_le_of_jetEnvelope (I := I) (M := M) g₀ hm0 hm1 B hB
  refine ⟨Cw, hCw_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv v w u
  set δ' : ℝ := max δ 0 with hδ'_def
  have hδ'_nn : 0 ≤ δ' := le_max_right _ _
  have hδ'_le : δ' ≤ max δ₀ 0 := max_le hδ_le hm0
  have hδ'_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ' := by
    intro y a b
    refine le_trans (hδ y a b) ?_
    have hle : δ ≤ δ' := le_max_left _ _
    have hnn : 0 ≤ Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc δ * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)
        = δ * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) := by ring
      _ ≤ δ' * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) :=
          mul_le_mul_of_nonneg_right hle hnn
      _ = δ' * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by ring
  have henv' : ∀ j : ℕ, j ≤ 2 →
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖) ≤ B := by
    intro j hj
    have hterms : ∀ k ∈ Finset.range 3, (0 : ℝ) ≤
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    have hjmem : j ∈ Finset.range 3 := by
      rw [Finset.mem_range]; omega
    exact le_trans (Finset.single_le_sum hterms hjmem) henv
  have hWnorm := hCw g₁ P hδ'_le hδ'_nn hδ'_bound htie x henv'
  set W : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x with hW_def
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  have hAA_nn : 0 ≤ g₀.inner x A A := metric_inner_self_nonneg (I := I) (M := M) g₀ x A
  set NA : ℝ := Real.sqrt (g₀.inner x A A) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hbridge := covGrad_connDiffSection_flat_eval_eq_inner (I := I) (M := M) g₀ g₁ x v w u
  rw [← hA_def, ← hW_def] at hbridge
  have hprim := abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ x W A v u w
  rw [hbridge] at hprim
  rw [abs_of_nonneg hAA_nn] at hprim
  have hAA_sq : g₀.inner x A A = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hAA_nn]
  have hvv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hww_nn : 0 ≤ g₀.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₀.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Su * Sw := by
    have hp := hprim
    rw [hAA_sq] at hp
    rw [Real.sqrt_sq hNA_nn] at hp
    exact hp
  have hNA_le : NA ≤ NW * Sv * Sw * Su := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Su * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      have hcancel := le_of_mul_le_mul_left hkey hNApos
      calc NA ≤ NW * Sv * Su * Sw := hcancel
        _ = NW * Sv * Sw * Su := by ring
  calc NA ≤ NW * Sv * Sw * Su := hNA_le
    _ ≤ Cw * Sv * Sw * Su := by
        rw [hNW_def] at hWnorm
        have hprod_nn : 0 ≤ Sv * Sw * Su := by positivity
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hSu_nn, hNW_nn]

end Curvature
end Geometry
end DifferentialGeometry

end
