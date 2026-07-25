import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PerturbedRiemannTensorJetBound

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_curvatureCoeff_riemannianFiberNormSq_le_of_perturbedMetric_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B)
    (coeff : SmoothRiemannianMetric I M → SmoothCcTensor g₀ 2 2)
    (hcoeff_curvature : coeff = (fun g₁ => ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) ∨
      coeff = (fun g₁ => ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((coeff g₁).toSection x) ≤ Λ := by
  classical
  rcases hcoeff_curvature with hcoeff | hcoeff
  · obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      exists_riemannBiContrFib_perturbed_rfns_le_of_jetEnvelope
        (I := I) (M := M) g₀ hδ₀ B hB
    refine ⟨Λ, hΛ_nn, ?_⟩
    intro g₁ P δ hδ_le hδ htie x henv
    have h := hΛ g₁ P hδ_le hδ htie x henv
    rw [hcoeff, ricciArmOrder0RiemannCoeff_toSection]
    exact h
  · obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      exists_ricciArmOrder0CurvCoeffFib_perturbed_rfns_le_of_jetEnvelope
        (I := I) (M := M) g₀ hδ₀ B hB
    refine ⟨Λ, hΛ_nn, ?_⟩
    intro g₁ P δ hδ_le hδ htie x henv
    have h := hΛ g₁ P hδ_le hδ htie x henv
    rw [hcoeff, ricciArmOrder0CurvCoeff_toSection]
    exact h

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_curvatureCoeff_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B)
    (coeff : SmoothRiemannianMetric I M → SmoothCcTensor g₀ 2 2)
    (hcoeff_curvature : coeff = (fun g₁ => ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) ∨
      coeff = (fun g₁ => ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((coeff (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_curvatureCoeff_riemannianFiberNormSq_le_of_perturbedMetric_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB coeff
      hcoeff_curvature
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w := by
    intro y v w
    rw [hg₁, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w]
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      (|1 - s| * δ' + |s| * δ) :=
    convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ δ₁ := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ :=
      mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ :=
      mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ δ₁ := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) δ₁ := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hsv : 0 ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
    have hsw : 0 ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg hsv hsw
    have hle' : |1 - s| * δ' + |s| * δ ≤ δ₁ := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  exact hΛ g₁ (convexPerturbation (I := I) g₀ T T' s) (le_of_eq hδ₁_def) hδs htie x henv

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (riemannBiContrFib (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x)) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_curvatureCoeff_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
      (fun g₁ => ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) (Or.inl rfl)
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  have h := hΛ T T' hδ_le hδ hδ'_le hδ' s hs x henv
  rwa [ricciArmOrder0RiemannCoeff_toSection] at h

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x)) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_curvatureCoeff_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
      (fun g₁ => ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) (Or.inr rfl)
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  have h := hΛ T T' hδ_le hδ hδ'_le hδ' s hs x henv
  rwa [ricciArmOrder0CurvCoeff_toSection] at h

end Curvature
end Geometry
end DifferentialGeometry

end
