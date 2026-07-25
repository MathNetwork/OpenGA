import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ j : ℕ, SmoothCcTensor g r s → SmoothCcTensor g r (s + j)
  | 0 => fun T => T
  | (j + 1) => fun T =>
      covGrad (I := I) (M := M) g r (s + j)
        (iteratedCovGrad g r s j T)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma iteratedCovGrad_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGrad g r s 0 T = T := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma iteratedCovGrad_succ
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGrad g r s (j + 1) T =
      covGrad (I := I) (M := M) g r (s + j)
        (iteratedCovGrad g r s j T) := rfl

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def iteratedCovGradSobolevNorm
    (g : SmoothRiemannianMetric I M) (r s k j : ℕ) (T : SmoothCcTensor g r s) : ℝ :=
  ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * (k - j))
    (iteratedCovGrad g r s j T)‖

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toSobolev_embedding_Cm
    (g : SmoothRiemannianMetric I M) (r s k m : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖)) ≤
          C * ∑ j ∈ Finset.range (m + 1),
            iteratedCovGradSobolevNorm g r s k j T := by
  classical
  have h_perdeg : ∀ j : ℕ,
      ∃ Cj : ℝ, 0 < Cj ∧ (j ≤ m → ∀ (T : SmoothCcTensor g r s) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
        ‖(iteratedCovGrad g r s j T).toSection x‖) ≤
          Cj * iteratedCovGradSobolevNorm g r s k j T) := by
    intro j
    by_cases hjm : j ≤ m
    · have h_super_j : 2 * (k - j) > Module.finrank ℝ E + 2 * 0 := by omega
      obtain ⟨Cj, hCj_pos, hCj⟩ :=
        tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M)
          g r (s + j) (k - j) 0 h_super_j
      exact ⟨Cj, hCj_pos,
        fun _ T x => hCj (iteratedCovGrad g r s j T) x⟩
    · exact ⟨1, one_pos, fun h => absurd h hjm⟩
  choose Cfun hCfun_pos hCfun using h_perdeg
  have hne : (Finset.range (m + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)
  set j₀ : ℕ := hne.choose with hj₀_def
  have hj₀ : j₀ ∈ Finset.range (m + 1) := hne.choose_spec
  refine ⟨(Finset.range (m + 1)).sup' hne Cfun + 1, ?_, ?_⟩
  · have hpos : 0 < Cfun j₀ := hCfun_pos j₀
    have hle : Cfun j₀ ≤ (Finset.range (m + 1)).sup' hne Cfun :=
      Finset.le_sup' Cfun hj₀
    linarith
  · intro T x
    set Cmax : ℝ := (Finset.range (m + 1)).sup' hne Cfun with hCmax_def
    have hCmax_nn : 0 ≤ Cmax :=
      le_trans (le_of_lt (hCfun_pos j₀)) (Finset.le_sup' Cfun hj₀)
    calc (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖))
        ≤ ∑ j ∈ Finset.range (m + 1),
            Cmax * iteratedCovGradSobolevNorm g r s k j T := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
          refine le_trans (hCfun j hjm T x) ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact Finset.le_sup' Cfun hj
      _ = Cmax * ∑ j ∈ Finset.range (m + 1),
            iteratedCovGradSobolevNorm g r s k j T := by
          rw [Finset.mul_sum]
      _ ≤ (Cmax + 1) * ∑ j ∈ Finset.range (m + 1),
            iteratedCovGradSobolevNorm g r s k j T := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          refine Finset.sum_nonneg (fun j _ => ?_)
          unfold iteratedCovGradSobolevNorm
          exact norm_nonneg _

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toSobolev_embedding_C2
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + j)
            ‖(iteratedCovGrad g 0 2 j T).toSection x‖)) ≤
          C * ∑ j ∈ Finset.range 3,
            iteratedCovGradSobolevNorm g 0 2 k j T := by
  have h_super' : 2 * k > Module.finrank ℝ E + 2 * 2 := by omega
  simpa using
    iteratedCovGrad_toSobolev_embedding_Cm (I := I) (M := M) g 0 2 k 2 h_super'

end InnerProductSpaceModel

end DifferentialGeometry.PDE.RicciFlow

end
