import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Order2Equivalence
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def order2ConnLapIterateL2Sum (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) : ℝ :=
  ∑ j ∈ Finset.range (2 + 1),
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖

omit [CompactSpace M] [I.Boundaryless] in
theorem order2IterateNspec_nonneg (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    0 ≤ order2ConnLapIterateL2Sum (I := I) (M := M) g T :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem exists_order2IterateNspec_le_tensorPouSobolevHsNorm
    (g : SmoothRiemannianMetric I M) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      ∀ T : SmoothCcTensor g 0 2,
        order2ConnLapIterateL2Sum (I := I) (M := M) g T ≤
          C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
  classical

  obtain ⟨Cl2, hCl2_nn, hCl2⟩ :=
    exists_l2Norm_le_toHs_zero (I := I) (M := M) g

  set Cdrop : ℕ → ℝ := fun j =>
    (exists_rawConnLapIter_toHs_le_toHs (I := I) (M := M) g j 0).choose with hCdrop_def
  have hCdrop_nn : ∀ j : ℕ, 0 ≤ Cdrop j := fun j =>
    (exists_rawConnLapIter_toHs_le_toHs (I := I) (M := M) g j 0).choose_spec.1
  have hCdrop_spec : ∀ (j : ℕ) (T : SmoothCcTensor g 0 2),
      ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
          (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
        Cdrop j * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖ := fun j T =>
    (exists_rawConnLapIter_toHs_le_toHs (I := I) (M := M) g j 0).choose_spec.2 T

  set Cj : ℕ → ℝ := fun j => Cl2 * Cdrop j with hCj_def
  have hCj_nn : ∀ j : ℕ, 0 ≤ Cj j := fun j => mul_nonneg hCl2_nn (hCdrop_nn j)

  have hterm : ∀ (j : ℕ), j ≤ 2 → ∀ T : SmoothCcTensor g 0 2,
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
        Cj j * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
    intro j hj T
    set N2 : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal with hN2_def
    have hN2_nn : 0 ≤ N2 := ENNReal.toReal_nonneg

    have hstep2 :
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
          Cl2 * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
            (rawTensorConnLapIter (I := I) g 0 2 j T)‖ :=
      hCl2 (rawTensorConnLapIter (I := I) g 0 2 j T)

    have hstep3 :
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
            (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
          Cdrop j * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖ :=
      hCdrop_spec j T

    have hstep4 :
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖ ≤ N2 := by
      rw [hN2_def, ← tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g 2 T]
      have h0j : (0 + j) ≤ 2 := by omega
      exact toHs_norm_mono (I := I) (M := M) (g := g) (r := 0) (s := 2) h0j T
    calc ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖
        ≤ Cl2 * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
            (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := hstep2
      _ ≤ Cl2 * (Cdrop j * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖) :=
            mul_le_mul_of_nonneg_left hstep3 hCl2_nn
      _ ≤ Cl2 * (Cdrop j * N2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hstep4 (hCdrop_nn j)) hCl2_nn
      _ = (Cl2 * Cdrop j) * N2 := by ring
      _ = Cj j * N2 := by rw [hCj_def]

  refine ⟨∑ j ∈ Finset.range (2 + 1), Cj j,
    Finset.sum_nonneg (fun j _ => hCj_nn j), fun T => ?_⟩
  set N2 : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal with hN2_def
  have hN2_nn : 0 ≤ N2 := ENNReal.toReal_nonneg
  calc order2ConnLapIterateL2Sum (I := I) (M := M) g T
      = ∑ j ∈ Finset.range (2 + 1),
          ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := rfl
    _ ≤ ∑ j ∈ Finset.range (2 + 1), Cj j * N2 := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        exact hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) T
    _ = (∑ j ∈ Finset.range (2 + 1), Cj j) * N2 := by
        rw [Finset.sum_mul]

theorem exists_tensorPouSobolevHsNorm_le_order2IterateNspec
    (g : SmoothRiemannianMetric I M) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤
          C₂ * order2ConnLapIterateL2Sum (I := I) (M := M) g T := by
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    DifferentialGeometry.Integral.Connection.exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
      (I := I) (M := M) g 2 2
  exact ⟨C₂, hC₂_nn, fun T => hC₂ T⟩

theorem exists_Order2NormEquivOnSmooth (g : SmoothRiemannianMetric I M) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      Order2NormEquivOnSmooth (I := I) (M := M) g 0 2
        (order2ConnLapIterateL2Sum (I := I) (M := M) g) C₁ C₂ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    exists_order2IterateNspec_le_tensorPouSobolevHsNorm (I := I) (M := M) g
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    exists_tensorPouSobolevHsNorm_le_order2IterateNspec (I := I) (M := M) g
  exact ⟨C₁, C₂, hC₁_nn, hC₂_nn, hC₁, hC₂⟩

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
