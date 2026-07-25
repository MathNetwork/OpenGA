import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegForcingH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm










noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]




theorem rem_h0_lip {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k₁ k₂ : ι,
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        ((deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
            deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) -
          rawTensorConnLapSmooth (I := I) gBase 0 2
            (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
              metricCcTensor (I := I) (M := M) gBase (gSeq k₂)))‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ)
          (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
            metricCcTensor (I := I) (M := M) gBase (gSeq k₂))‖ := by
  obtain ⟨Crhs, hCrhs, hrhs⟩ := rhs_h0_lip (I := I) (M := M) gBase gSeq D hD
  refine ⟨Crhs + 1, add_nonneg hCrhs zero_le_one, ?_⟩
  intro k₁ k₂
  let U : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
      metricCcTensor (I := I) (M := M) gBase (gSeq k₂)
  let S : SmoothCcTensor gBase 0 2 :=
    deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
      deTurckRHSSectionBg (I := I) gBase (gSeq k₂)
  have hrhs' : ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖ ≤
      Crhs * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by
    simpa only [S, U] using hrhs k₁ k₂
  have hlap := smoothCcToTensorHs_rawTensorConnLapSmooth_le
    (I := I) (M := M) gBase (0 : ℝ) U
  change ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
      (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ ≤
    ‖ccTensorToHs (I := I) (M := M) gBase 2 ((0 : ℝ) + 2) U‖ at hlap
  have hlap' : ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by
    have h02 : (0 : ℝ) + 2 = 2 := by norm_num
    rw [h02] at hlap
    exact hlap
  change ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
      (S - rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ ≤
    (Crhs + 1) * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖
  have hsub : ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        (S - rawTensorConnLapSmooth (I := I) gBase 0 2 U) =
      ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S -
        ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) gBase 0 2 U) := by
    have hneg : ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (-rawTensorConnLapSmooth (I := I) gBase 0 2 U) =
        -ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) gBase 0 2 U) := by
      rw [show -rawTensorConnLapSmooth (I := I) gBase 0 2 U =
          (-1 : ℝ) • rawTensorConnLapSmooth (I := I) gBase 0 2 U by simp,
        ccTensorToHs_smul]
      simp
    rw [sub_eq_add_neg, ccTensorToHs_add, hneg]
    rfl
  rw [hsub]
  calc
    ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S -
        ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖
        ≤ ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖ +
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
            (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ := norm_sub_le _ _
    _ ≤ Crhs * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ +
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ :=
      add_le_add hrhs' hlap'
    _ = (Crhs + 1) *
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by ring

end DifferentialGeometry.PDE.RicciFlow
