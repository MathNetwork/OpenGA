import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricDoubleTraceFib_eq_sum_curry (g₀ : SmoothRiemannianMetric I M) (b : ℕ)
    (x : M) (D : Tensor0SSpace (b + 2) I x) :
    (show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace b I x from
        (cometricDoubleTraceField (I := I) g₀ b).toSection x) D =
      ∑ k : Fin (Module.finrank ℝ E),
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) b x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (b + 1) x D
            (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show (show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace b I x from
        (cometricDoubleTraceField (I := I) g₀ b).toSection x) D =
      cometricDoubleTraceFib (I := I) g₀ b x D from rfl]
  nth_rewrite 2 [← Tensor0SSpace.toModelL_apply (s := b) (x := x)]
  rw [map_sum (Tensor0SSpace.toModelL b x)]
  rw [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply (E := E) b (cometricLmodel (I := I) g₀ x)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  rw [tensor0S_curry_apply_eval (I := I) (M := M)
    (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (b + 1) x D
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))))
    (v0 := ((Module.finBasis ℝ E) k)) (vs := m)]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (T := D)
    (v0 := cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)))
    (vs := Fin.cons ((Module.finBasis ℝ E) k) m)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem toModel_slotExtend_two_apply (g₀ : SmoothRiemannianMetric I M) (b s : ℕ)
    (Φ : SmoothCcTensor g₀ b s) (x : M) (D : Tensor0SSpace (b + 2) I x) (a c : E)
    (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1)
            (slotExtend (I := I) (M := M) g₀ b s Φ)).toSection x) D)
        (Fin.cons a (Fin.cons c m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) b x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (b + 1) x D a) c)) m := by
  rw [show (show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1)
          (slotExtend (I := I) (M := M) g₀ b s Φ)).toSection x) D =
      slotExtendPointwise (I := I) (M := M) g₀ (b + 1) (s + 1) x
        (show Tensor0SSpace (b + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g₀ b s Φ).toSection x) D from rfl]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ (b + 1) (s + 1) x
    (show Tensor0SSpace (b + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g₀ b s Φ).toSection x) D a (Fin.cons c m)]
  rw [show (show Tensor0SSpace (b + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (slotExtend (I := I) (M := M) g₀ b s Φ).toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (b + 1) x D a) =
      slotExtendPointwise (I := I) (M := M) g₀ b s x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (b + 1) x D a) from rfl]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ b s x
    (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (b + 1) x D a) c m]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricDoubleTraceFib_comp_slotExtend_two_eq (g₀ : SmoothRiemannianMetric I M) (b s : ℕ)
    (Φ : SmoothCcTensor g₀ b s) (x : M) :
    (show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
          (cometricDoubleTraceField (I := I) g₀ s).toSection x).comp
        (show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1)
            (slotExtend (I := I) (M := M) g₀ b s Φ)).toSection x) =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace b I x from
          (cometricDoubleTraceField (I := I) g₀ b).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [cometricDoubleTraceFib_eq_sum_curry (I := I) g₀ b x D]
  rw [map_sum (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)]
  nth_rewrite 2 [← Tensor0SSpace.toModelL_apply (s := s) (x := x)]
  rw [map_sum (Tensor0SSpace.toModelL s x)]
  rw [show (show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (cometricDoubleTraceField (I := I) g₀ s).toSection x)
          ((show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1)
              (slotExtend (I := I) (M := M) g₀ b s Φ)).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ s x
        ((show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1)
            (slotExtend (I := I) (M := M) g₀ b s Φ)).toSection x) D) from rfl]
  rw [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
  simp only [ContinuousMultilinearMap.sum_apply, Tensor0SSpace.toModelL_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [toModel_slotExtend_two_apply (I := I) (M := M) g₀ b s Φ x D
    (cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)))
    ((Module.finBasis ℝ E) k) m]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricDoubleTrace_appCc_slotExtend_two_comm (g₀ : SmoothRiemannianMetric I M) (b s : ℕ)
    (Φ : SmoothCcTensor g₀ b s) (V : SmoothCcTensor g₀ 0 (b + 2)) :
    operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (operatorFieldApply (I := I) (M := M) g₀ (b + 2) (s + 2)
          (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1)
            (slotExtend (I := I) (M := M) g₀ b s Φ)) V) =
      operatorFieldApply (I := I) (M := M) g₀ b s Φ
        (operatorFieldApply (I := I) (M := M) g₀ (b + 2) b (cometricDoubleTraceField (I := I) g₀ b) V) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [appCc_toSection]
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
    cometricDoubleTraceFib_comp_slotExtend_two_eq (I := I) g₀ b s Φ x]

theorem rawTensorConnLap_appCc_comm_of_rank (g₀ : SmoothRiemannianMetric I M) (b s : ℕ)
    (Φ : SmoothCcTensor g₀ b s) (W : SmoothCcTensor g₀ 0 b) :
    rawTensorConnLapSmooth (I := I) g₀ 0 s (operatorFieldApply (I := I) (M := M) g₀ b s Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ b s Φ (rawTensorConnLapSmooth (I := I) g₀ 0 b W)
      + operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
          (operatorFieldApply (I := I) (M := M) g₀ b (s + 2)
            (covGrad (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ)) W)
      + operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
          (operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 2)
            (slotExtend (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ))
            (covGrad (I := I) (M := M) g₀ 0 b W))
      + operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
          (operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 2)
            (covGrad (I := I) (M := M) g₀ (b + 1) (s + 1)
              (slotExtend (I := I) (M := M) g₀ b s Φ))
            (covGrad (I := I) (M := M) g₀ 0 b W)) := by
  classical
  rw [rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace_of_rank (I := I) g₀ s
    (operatorFieldApply (I := I) (M := M) g₀ b s Φ W)]
  have h1 : covGrad (I := I) (M := M) g₀ 0 s (operatorFieldApply (I := I) (M := M) g₀ b s Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ) W +
        operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ)
          (covGrad (I := I) (M := M) g₀ 0 b W) :=
    covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ b s Φ W
  have hA : covGrad (I := I) (M := M) g₀ 0 (s + 1)
        (operatorFieldApply (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ) W) =
      operatorFieldApply (I := I) (M := M) g₀ b (s + 2)
          (covGrad (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ)) W +
        operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 2)
          (slotExtend (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ))
          (covGrad (I := I) (M := M) g₀ 0 b W) :=
    covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ) W
  have hB : covGrad (I := I) (M := M) g₀ 0 (s + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ)
          (covGrad (I := I) (M := M) g₀ 0 b W)) =
      operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 2)
          (covGrad (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ))
          (covGrad (I := I) (M := M) g₀ 0 b W) +
        operatorFieldApply (I := I) (M := M) g₀ (b + 2) (s + 2)
          (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ))
          (covGrad (I := I) (M := M) g₀ 0 (b + 1) (covGrad (I := I) (M := M) g₀ 0 b W)) :=
    covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ)
      (covGrad (I := I) (M := M) g₀ 0 b W)
  have hexp : iteratedCovGrad (I := I) g₀ 0 s 2 (operatorFieldApply (I := I) (M := M) g₀ b s Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ b (s + 2)
          (covGrad (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ)) W +
        operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 2)
          (slotExtend (I := I) (M := M) g₀ b (s + 1) (covGrad (I := I) (M := M) g₀ b s Φ))
          (covGrad (I := I) (M := M) g₀ 0 b W) +
        operatorFieldApply (I := I) (M := M) g₀ (b + 1) (s + 2)
          (covGrad (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ))
          (covGrad (I := I) (M := M) g₀ 0 b W) +
        operatorFieldApply (I := I) (M := M) g₀ (b + 2) (s + 2)
          (slotExtend (I := I) (M := M) g₀ (b + 1) (s + 1) (slotExtend (I := I) (M := M) g₀ b s Φ))
          (covGrad (I := I) (M := M) g₀ 0 (b + 1) (covGrad (I := I) (M := M) g₀ 0 b W)) := by
    have hxeq : iteratedCovGrad (I := I) g₀ 0 s 2 (operatorFieldApply (I := I) (M := M) g₀ b s Φ W) =
        covGrad (I := I) (M := M) g₀ 0 (s + 1)
          (covGrad (I := I) (M := M) g₀ 0 s (operatorFieldApply (I := I) (M := M) g₀ b s Φ W)) := rfl
    rw [hxeq, h1, covGrad_add, hA, hB]
    abel
  rw [hexp]
  simp only [appCc_add_right]
  rw [cometricDoubleTrace_appCc_slotExtend_two_comm (I := I) g₀ b s Φ
    (covGrad (I := I) (M := M) g₀ 0 (b + 1) (covGrad (I := I) (M := M) g₀ 0 b W))]
  rw [show operatorFieldApply (I := I) (M := M) g₀ (b + 2) b (cometricDoubleTraceField (I := I) g₀ b)
        (covGrad (I := I) (M := M) g₀ 0 (b + 1) (covGrad (I := I) (M := M) g₀ 0 b W)) =
      rawTensorConnLapSmooth (I := I) g₀ 0 b W from by
    rw [rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace_of_rank (I := I) g₀ b W]
    rfl]
  abel

theorem rawConnLap_iteratedCovGrad_two_comm (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 s) :
    rawTensorConnLapSmooth (I := I) g₀ 0 (s + 2) (iteratedCovGrad (I := I) g₀ 0 s 2 S) =
      iteratedCovGrad (I := I) g₀ 0 s 2 (rawTensorConnLapSmooth (I := I) g₀ 0 s S)
      + covGrad (I := I) (M := M) g₀ 0 (s + 1) (pointwiseTensorCurv (I := I) (M := M) g₀ s S)
      + pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) (covGrad (I := I) (M := M) g₀ 0 s S) := by
  have hxeq : iteratedCovGrad (I := I) g₀ 0 s 2 S =
      covGrad (I := I) (M := M) g₀ 0 (s + 1) (covGrad (I := I) (M := M) g₀ 0 s S) := rfl
  rw [hxeq]
  rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + 1)
    (covGrad (I := I) (M := M) g₀ 0 s S)]
  rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ s S]
  rw [covGrad_add]
  have hxeq2 : iteratedCovGrad (I := I) g₀ 0 s 2 (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
      covGrad (I := I) (M := M) g₀ 0 (s + 1)
        (covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := rfl
  rw [hxeq2]

theorem rawConnLap_appCc_iteratedCovGrad_two_comm (g₀ : SmoothRiemannianMetric I M) (s t : ℕ)
    (C : SmoothCcTensor g₀ (s + 2) t) (S : SmoothCcTensor g₀ 0 s) :
    rawTensorConnLapSmooth (I := I) g₀ 0 t
        (operatorFieldApply (I := I) (M := M) g₀ (s + 2) t C (iteratedCovGrad (I := I) g₀ 0 s 2 S)) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) t C
          (iteratedCovGrad (I := I) g₀ 0 s 2 (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      + operatorFieldApply (I := I) (M := M) g₀ (s + 2) t C
          (covGrad (I := I) (M := M) g₀ 0 (s + 1) (pointwiseTensorCurv (I := I) (M := M) g₀ s S))
      + operatorFieldApply (I := I) (M := M) g₀ (s + 2) t C
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) (covGrad (I := I) (M := M) g₀ 0 s S))
      + operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
          (operatorFieldApply (I := I) (M := M) g₀ (s + 2) (t + 2)
            (covGrad (I := I) (M := M) g₀ (s + 2) (t + 1)
              (covGrad (I := I) (M := M) g₀ (s + 2) t C))
            (iteratedCovGrad (I := I) g₀ 0 s 2 S))
      + operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
          (operatorFieldApply (I := I) (M := M) g₀ (s + 2 + 1) (t + 2)
            (slotExtend (I := I) (M := M) g₀ (s + 2) (t + 1)
              (covGrad (I := I) (M := M) g₀ (s + 2) t C))
            (covGrad (I := I) (M := M) g₀ 0 (s + 2) (iteratedCovGrad (I := I) g₀ 0 s 2 S)))
      + operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
          (operatorFieldApply (I := I) (M := M) g₀ (s + 2 + 1) (t + 2)
            (covGrad (I := I) (M := M) g₀ (s + 2 + 1) (t + 1)
              (slotExtend (I := I) (M := M) g₀ (s + 2) t C))
            (covGrad (I := I) (M := M) g₀ 0 (s + 2) (iteratedCovGrad (I := I) g₀ 0 s 2 S))) := by
  rw [rawTensorConnLap_appCc_comm_of_rank (I := I) g₀ (s + 2) t C (iteratedCovGrad (I := I) g₀ 0 s 2 S)]
  rw [rawConnLap_iteratedCovGrad_two_comm (I := I) g₀ s S]
  rw [appCc_add_right, appCc_add_right]

end Connection
end Integral
end DifferentialGeometry

end
