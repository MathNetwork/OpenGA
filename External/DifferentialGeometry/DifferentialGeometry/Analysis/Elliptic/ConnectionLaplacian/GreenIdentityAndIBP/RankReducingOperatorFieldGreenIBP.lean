import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS

noncomputable section

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_covGrad_appCcRS_eq_add (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (T : SmoothCcTensor g a (c + 1)) :
    tensorL2Inner (I := I) (M := M) g a (c + 1)
        (covGrad (I := I) (M := M) g a c
          (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W)).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1)
            (covGrad (I := I) (M := M) g b c Φ) W).toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
            (slotExtend (I := I) (M := M) g b c Φ)
            (covGrad (I := I) (M := M) g a b W)).toFun T.toFun := by
  classical
  set A1 : SmoothCcTensor g a (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W with hA1
  set A2 : SmoothCcTensor g a (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
      (covGrad (I := I) (M := M) g a b W) with hA2
  have hB : covGrad (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) = A1 + A2 :=
    covGrad_appCcRS_eq (I := I) (M := M) g a b c Φ W
  have hstep := congrArg
    (fun Z : SmoothCcTensor g a (c + 1) =>
      tensorL2Inner (I := I) (M := M) g a (c + 1) Z.toFun T.toFun) hB
  simp only at hstep
  rw [hstep, SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_left (I := I) (M := M) g a (c + 1)
    A1.toFun A2.toFun T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A1 T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A2 T)

theorem tensorL2Inner_appCcRS_covGrad_covGrad_eq_neg (g : SmoothRiemannianMetric I M)
    (a c : ℕ) (Φ : SmoothCcTensor g c c) (S : SmoothCcTensor g a c) :
    tensorL2Inner (I := I) (M := M) g a (c + 1)
        (ccOperatorFieldComp (I := I) (M := M) g a c (c + 1)
          (covGrad (I := I) (M := M) g c c Φ) S).toFun
        (covGrad (I := I) (M := M) g a c S).toFun =
      - tensorL2Inner (I := I) (M := M) g a c
          (rawTensorConnLapSmooth (I := I) g a c
            (ccOperatorFieldComp (I := I) (M := M) g a c c Φ S)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a (c + 1) (c + 1)
            (slotExtend (I := I) (M := M) g c c Φ)
            (covGrad (I := I) (M := M) g a c S)).toFun
          (covGrad (I := I) (M := M) g a c S).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_appCcRS_eq_add (I := I) (M := M) g a c c Φ S
    (covGrad (I := I) (M := M) g a c S)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a c c Φ S) S
  rw [hgreen] at hsplit
  linarith [hsplit]

theorem tensorL2Inner_appCcRS_slotExtend_input_covGrad_eq (g : SmoothRiemannianMetric I M)
    (a b c : ℕ) (Φ : SmoothCcTensor g b c) (X : SmoothCcTensor g a b)
    (V : SmoothCcTensor g a c) :
    tensorL2Inner (I := I) (M := M) g a (c + 1)
        (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
          (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b X)).toFun
        (covGrad (I := I) (M := M) g a c V).toFun =
      - tensorL2Inner (I := I) (M := M) g a c
          (rawTensorConnLapSmooth (I := I) g a c
            (ccOperatorFieldComp (I := I) (M := M) g a b c Φ X)).toFun V.toFun -
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1)
            (covGrad (I := I) (M := M) g b c Φ) X).toFun
          (covGrad (I := I) (M := M) g a c V).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_appCcRS_eq_add (I := I) (M := M) g a b c Φ X
    (covGrad (I := I) (M := M) g a c V)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ X) V
  rw [hgreen] at hsplit
  linarith [hsplit]

theorem tensorL2Inner_rawConnLap_appCcRS_eq_neg_covGrad_split (g : SmoothRiemannianMetric I M)
    (a b c : ℕ) (A : SmoothCcTensor g a c) (Φ : SmoothCcTensor g b c)
    (W : SmoothCcTensor g a b) :
    tensorL2Inner (I := I) (M := M) g a c
        (rawTensorConnLapSmooth (I := I) g a c A).toFun
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toFun =
      - tensorL2Inner (I := I) (M := M) g a (c + 1)
          (covGrad (I := I) (M := M) g a c A).toFun
          (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
            (slotExtend (I := I) (M := M) g b c Φ)
            (covGrad (I := I) (M := M) g a b W)).toFun -
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (covGrad (I := I) (M := M) g a c A).toFun
          (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1)
            (covGrad (I := I) (M := M) g b c Φ) W).toFun := by
  classical
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g a c A (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W)
  have hsplit := tensorL2Inner_covGrad_appCcRS_eq_add (I := I) (M := M) g a b c Φ W
    (covGrad (I := I) (M := M) g a c A)
  have hsymm0 := tensorL2Inner_symm (I := I) (M := M) g a (c + 1)
    (covGrad (I := I) (M := M) g a c A).toFun
    (covGrad (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W)).toFun
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g a (c + 1)
    (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W).toFun
    (covGrad (I := I) (M := M) g a c A).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g a (c + 1)
    (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
      (slotExtend (I := I) (M := M) g b c Φ)
      (covGrad (I := I) (M := M) g a b W)).toFun
    (covGrad (I := I) (M := M) g a c A).toFun
  linarith [hgreen, hsplit, hsymm0, hsymm1, hsymm2]

end Connection
end Integral
end DifferentialGeometry

end
