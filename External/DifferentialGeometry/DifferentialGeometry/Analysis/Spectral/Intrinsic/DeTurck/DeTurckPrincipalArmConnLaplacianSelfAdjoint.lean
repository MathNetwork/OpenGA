import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ConnLapPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.EndoCovariantDerivativeSelfAdjoint
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotSwapPairingCalculus
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem rawConnLap_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
  have hTv := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s T v
  have hvT := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s v T
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T).toFun (covGrad (I := I) (M := M) g r s v).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s v).toFun T.toFun
  rw [hsymm1, hvT] at hTv; rw [← hsymm2]; linarith [hTv]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorL2Inner_sub_left_smoothCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  have hsub : (S₁.toFun - S₂.toFun) = S₁.toFun + (-1 : ℝ) • S₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S₂ T
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S₂.toFun x) (T.toFun x)) := by
      funext x
      change tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • S₂.toFun x) (T.toFun x) = _
      rw [tensorInnerPointwise_smul_left]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun ((-1 : ℝ) • S₂.toFun) T.toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S₁ T) hint2,
    tensorL2Inner_smul_left]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorL2Inner_sub_right_smoothCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  have hsub : (T₁.toFun - T₂.toFun) = T₁.toFun + (-1 : ℝ) • T₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S T₂
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (T₂.toFun x)) := by
      funext x
      change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) ((-1 : ℝ) • T₂.toFun x) = _
      rw [tensorInnerPointwise_smul_right]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_right (I := I) (M := M) g r s S.toFun T₁.toFun ((-1 : ℝ) • T₂.toFun)
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S T₁) hint2,
    tensorL2Inner_smul_right]
  ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
