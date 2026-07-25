import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionTowerGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound)

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in

def gInvDiffSlotCoeff (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x)
      contMDiff_toFun := gInvDiffSlotEndo_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

def gInvDiffMetricArmCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => gInvDiffSlotCoeff (I := I) g₀ g₁
    | _ => 0

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in

omit [CompleteSpace E] in
theorem gInvDiffMetricArm_iteratedCovGrad_singleSum_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (gInvDiffMetricArmCoeffField (I := I) g₀ g₁)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (gInvDiffMetricArmCoeffField (I := I) g₀ g₁)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (gInvDiffMetricArmCoeffField (I := I) g₀ g₁) x₀ 2 W a


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_gInvDiffMetricArm_neumannFibreBound (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cnorm : ℝ, 0 ≤ Cnorm ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ → metricCauchySchwarzBound (I := I) g₀ h δ →
        ∀ (x : M) (v : TensorRSSpace 0 2 I x),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              (metricComparisonDiffFibreEndo (I := I) g₀ g₁ x v) ≤
            (Cnorm * δ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v :=
  exists_gInvDiffFibreEndo_neumannFibreBound (I := I) g₀

set_option backward.isDefEq.respectTransparency false in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_toSection_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x =
      covGradBundleEquiv (I := I) (M := M) 2 2 x
        (tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection y) x) :=
  covGrad_toSection_apply (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) x

set_option backward.isDefEq.respectTransparency false in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_leibniz
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (w : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, (fun x : M => Tensor0SSpace 2 I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 2 2
          (gInvDiffSlotCoeff (I := I) g₀ g₁) x v) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun y => metricComparisonDiffSlotEndo (I := I) g₀ g₁ y (w y)) x v -
      metricComparisonDiffSlotEndo (I := I) g₀ g₁ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀) w x v) := by
  rw [tensorCovDerivAt_def]
  exact tensorRSCovariantDerivative_apply I M 2 2 (LeviCivita (I := I) g₀)
    (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection w x v

set_option backward.isDefEq.respectTransparency false in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_leibniz_value
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) :
    ∃ w : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, (fun x : M => Tensor0SSpace 2 I x)⟯,
      w x = D ∧
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g₀ 2 2
            (gInvDiffSlotCoeff (I := I) g₀ g₁) x v) D =
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y => metricComparisonDiffSlotEndo (I := I) g₀ g₁ y (w y)) x v -
        metricComparisonDiffSlotEndo (I := I) g₀ g₁ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀) w x v) := by
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 2 ℝ E) (V := fun y : M => Tensor0SSpace 2 I y)
    (n := (⊤ : ℕ∞)) x D
  refine ⟨w, hw, ?_⟩
  rw [← hw, tensorCovDerivAt_def]
  exact tensorRSCovariantDerivative_apply I M 2 2 (LeviCivita (I := I) g₀)
    (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection w x v

end InnerProductSpaceModel

end Connection
end Integral
end DifferentialGeometry

end
