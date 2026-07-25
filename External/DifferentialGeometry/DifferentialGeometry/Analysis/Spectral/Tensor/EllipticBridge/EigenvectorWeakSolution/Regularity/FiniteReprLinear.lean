import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion








noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



private noncomputable def finiteCoeffLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    tensorHs.finiteSupportSubmodule
        (I := I) (M := M) (g := g) (r := r) (s := s) σ →ₗ[ℝ]
      (TensorEigenIdx (I := I) (M := M) g r s →₀ ℝ) where
  toFun v := Finsupp.ofSupportFinite v.1.coeff v.2
  map_add' v w := by
    ext i
    rfl
  map_smul' c v := by
    ext i
    rfl



noncomputable def finiteReprLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    tensorHs.finiteSupportSubmodule
        (I := I) (M := M) (g := g) (r := r) (s := s) σ →ₗ[ℝ]
      SmoothCcTensor g r s :=
  (Finsupp.linearCombination ℝ
      (eigenvectorSmooth (I := I) (M := M) g r s)).comp
    (finiteCoeffLin (I := I) (M := M) g r s σ)


omit [CompleteSpace E] in
@[simp] theorem finiteReprLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (v : tensorHs.finiteSupportSubmodule
      (I := I) (M := M) (g := g) (r := r) (s := s) σ) :
    finiteReprLin (I := I) (M := M) g r s σ v =
      tensorHsSmoothRepr (I := I) (M := M) v.1 v.2 := by
  classical
  change
    Finsupp.linearCombination ℝ
        (eigenvectorSmooth (I := I) (M := M) g r s)
        (Finsupp.ofSupportFinite v.1.coeff v.2) =
      tensorHsSmoothRepr (I := I) (M := M) v.1 v.2
  rw [Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.ofSupportFinite_support,
    tensorHsSmoothRepr_eq]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
