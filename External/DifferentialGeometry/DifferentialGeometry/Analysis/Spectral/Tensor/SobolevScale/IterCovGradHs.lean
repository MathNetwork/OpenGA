import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def iterCovGradCcLin
    (g : SmoothRiemannianMetric I M) (s j : ℕ) :
    SmoothCcTensor g 0 s →ₗ[ℝ] SmoothCcTensor g 0 (s + j) where
  toFun := iteratedCovGrad (I := I) g 0 s j
  map_add' := iteratedCovGrad_add (I := I) (M := M) g 0 s j
  map_smul' := iteratedCovGrad_smul (I := I) (M := M) g 0 s j



noncomputable def iterCovGradHs
    (g : SmoothRiemannianMetric I M) (s j k : ℕ) :
    tensorHs (I := I) (M := M) g 0 s ((k : ℝ) + (j : ℝ)) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 (s + j) (k : ℝ) :=
  ((ccToHsLin (I := I) (M := M) g (s + j) (k : ℝ)).comp
      (iterCovGradCcLin (I := I) (M := M) g s j)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ)))



theorem iterCovGradHs_core
    (g : SmoothRiemannianMetric I M) (s j k : ℕ)
    (W : SmoothCcTensor g 0 s) :
    iterCovGradHs (I := I) (M := M) g s j k
        (ccTensorToHs (I := I) (M := M) g s ((k : ℝ) + (j : ℝ)) W) =
      ccTensorToHs (I := I) (M := M) g (s + j) (k : ℝ)
        (iteratedCovGrad (I := I) g 0 s j W) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ))) :=
    ccToHsLin_dense (I := I) (M := M) g s (by positivity)
  obtain ⟨C, _, hC⟩ := ccGrad_le (I := I) (M := M) g s j k
  change
    (((ccToHsLin (I := I) (M := M) g (s + j) (k : ℝ)).comp
        (iterCovGradCcLin (I := I) (M := M) g s j)).extendOfNorm
      (ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ))))
        ((ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ))) W) =
      ((ccToHsLin (I := I) (M := M) g (s + j) (k : ℝ)).comp
        (iterCovGradCcLin (I := I) (M := M) g s j)) W
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C, ?_⟩
  intro S
  change
    ‖ccTensorToHs (I := I) (M := M) g (s + j) (k : ℝ)
        (iteratedCovGrad (I := I) g 0 s j S)‖ ≤
      C * ‖ccTensorToHs (I := I) (M := M) g s ((k : ℝ) + (j : ℝ)) S‖
  have hkj : ((k + j : ℕ) : ℝ) = (k : ℝ) + (j : ℝ) := by norm_num
  rw [← hkj]
  exact hC S

end Connection
end Integral
end DifferentialGeometry

end
