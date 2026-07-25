import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSCovariantDerivativeCongrLocally
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_toSection_apply_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y) :
    (covGrad (I := I) (M := M) g r s G₁).toSection x =
      (covGrad (I := I) (M := M) g r s G₂).toSection x := by
  rw [covGrad_toSection_apply, covGrad_toSection_apply]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) r s x) ?_
  exact tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g r s
    (σ := fun y : M => G₁.toSection y) (σ' := fun y : M => G₂.toSection y) (x := x)
    hagree
    (G₁.toSection.contMDiff.mdifferentiableAt (by simp))
    (G₂.toSection.contMDiff.mdifferentiableAt (by simp))

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_toSection_eventuallyEq_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y) :
    ∀ᶠ y in 𝓝 x,
      (covGrad (I := I) (M := M) g r s G₁).toSection y =
        (covGrad (I := I) (M := M) g r s G₂).toSection y := by
  filter_upwards [hagree.eventually_nhds] with y hy
  exact covGrad_toSection_apply_congr_of_eventuallyEq (I := I) g r s
    (G₁ := G₁) (G₂ := G₂) (x := y) hy

omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_toSection_apply_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y) :
    ∀ k : ℕ,
      (iteratedCovGrad g r s k G₁).toSection x =
        (iteratedCovGrad g r s k G₂).toSection x := by
  have hev : ∀ k : ℕ,
      ∀ᶠ y in 𝓝 x,
        (iteratedCovGrad g r s k G₁).toSection y =
          (iteratedCovGrad g r s k G₂).toSection y := by
    intro k
    induction k with
    | zero => simpa only [iteratedCovGrad_zero] using hagree
    | succ k ih =>
        simp only [iteratedCovGrad_succ]
        exact covGrad_toSection_eventuallyEq_of_eventuallyEq (I := I) g r (s + k)
          (G₁ := iteratedCovGrad g r s k G₁)
          (G₂ := iteratedCovGrad g r s k G₂) ih
  intro k
  exact (hev k).self_of_nhds

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_toSection_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y)
    (k : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + k) x
        ((iteratedCovGrad g r s k G₁).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + k) x
        ((iteratedCovGrad g r s k G₂).toSection x) :=
  congrArg (riemannianFiberNormSq (I := I) (M := M) g r (s + k) x)
    (iteratedCovGrad_toSection_apply_congr_of_eventuallyEq (I := I) g r s hagree k)

end RicciFlow
end PDE
end DifferentialGeometry

end
