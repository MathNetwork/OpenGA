import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Tensor3rdCurvFiberNormBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def curvatureContraction
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun b : M => riemannSec (tensorCov (I := I) g 0 s) X Y
        (fun y : M => Z.toSection y) b
      contMDiff_toFun :=
        riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hX hY Z.toSection.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma curvatureContraction_toSection_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    (curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) X Y (fun y : M => Z.toSection y) x := rfl


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem curvatureContraction_toSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    (curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x =
      riemannOp (tensorCov (I := I) g 0 s) x (X x) (Y x) (Z.toSection x) := by
  rw [curvatureContraction_toSection_eq_riemannSec]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hX hY
    Z.toSection.contMDiff


omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_riemannOp_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ K_R : ℝ, 0 ≤ K_R ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (riemannOp (tensorCov (I := I) g 0 s) x (X x) (Y x) (Z.toSection x)) ≤ K_R := by
  obtain ⟨K_R, hK_nonneg, hK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor g 0 s
      (curvatureContraction (I := I) (M := M) g s Z hX hY)
  refine ⟨K_R, hK_nonneg, fun x => ?_⟩
  have hx := hK x
  rwa [curvatureContraction_toSection_apply (I := I) (M := M) g s Z hX hY x] at hx

def covGradCurvatureContraction
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    SmoothCcTensor g 0 (s + 1) :=
  covGrad g 0 s (curvatureContraction (I := I) (M := M) g s Z hX hY)


omit [NeZero (Module.finrank ℝ E)] in
lemma covGradCurvatureContraction_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (covGradCurvatureContraction (I := I) (M := M) g s Z hX hY).toSection =
      (covGrad g 0 s (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection := rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ KgradR : ℝ, 0 ≤ KgradR ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGradCurvatureContraction (I := I) (M := M) g s Z hX hY).toSection x) ≤ KgradR :=
  exists_bound_riemannianFiberNormSq_smoothCcTensor g 0 (s + 1)
    (covGradCurvatureContraction (I := I) (M := M) g s Z hX hY)

end Connection
end Integral
end DifferentialGeometry

end
