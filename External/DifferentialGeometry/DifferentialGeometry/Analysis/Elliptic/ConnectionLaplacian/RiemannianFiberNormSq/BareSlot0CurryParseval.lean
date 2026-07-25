import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.SlotSplitParsevalBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality


noncomputable section

set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def tensor0SToTensorRS {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight C


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensor0SAsRS_apply {s : ℕ} (x : M) (C : Tensor0SSpace s I x)
    (τ : Tensor0SSpace 0 I x) :
    (tensor0SToTensorRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • C := by
  change ((tensor00Scalar (I := I) (M := M) x).smulRight C) τ = _
  rw [ContinuousLinearMap.smulRight_apply]


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma coframeS_zero_eq_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) :
    coframeS (I := I) (M := M) g x 0 e K₀ = unitZeroSec (I := I) (M := M) x := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
  intro u
  rw [coframeS_apply (I := I) (M := M) g x 0 e K₀ u]
  rw [Fin.prod_univ_zero]
  rw [show ((unitZeroSec (I := I) (M := M) x) u : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) u from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    slot0Curry (I := I) (M := M) g x s e K₀ T a =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x)) (e a)) := by
  unfold slot0Curry tensor0SToTensorRS
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) s x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) := by
  classical
  obtain ⟨n, e, K₀, hn, hsplit⟩ :=
    riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g s x T
  refine ⟨n, e, hn, ?_⟩
  rw [hsplit]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ T a]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem riemannianFiberNormSq_three_eq_sum_bareSlot0Curry
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TensorRSSpace 0 3 I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) 2 x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) :=
  riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry (I := I) (M := M) g 2 x T

end Connection
end Integral
end DifferentialGeometry

end
