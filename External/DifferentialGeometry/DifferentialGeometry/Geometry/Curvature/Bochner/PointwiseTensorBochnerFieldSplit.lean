import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.TraceDiscrepancyDecomposition

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

lemma pointwiseTensorCurv_eq_covGradRoughLapCurv_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    pointwiseTensorCurv (I := I) (M := M) g s S =
      covGradRoughLapCurv_gen (I := I) (M := M) g s S := rfl

lemma tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
        (covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s S x w +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x) -
          covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s S x w) := by
  rw [pointwiseTensorCurv_eq_covGradRoughLapCurv_gen (I := I) (M := M) g s S]
  rw [covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen
    (I := I) (M := M) g s S x w]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [Tensor3rdCurv_eq_genuine_add_bracket (I := I) g 0 s
      (smoothExtensionTangent (I := I) x w) (fun y : M => S.toSection y) x]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  abel

noncomputable def genuineThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

noncomputable def bracketThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      (covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s S x (e a) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s S x (e a)) m

theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hrecon⟩ :=
    tensor0S_eq_sum_slot0_uncurry (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
  rw [hrecon
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

end Connection
end Integral
end DifferentialGeometry
