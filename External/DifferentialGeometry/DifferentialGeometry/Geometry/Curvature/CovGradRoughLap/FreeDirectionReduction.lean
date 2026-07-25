import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.AbstractRoughLaplacianNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma covGrad_rawConnLap_unit_eval_curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth g 0 2 T₀) x w)
        (unitZeroSec (I := I) (M := M) x) := by
  have := curry_covGrad_unit_eval_general (I := I) (M := M) g 2
    (rawTensorConnLapSmooth g 0 2 T₀) x w
  exact this

omit [CompactSpace M] [I.Boundaryless] in
lemma rawConnLapSection_eq_frame_trace_secondCovDeriv_section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (rawTensorConnLapSmooth g 0 2 T₀).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 2
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => T₀.toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 2
    (fun y : M => T₀.toSection y) x

omit [CompactSpace M] [I.Boundaryless] in
lemma frame_trace_third_eq_swap_unit
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 2).toFun
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hT₀ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) b (T₀.toSection b)) :=
    T₀.toSection.contMDiff
  have hswap := frame_trace_thirdCovDeriv_swap (I := I) g 0 2
    (W := smoothExtensionTangent (I := I) x w) (T := fun y : M => T₀.toSection y) (x := x)
    hW hT₀
  have happ := congrArg
    (fun (φ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) =>
      φ (unitZeroSec (I := I) (M := M) x)) hswap
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply] using happ

lemma curry_unitGradAbstractRoughLap_along
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        (unitGradAbstractRoughLap (I := I) (M := M) g T₀ x)
        (smoothExtensionTangent (I := I) x w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        ( ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
              (fun z : M =>
                curriedSection I M
                  (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3
                    (LeviCivita (I := I) g)) (smoothOrthoFrame (I := I) g x i)
                    (unitGradField (I := I) (M := M) g T₀)) z
                  (smoothExtensionTangent (I := I) x w z)) x
              (smoothOrthoFrame (I := I) g x i x) -
            curriedSection I M
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3
                (LeviCivita (I := I) g)) (smoothOrthoFrame (I := I) g x i)
                (unitGradField (I := I) (M := M) g T₀)) x
              ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x w) x
                (smoothOrthoFrame (I := I) g x i x))) -
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z
                    (smoothExtensionTangent (I := I) x w z))
                  (unitZeroSec (I := I) (M := M) z)) x
              (smoothExtensionTangent (I := I) x
                ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
                  (smoothOrthoFrame (I := I) g x i x)) x) -
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
                ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x w) x
                  (smoothExtensionTangent (I := I) x
                    ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
                      (smoothOrthoFrame (I := I) g x i x)) x)))
              (unitZeroSec (I := I) (M := M) x))) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  rw [unitGradAbstractRoughLap_def]
  rw [show (tensor0S_curry (I := I) (M := M) 2 x
        (∑ i : Fin (Module.finrank ℝ E),
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
              (smoothOrthoFrame (I := I) g x i x) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (unitGradField (I := I) (M := M) g T₀) x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x))))) =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensor0S_curry (I := I) (M := M) 2 x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
              (smoothOrthoFrame (I := I) g x i x) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (unitGradField (I := I) (M := M) g T₀) x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x)))) from
      map_sum (tensor0S_curry (I := I) (M := M) 2 x) _ _]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothExtensionTangent (I := I) x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))) :=
    smoothExtensionTangent_contMDiff x _
  rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [curry_abstract_covDeriv_covApply_unitGrad_unfold (I := I) (M := M) g T₀ hB hB hW]
  have hCx : smoothExtensionTangent (I := I) x
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) x =
      (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x) :=
    smoothExtensionTangent_eq x _
  rw [show
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        (smoothExtensionTangent (I := I) x
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x)) x) from by rw [hCx]]
  rw [curry_abstract_covDeriv_unitGrad_unfold' (I := I) (M := M) g T₀ hC hW]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDeriv_unit_eval_eq_two
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v :=
  tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g 2 σ x v

end Connection
end Integral
end DifferentialGeometry

end
