import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CurvatureDefect
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Tensor3rdCurvFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval


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

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

def slot0FrameTraceMatching
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) : Prop :=
  tensor0S_curry (I := I) (M := M) 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w =
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

lemma rawConnLap_covGrad_curry_eq_abstractRoughLap_curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      tensor0S_curry (I := I) (M := M) 2 x
        (unitGradAbstractRoughLap (I := I) (M := M) g T₀ x)
        (smoothExtensionTangent (I := I) x w x) := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  rw [rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap (I := I) (M := M) g T₀ x]
  rw [smoothExtensionTangent_eq]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covApply_unit_eval_eq_two
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        covApply (tensorCov (I := I) g 0 2) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq_two (I := I) (M := M) g σ y (X y)

noncomputable def covApplyT₀Section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covApply (tensorCov (I := I) g 0 2) X (fun z => T₀.toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 2 (T := fun y => T₀.toSection y)
      T₀.toSection.contMDiff hX)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covApplyT₀Section_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyT₀Section (I := I) (M := M) g T₀ hX y =
      covApply (tensorCov (I := I) g 0 2) X (fun z => T₀.toSection z) y := rfl

noncomputable def covApplyBcovApplyT₀Section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {W B : Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covApply (tensorCov (I := I) g 0 2) B
      (fun z => covApply (tensorCov (I := I) g 0 2) W (fun u => T₀.toSection u) z) y)
    (covApplyRS_contMDiff (I := I) g 0 2
      (T := fun y => covApply (tensorCov (I := I) g 0 2) W (fun u => T₀.toSection u) y)
      (covApplyRS_contMDiff (I := I) g 0 2 (T := fun u => T₀.toSection u)
        T₀.toSection.contMDiff hW) hB)

omit [CompactSpace M] [I.Boundaryless] in
lemma frameTraceSummand_unit_eq_abstract
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
        (fun y : M =>
          covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i)
            (fun z : M =>
              (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                covApply (tensorCov (I := I) g 0 2)
                  (smoothExtensionTangent (I := I) x w) (fun u => T₀.toSection u) z)
                (unitZeroSec (I := I) (M := M) z)) y)
        x (smoothOrthoFrame (I := I) g x i x) := by
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hStep1 := covDeriv_unit_eval_eq_two (I := I) (M := M) g
    (covApplyBcovApplyT₀Section (I := I) (M := M) g T₀ hW hB) x
    (smoothOrthoFrame (I := I) g x i x)
  have hInner := covApply_unit_eval_eq_two (I := I) (M := M) g
    (covApplyT₀Section (I := I) (M := M) g T₀ hW) (smoothOrthoFrame (I := I) g x i)
  calc (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x)
        (unitZeroSec (I := I) (M := M) x)
      = (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
            (fun y : M => covApplyBcovApplyT₀Section (I := I) (M := M) g T₀ hW hB y) x
            (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              covApplyBcovApplyT₀Section (I := I) (M := M) g T₀ hW hB y)
              (unitZeroSec (I := I) (M := M) y)) x
          (smoothOrthoFrame (I := I) g x i x) := hStep1
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => covApplyT₀Section (I := I) (M := M) g T₀ hW z) y)
              (unitZeroSec (I := I) (M := M) y)) x
          (smoothOrthoFrame (I := I) g x i x) := rfl
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  covApplyT₀Section (I := I) (M := M) g T₀ hW z)
                  (unitZeroSec (I := I) (M := M) z)) y) x
          (smoothOrthoFrame (I := I) g x i x) := by rw [hInner]
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  covApply (tensorCov (I := I) g 0 2)
                    (smoothExtensionTangent (I := I) x w) (fun u => T₀.toSection u) z)
                  (unitZeroSec (I := I) (M := M) z)) y) x
          (smoothOrthoFrame (I := I) g x i x) := rfl

theorem covGradRoughLapCurv_curry_eq_of_slot0Matching
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x)
    (hmatch : slot0FrameTraceMatching (I := I) (M := M) g T₀ x w) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
          (fun y : M => T₀.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  have hdef : (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
    rw [covGradRoughLapCurv, SmoothCcTensor.toSection_sub]; rfl
  rw [hdef]
  rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
  unfold slot0FrameTraceMatching at hmatch
  rw [hmatch]
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (I := I) (M := M) g T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w] at hswap
  rw [hswap]
  abel

end Connection
end Integral
end DifferentialGeometry

end
