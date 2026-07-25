import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField


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

noncomputable def unitGradAbstractRoughLap
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    Tensor0SSpace 3 I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

omit [NeZero (Module.finrank ℝ E)] in
lemma unitGradAbstractRoughLap_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    unitGradAbstractRoughLap (I := I) (M := M) g T₀ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
            (unitGradField (I := I) (M := M) g T₀) x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

theorem rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        rawTensorConnLap (I := I) g 0 3
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      unitGradAbstractRoughLap (I := I) (M := M) g T₀ x := by
  classical
  rw [rawTensorConnLap_covGrad_eq_frame_trace (I := I) (M := M) g T₀ x]
  rw [unitGradAbstractRoughLap_def]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          ∑ i : Fin (Module.finrank ℝ E),
            tensorSecondCovDeriv (I := I) g 0 3
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
          (unitZeroSec (I := I) (M := M) x) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            tensorSecondCovDeriv (I := I) g 0 3
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
            (unitZeroSec (I := I) (M := M) x) from by
        rw [ContinuousLinearMap.sum_apply]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  exact tensorSecondCovDeriv_covGrad_unit_eval (I := I) (M := M) g T₀ hB x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem abstract_succ_covDeriv_unfold_at
    (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SSpace 3 I y)
    {Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M W y)) x)
    (hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x)
    (hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          W x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => curriedSection I M W y (Y y)) x (Vfield x) -
        curriedSection I M W x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (F := Tensor0SModel 2 ℝ E)
    (V := fun z : M => Tensor0SSpace 2 I z)
    (cov_TM := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
    (τ := curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0S_curry (I := I) (M := M) 2 x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        W x (Vfield x)) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M)
        (F := Tensor0SModel 2 ℝ E)
        (V := fun z : M => Tensor0SSpace 2 I z)
        (cov_TM := LeviCivita (I := I) g)
        (cov_V := tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
        (τ := curriedSection I M W) x (Vfield x) := by
    rw [show
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          W x (Vfield x) =
        (Tensor0SNabla.tensor0SCovariantDerivative_succ I M (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))).toFun
          W x (Vfield x) from by
      rw [tensor0SCovariantDerivative_succ_eq]]
    rw [tensor0SCovariantDerivative_succ_apply]
    exact (tensor0S_curry (I := I) (M := M) 2 x).apply_symm_apply _
  rw [hsucc]
  exact hHom
end Connection
end Integral
end DifferentialGeometry

end
