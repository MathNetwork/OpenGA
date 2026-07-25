import DifferentialGeometry.Analysis.Integration.L2.Pairing.MovingFrameBracketDivergence
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hdiv : (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun x)
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => divergence_g (I := I) g X x)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 :=
  tensorL2Inner_eq_zero_of_pointwise_inner_eq_divergence (I := I) (M := M) g s
    (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv)
    (covGrad (I := I) (M := M) g 0 s S) X hdiv

theorem tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_pointwise_divergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hdiv : (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun x)
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => divergence_g (I := I) g X x)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hnull :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun = 0 :=
    tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence
      (I := I) (M := M) g s S Gcurv GcurvDeriv X hdiv
  have hCurv_eq : Curv = (Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv) := by abel
  have hfun : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toFun =
      (Gcurv + GcurvDeriv).toFun + (Curv - Gcurv - GcurvDeriv).toFun :=
    SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gcurv + GcurvDeriv) gradS
  have hint₂ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - GcurvDeriv) gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (Gcurv + GcurvDeriv).toFun (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun hint₁ hint₂
  rw [hnull] at hsplit
  linarith [hsplit]

theorem tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (hnull : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hCurv_eq : Curv = (Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv) := by abel
  have hfun : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toFun =
      (Gcurv + GcurvDeriv).toFun + (Curv - Gcurv - GcurvDeriv).toFun :=
    SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gcurv + GcurvDeriv) gradS
  have hint₂ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - GcurvDeriv) gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (Gcurv + GcurvDeriv).toFun (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun hint₁ hint₂
  rw [hnull] at hsplit
  linarith [hsplit]

end Connection
end Integral
end DifferentialGeometry

end
