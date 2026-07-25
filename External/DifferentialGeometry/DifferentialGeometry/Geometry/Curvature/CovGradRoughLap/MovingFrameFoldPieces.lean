import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderCarrierSection
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

noncomputable section

set_option backward.isDefEq.respectTransparency false
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

theorem frameSummand_leadingSlot_secondOrder_commutation_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) -
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) =
      nablaTensorCurvSec (I := I) g
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)
          (unitEvalSection (I := I) (M := M) g s S) x
        + (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (smoothOrthoFrame (I := I) g x i)
              (unitEvalSection (I := I) (M := M) g s S) x
            + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (unitEvalSection (I := I) (M := M) g s S) x
            + (2 : ℝ) • riemannSec
              (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i)
                (unitEvalSection (I := I) (M := M) g s S)) x)
        + secondOrderChristoffelResidual (I := I) g
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (unitEvalSection (I := I) (M := M) g s S) x := by
  have hB := smoothOrthoFrame_smooth (I := I) (M := M) g x i
  exact covGrad_covDeriv_leadingSlot_secondOrder_commutation (I := I) (M := M) g s S hB hB x

omit [CompactSpace M] [I.Boundaryless] in

omit [SigmaCompactSpace M] in
theorem frame_cyclic_second_bianchi_orthoFrame
    (g : SmoothRiemannianMetric I M)
    {Z W : Π b : M, TangentSpace I b} {x : M}
    (i : Fin (Module.finrank ℝ E))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) Z W x +
      nablaCurvSec (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) Z (smoothOrthoFrame (I := I) g x i) W x +
      nablaCurvSec (LeviCivita (I := I) g)
        Z (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) W x = 0 := by
  have hB := smoothOrthoFrame_smooth (I := I) (M := M) g x i
  exact second_bianchi_levi_civita_metric (I := I) (M := M) g hB hB hZ hW

omit [CompactSpace M] [I.Boundaryless] in

omit [SigmaCompactSpace M] in
theorem frameSummed_contracted_second_bianchi_eq_half_nablaScalar
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b} {x : M}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ∑ j, nablaRicci (I := I) g
        (smoothOrthoFrame (I := I) g x j) (smoothOrthoFrame (I := I) g x j) V x =
      1 / 2 * nablaScalar (I := I) g V x := by
  exact contracted_second_bianchi (I := I) (M := M) g hV

noncomputable def christoffelResidualPairingFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  covariantTensorInnerPointwise (I := I) (M := M) s g x
    (Tensor0SSpace.toModel
      (secondOrderChristoffelResidual (I := I) g
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
        (unitEvalSection (I := I) (M := M) g s S) x))
    (Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x)))

end Connection
end Integral
end DifferentialGeometry

end
