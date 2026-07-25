import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CommutatorIdentity

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

omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_covApply_unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
          (unitGradField (I := I) (M := M) g T₀) y)) := by
  classical
  have hU : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (unitGradField (I := I) (M := M) g T₀ y)) :=
    contMDiff_unitGradField (I := I) (M := M) g T₀
  exact covApply_contMDiff
    (cov := Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) hX hU

omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_curried_covApply_unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) y)) :=
  (contMDiff_curriedSection_iff_section (I := I) (M := M)
    (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
      (unitGradField (I := I) (M := M) g T₀))).mp
    (contMDiff_covApply_unitGradField (I := I) (M := M) g T₀ hX)

omit [NeZero (Module.finrank ℝ E)] in
lemma curriedSection_covApply_unitGradField_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (fun y : M =>
      curriedSection I M
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
          (unitGradField (I := I) (M := M) g T₀)) y (Y y)) =
      (fun y : M =>
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
            (fun z : M =>
              (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z (Y z))
                (unitZeroSec (I := I) (M := M) z)) y (X y) -
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
            tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y
              ((LeviCivita (I := I) g).toFun Y y (X y)))
            (unitZeroSec (I := I) (M := M) y)) := by
  classical
  funext y
  rw [curriedSection_apply]
  rw [covApply_apply]
  exact curry_abstract_covDeriv_unitGrad_unfold' (I := I) (M := M) g T₀ hX hY

omit [NeZero (Module.finrank ℝ E)] in
lemma curry_abstract_covDeriv_covApply_unitGrad_unfold
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hVfield : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Vfield))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun z : M =>
            curriedSection I M
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
                (unitGradField (I := I) (M := M) g T₀)) z (Y z)) x (Vfield x) -
        curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  exact abstract_succ_covDeriv_unfold_at (I := I) (M := M) g
    (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
      (unitGradField (I := I) (M := M) g T₀))
    (Vfield := Vfield) (Y := Y) (x := x)
    ((contMDiff_curried_covApply_unitGradField (I := I) (M := M) g T₀ hX x).mdifferentiableAt
      (by simp))
    ((hVfield x).mdifferentiableAt (by simp))
    ((hY x).mdifferentiableAt (by simp))

omit [NeZero (Module.finrank ℝ E)] in
lemma curry_abstract_covDeriv_covApply_unitGrad_unfold_inner
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hVfield : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Vfield))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun z : M =>
            (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
                (fun u : M =>
                  (show Tensor0SSpace 0 I u →L[ℝ] Tensor0SSpace 2 I u from
                    tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ u (Y u))
                    (unitZeroSec (I := I) (M := M) u)) z (X z) -
              (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z
                  ((LeviCivita (I := I) g).toFun Y z (X z)))
                (unitZeroSec (I := I) (M := M) z)) x (Vfield x) -
        curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  rw [curry_abstract_covDeriv_covApply_unitGrad_unfold (I := I) (M := M) g T₀ hX hVfield hY]
  rw [curriedSection_covApply_unitGradField_eq (I := I) (M := M) g T₀ hX hY]

end Connection
end Integral
end DifferentialGeometry

end
