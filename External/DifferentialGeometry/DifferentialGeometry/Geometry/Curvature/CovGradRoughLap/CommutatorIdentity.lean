import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.AbstractRoughLaplacian
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement


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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma zeroTensor_eq_smul_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (tensor0Iso (I := I) M x D) • unitZeroSec (I := I) (M := M) x := by
  classical
  have hunit : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  apply (tensor0Iso (I := I) M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor03_ext_unit {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D]
  rw [map_smul, map_smul, h]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma curry_unitGradField_eq (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) (y : M) (w : TangentSpace I y) :
    tensor0S_curry (I := I) (M := M) 2 y (unitGradField (I := I) (M := M) g T₀ y) w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y w)
        (unitZeroSec (I := I) (M := M) y) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) 2 y (unitGradField (I := I) (M := M) g T₀ y) w) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y w)
        (unitZeroSec (I := I) (M := M) y)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := unitGradField (I := I) (M := M) g T₀ y) (v0 := w) (vs := m)]
  rw [unitGradField_apply]
  rw [covGrad_apply_unit_eval (I := I) (M := M) g T₀ y (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma curry_covGrad_unit_eval (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 S x w)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 S x w)
        (unitZeroSec (I := I) (M := M) x)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (covGrad (I := I) (M := M) g 0 2 S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v0 := w) (vs := m)]
  rw [covGrad_apply_unit_eval_generic (I := I) (M := M) g S x (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

omit [NeZero (Module.finrank ℝ E)] in
lemma curry_abstract_covDeriv_unitGrad_unfold
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M (unitGradField (I := I) (M := M) g T₀) y)) x)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x (X x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (Y y))
              (unitZeroSec (I := I) (M := M) y)) x (X x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
            ((LeviCivita (I := I) g).toFun Y x (X x)))
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hstep := abstract_succ_covDeriv_unfold_at (I := I) (M := M) g
    (unitGradField (I := I) (M := M) g T₀) (Vfield := X) (Y := Y) (x := x) hC hX hY
  rw [hstep]
  have hsec : (fun y : M => curriedSection I M (unitGradField (I := I) (M := M) g T₀) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (Y y))
          (unitZeroSec (I := I) (M := M) y)) := by
    funext y
    rw [curriedSection_apply]
    exact curry_unitGradField_eq (I := I) (M := M) g T₀ y (Y y)
  have hchr : curriedSection I M (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun Y x (X x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
          ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [curriedSection_apply]
    exact curry_unitGradField_eq (I := I) (M := M) g T₀ x
      ((LeviCivita (I := I) g).toFun Y x (X x))
  rw [hsec, hchr]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_unitGradField (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (unitGradField (I := I) (M := M) g T₀ y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel 3 ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g 0 2 T₀).toSection y))) :=
    covGrad_contMDiff_mk' (I := I) (M := M) g T₀
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace 3 I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 3 ℝ E) hϕ hv

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_curried_unitGradField (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M (unitGradField (I := I) (M := M) g T₀) y)) :=
  (contMDiff_curriedSection_iff_section (I := I) (M := M)
    (unitGradField (I := I) (M := M) g T₀)).mp
    (contMDiff_unitGradField (I := I) (M := M) g T₀)

omit [NeZero (Module.finrank ℝ E)] in
lemma curry_abstract_covDeriv_unitGrad_unfold'
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x (X x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (Y y))
              (unitZeroSec (I := I) (M := M) y)) x (X x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
            ((LeviCivita (I := I) g).toFun Y x (X x)))
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  refine curry_abstract_covDeriv_unitGrad_unfold (I := I) (M := M) g T₀ ?_ ?_ ?_
  · exact (contMDiff_curried_unitGradField (I := I) (M := M) g T₀ x).mdifferentiableAt (by simp)
  · exact (hX x).mdifferentiableAt (by simp)
  · exact (hY x).mdifferentiableAt (by simp)

end Connection
end Integral
end DifferentialGeometry

end
