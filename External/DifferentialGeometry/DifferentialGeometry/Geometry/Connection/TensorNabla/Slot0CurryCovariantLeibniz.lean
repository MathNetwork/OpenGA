import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.BareSlot0CurryParseval


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
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


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor00Scalar_unitZeroSec (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_unit_eval (t : ℕ) (x : M) (C : Tensor0SSpace t I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) = C := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) =
      tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) • C from
    tensor0SAsRS_apply (I := I) (M := M) x C (unitZeroSec (I := I) (M := M) x)]
  rw [tensor00Scalar_unitZeroSec (I := I) (M := M) x, one_smul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contMDiff_tensor00Scalar_read
    (Y : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun z : M => Tensor0SSpace 0 I z)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) := by
  have heq : (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) =
      Tensor0SNabla.scalarFn I M (fun y : M => Y y) := by
    funext y
    rfl
  rw [heq]
  exact (Tensor0SNabla.contMDiff_scalarFn_iff_section I M (fun y : M => Y y)).mpr Y.contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma contMDiff_tensor0SAsRS_wrap (t : ℕ) {C : Π y : M, Tensor0SSpace t I y}
    (hC : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel t ℝ E)
        (E := fun z : M => Tensor0SSpace t I z) y (C y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y
        (tensor0SToTensorRS (I := I) (M := M) y (C y))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel t ℝ E) (V₂ := fun z : M => Tensor0SSpace t I z)
    (φ := fun y : M => tensor0SToTensorRS (I := I) (M := M) y (C y))
  intro Y
  have hsmul := ContMDiff.smul_section (n := (∞ : WithTop ℕ∞))
    (contMDiff_tensor00Scalar_read (I := I) (M := M) Y) hC
  refine hsmul.congr fun y => ?_
  rw [show ((fun z : M => tensor00Scalar (I := I) (M := M) z (Y z)) • C) y =
      tensor00Scalar (I := I) (M := M) y (Y y) • C y from rfl]
  rw [← tensor0SAsRS_apply (I := I) (M := M) y (C y) (Y y)]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contMDiff_unitEvalSection (g : SmoothRiemannianMetric I M) (k : ℕ)
    (Z : SmoothCcTensor g 0 k) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SSpace k I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y)
          (unitZeroSec (I := I) (M := M) y))) := by
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel k ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace k I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y))) :=
    Z.toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace k I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel k ℝ E) hϕ hv


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma contMDiff_slot0Read (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 (s + 1)) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (tensor0SToTensorRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))) := by
  have hUzS := contMDiff_unitEvalSection (I := I) (M := M) g (s + 1) Z
  have hcur : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y)))) :=
    fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
      (I := I) (M := M)
      (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (s + 1) I z from
        Z.toSection z) (unitZeroSec (I := I) (M := M) z)) y (hUzS y)
  have hCs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) :=
    ContMDiff.clm_bundle_apply (b := fun y : M => y)
      (E₁ := TangentSpace I) (E₂ := fun z : M => Tensor0SSpace s I z)
      (F₁ := E) (F₂ := Tensor0SModel s ℝ E) hcur hX
  exact contMDiff_tensor0SAsRS_wrap (I := I) (M := M) s hCs

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor0S_curry_covApply_slot0_leibniz_fib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (Z : SmoothCcTensor g 0 (s + 1))
    {V X : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covApply (tensorCov (I := I) g 0 (s + 1)) V
            (fun y : M => Z.toSection y) x)
          (unitZeroSec (I := I) (M := M) x))) (X x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x)
        (unitZeroSec (I := I) (M := M) x) -
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          Z.toSection x) (unitZeroSec (I := I) (M := M) x)))
        ((LeviCivita (I := I) g).toFun X x (V x)) := by
  classical
  have hVAt : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (V b)) x :=
    (hV x).mdifferentiableAt (by simp)
  have hunitAt : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) x :=
    ((contMDiff_unitZeroSection (I := I) (M := M)) x).mdifferentiableAt (by simp)
  have hZAt : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y (Z.toSection y)) x :=
    (Z.toSection.contMDiff x).mdifferentiableAt (by simp)
  have hA : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        covApply (tensorCov (I := I) g 0 (s + 1)) V
          (fun y : M => Z.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
        (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Z.toSection y) (unitZeroSec (I := I) (M := M) y)) x (V x) := by
    have happ := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
      0 (s + 1) (LeviCivita (I := I) g) (fun y : M => Z.toSection y)
      (fun y : M => unitZeroSec (I := I) (M := M) y) V hZAt hunitAt hVAt
    rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
          (fun y : M => unitZeroSec (I := I) (M := M) y) x (V x)) = 0 from
      tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
        (LeviCivita (I := I) g) x (V x)] at happ
    rw [map_zero, sub_zero] at happ
    exact happ
  have hUzS := contMDiff_unitEvalSection (I := I) (M := M) g (s + 1) Z
  have hUzAt : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        Z.toSection y) (unitZeroSec (I := I) (M := M) y)) x :=
    (hUzS x).mdifferentiableAt (by simp)
  have hB := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M)
    g s (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      Z.toSection y) (unitZeroSec (I := I) (M := M) y)) hUzAt ⟨X, hX⟩ (V x)
  have hρS := contMDiff_slot0Read (I := I) (M := M) g s Z hX
  have hρAt : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (tensor0SToTensorRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))) x :=
    (hρS x).mdifferentiableAt (by simp)
  have happ2 := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
    0 s (LeviCivita (I := I) g)
    (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))
    (fun y : M => unitZeroSec (I := I) (M := M) y) V hρAt hunitAt hVAt
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x (V x)) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x (V x)] at happ2
  rw [map_zero, sub_zero] at happ2
  have hsec : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        tensor0SToTensorRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))
        (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)) := by
    funext y
    exact tensor0SAsRS_unit_eval (I := I) (M := M) s y _
  rw [hsec] at happ2
  have hC2 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      covApply (tensorCov (I := I) g 0 s) V
        (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x)
      (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)) x (V x) :=
    happ2
  rw [hA]
  have hfinal := eq_sub_of_add_eq hB.symm
  simp only [ContMDiffSection.coeFn_mk, Tensor0SNabla.curriedSection_apply] at hfinal
  rw [hfinal, ← hC2]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor0S_curry_covApply_slot0_leibniz
    (g : SmoothRiemannianMetric I M) (s : ℕ) (Z : SmoothCcTensor g 0 (s + 1))
    {V X : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            covApply (tensorCov (I := I) g 0 (s + 1)) V
              (fun y : M => Z.toSection y) x)
            (unitZeroSec (I := I) (M := M) x))) (X x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          covApply (tensorCov (I := I) g 0 s) V
            (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
                ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                  Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x)
          (unitZeroSec (I := I) (M := M) x)) m -
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            Z.toSection x) (unitZeroSec (I := I) (M := M) x)))
          ((LeviCivita (I := I) g).toFun X x (V x))) m := by
  rw [tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s Z hV hX x]
  rw [Tensor0SSpace.toModel_sub]
  rfl

end Connection
end Integral
end DifferentialGeometry

end
