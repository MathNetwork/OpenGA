import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false










namespace DifferentialGeometry.Integral.Connection

open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]






def LeviCivitaConnectionUniqueOnSmooth
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _),
    CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ->
      CovariantDerivative.ContMDiffCovariantDerivative cov' ∞ ->
        IsLeviCivita (I := I) cov g ->
          IsLeviCivita (I := I) cov' g ->
            forall {x : M} (Y : (p : M) -> TangentSpace I p),
              MDiffAt (T% Y) x ->
                forall v : TangentSpace I x,
                  cov Y x v = cov' Y x v


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_inner_eq_half_koszul
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hlc : IsLeviCivita (I := I) cov g)
    {X Y Z : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (cov Y x (X x)) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  have hmc := metricCompatible_of_isLeviCivita (I := I) hlc
  have htf := torsionFree_of_isLeviCivita (I := I) hlc
  have hXYZ := Connection.metric_compatible_apply (I := I) hmc X Y Z hX hY hZ
  have hYZX := Connection.metric_compatible_apply (I := I) hmc Y Z X hY hZ hX
  have hZXY := Connection.metric_compatible_apply (I := I) hmc Z X Y hZ hX hY
  have htYZ := torsion_free_apply (I := I) htf (X := Y) (Y := Z) hY hZ
  have htZX := torsion_free_apply (I := I) htf (X := Z) (Y := X) hZ hX
  have htXY := torsion_free_apply (I := I) htf (X := X) (Y := Y) hX hY
  change directionalDerivAlong (I := I) X
      (fun y : M => g.inner y (Y y) (Z y)) x =
    g.inner x (cov Y x (X x)) (Z x) +
      g.inner x (Y x) (cov Z x (X x)) at hXYZ
  change directionalDerivAlong (I := I) Y
      (fun y : M => g.inner y (Z y) (X y)) x =
    g.inner x (cov Z x (Y x)) (X x) +
      g.inner x (Z x) (cov X x (Y x)) at hYZX
  change directionalDerivAlong (I := I) Z
      (fun y : M => g.inner y (X y) (Y y)) x =
    g.inner x (cov X x (Z x)) (Y x) +
      g.inner x (X x) (cov Y x (Z x)) at hZXY
  unfold koszulScalar
  rw [hXYZ, hYZX, hZXY, ← htYZ, ← htZX, ← htXY]
  simp only [map_sub]
  rw [g.symm x (cov Z x (Y x)) (X x)]
  rw [g.symm x (Z x) (cov X x (Y x))]
  rw [g.symm x (cov X x (Z x)) (Y x)]
  rw [g.symm x (X x) (cov Y x (Z x))]
  rw [g.symm x (Y x) (cov Z x (X x))]
  rw [← g.symm x (cov Y x (X x)) (Z x)]
  ring







omit [SigmaCompactSpace M] [T2Space M] in
theorem coordinateFrame_christoffel_formula_point_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x0 : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x0)
    (gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x
      (coordinateFrameAt_basis (I := I) x0 hx) gInv)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x i j k =
      (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l *
            (directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 j y)
                    (coordinateFrameAt (I := I) x0 l y)) x +
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 l y)) x -
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 j y)) x) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  let basis := coordinateFrameAt_basis (I := I) x0 hx
  let A : TangentSpace I x := (cov (frame j) x) (frame i x)
  have hdiff :
      ∀ a : CoordinateIdx (𝕜 := Real) E, MDiffAt (T% (frame a)) x := by
    intro a
    exact (((coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffAt
      (coordinateFrameSet_open (I := I) x0) hx a).mdifferentiableAt
        (by simp))
  have hcoeff :
      christoffelSymbolInFrame cov frame hframe x i j k = basis.coord k A := by
    unfold christoffelSymbolInFrame A
    have hbasis :
        hframe.toBasisAt hx = basis := by
      ext a
      rw [IsLocalFrameOn.toBasisAt_coe]
      rw [coordinateFrameAt_basis_apply]
    unfold IsLocalFrameOn.coeff
    rw [dif_pos hx, hbasis]
  have hcoord :
      basis.coord k A =
        ∑ l : CoordinateIdx (𝕜 := Real) E, gInv k l * g.inner x (basis l) A :=
    coordinate_basis_coord_eq_sum_inv_metric_inner
      (I := I) g basis gInv hinv k A
  have hinner :
      ∀ l : CoordinateIdx (𝕜 := Real) E,
        g.inner x (basis l) A =
          (1 / 2 : Real) *
            koszulScalar (I := I) g (frame i) (frame j) (frame l) x := by
    intro l
    have hKos := leviCivita_inner_eq_half_koszul
      (I := I) (cov := cov) (g := g) hLC
      (X := frame i) (Y := frame j) (Z := frame l)
      (x := x) (hdiff i) (hdiff j) (hdiff l)
    calc
      g.inner x (basis l) A = g.inner x A (basis l) := by
        exact g.symm x (basis l) A
      _ = (1 / 2 : Real) *
            koszulScalar (I := I) g (frame i) (frame j) (frame l) x := by
        simpa [A, basis, frame] using hKos
  rw [hcoeff, hcoord]
  calc
    (∑ l : CoordinateIdx (𝕜 := Real) E, gInv k l * g.inner x (basis l) A)
        = ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv k l * ((1 / 2 : Real) *
              koszulScalar (I := I) g (frame i) (frame j) (frame l) x) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hinner l]
    _ = (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l * koszulScalar (I := I) g (frame i) (frame j) (frame l) x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l *
            (directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 j y)
                    (coordinateFrameAt (I := I) x0 l y)) x +
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 l y)) x -
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 j y)) x) := by
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [koszulScalar_coordinateFrame_eq_metric_derivs_of_mem
            (I := I) g x0 hx i j l]




omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_apply_eq_of_smooth
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (_hcovSmooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (_hcov'Smooth : CovariantDerivative.ContMDiffCovariantDerivative cov' ∞)
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  simp only [metricFlatLinear_apply]
  let Z : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x v
  have hZ : MDiffAt (T% Z) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x v
  have hleft := leviCivita_inner_eq_half_koszul
    (I := I) (cov := cov) (g := g) hcov
    (X := X) (Y := Y) (Z := Z) hX hY hZ
  have hright := leviCivita_inner_eq_half_koszul
    (I := I) (cov := cov') (g := g) hcov'
    (X := X) (Y := Y) (Z := Z) hX hY hZ
  have hZx : Z x = v := by
    change tangentConstAt (I := I) x v x = v
    rw [tangentConstAt_self]
  rw [hZx] at hleft hright
  exact hleft.trans hright.symm


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_apply_eq_of_smooth_direction
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hcovSmooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (hcov'Smooth : CovariantDerivative.ContMDiffCovariantDerivative cov' ∞)
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g)
    {x : M} (Y : (p : M) -> TangentSpace I p)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    cov Y x v = cov' Y x v := by
  let X : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x v
  have hX : MDiffAt (T% X) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x v
  have h := leviCivita_apply_eq_of_smooth
    (I := I) (cov := cov) (cov' := cov') (g := g)
    hcovSmooth hcov'Smooth hcov hcov' (X := X) (Y := Y) hX hY
  have hXx : X x = v := by
    change tangentConstAt (I := I) x v x = v
    rw [tangentConstAt_self]
  rw [hXx] at h
  exact h


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionUniqueOnSmooth
    (g : SmoothRiemannianMetric I M) :
    LeviCivitaConnectionUniqueOnSmooth (I := I) g := by
  intro cov cov' hcovSmooth hcov'Smooth hcov hcov' x Y hY v
  exact leviCivita_apply_eq_of_smooth_direction
    (I := I) (cov := cov) (cov' := cov') (g := g)
    hcovSmooth hcov'Smooth hcov hcov' (x := x) Y hY v

end DifferentialGeometry.Integral.Connection
