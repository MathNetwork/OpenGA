import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian

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



omit [SigmaCompactSpace M] [T2Space M] in
theorem torsion_free_at_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {x : M}
    (htf : IsTorsionFreeAt (I := I) cov x)
    {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x := by
  unfold IsTorsionFreeAt at htf
  have hzero :=
    congrArg
      (fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x =>
        T (X x) (Y x))
      htf
  change cov.torsion x (X x) (Y x) = 0 at hzero
  rw [cov.torsion_apply hX hY] at hzero
  exact sub_eq_zero.mp hzero


omit [SigmaCompactSpace M] [T2Space M] in
theorem torsion_free_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : IsTorsionFree (I := I) cov)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x :=
  torsion_free_at_apply (I := I) (htf x) hX hY


omit [SigmaCompactSpace M] [T2Space M] in
theorem torsion_free_family_apply
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (htf : IsTorsionFreeFamilyOn (I := I) G)
    (t : RealTimeInterval.FlowTime D)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    G.connectionAt t Y x (X x) - G.connectionAt t X x (Y x) =
      VectorField.mlieBracket I X Y x :=
  torsion_free_apply (I := I) (htf t) hX hY



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem coordinate_basis_coord_eq_sum_inv_metric_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V =
      ∑ k : Idx, gInv a k * g.inner x (basis k) V := by
  symm
  calc
    (∑ k : Idx, gInv a k * g.inner x (basis k) V)
        = ∑ k : Idx, gInv a k *
            g.inner x (basis k) (∑ j : Idx, basis.coord j V • basis j) := by
          rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
    _ = ∑ k : Idx, ∑ j : Idx,
          gInv a k * (basis.coord j V * g.inner x (basis k) (basis j)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_sum]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ j : Idx, basis.coord j V *
          (∑ k : Idx, gInv a k * g.inner x (basis k) (basis j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ = ∑ j : Idx, basis.coord j V * (if a = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [(hinv a j).1]
    _ = basis.coord a V := by
      simp

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_coordinateFrame_eq_metric_derivs_of_mem
    (g : SmoothRiemannianMetric I M)
    (x0 : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x0)
    (i j l : CoordinateIdx (𝕜 := Real) E) :
    koszulScalar (I := I) g
        (coordinateFrameAt (I := I) x0 i)
        (coordinateFrameAt (I := I) x0 j)
        (coordinateFrameAt (I := I) x0 l) x =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
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
            (coordinateFrameAt (I := I) x0 j y)) x := by
  unfold koszulScalar
  rw [show
      (fun y : M =>
        g.inner y (coordinateFrameAt (I := I) x0 l y)
          (coordinateFrameAt (I := I) x0 i y)) =
      (fun y : M =>
        g.inner y (coordinateFrameAt (I := I) x0 i y)
          (coordinateFrameAt (I := I) x0 l y)) by
        funext y
        exact g.symm y (coordinateFrameAt (I := I) x0 l y)
          (coordinateFrameAt (I := I) x0 i y)]
  simp [coordinateFrameAt_bracket_zero_of_mem (I := I) hx i j,
    coordinateFrameAt_bracket_zero_of_mem (I := I) hx j l,
    coordinateFrameAt_bracket_zero_of_mem (I := I) hx l i]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_coordinateFrame_eq_metric_derivs
    (g : SmoothRiemannianMetric I M)
    (x0 : M) (i j l : CoordinateIdx (𝕜 := Real) E) :
    koszulScalar (I := I) g
        (coordinateFrameAt (I := I) x0 i)
        (coordinateFrameAt (I := I) x0 j)
        (coordinateFrameAt (I := I) x0 l) x0 =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x0 j y)
            (coordinateFrameAt (I := I) x0 l y)) x0 +
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x0 i y)
            (coordinateFrameAt (I := I) x0 l y)) x0 -
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x0 i y)
            (coordinateFrameAt (I := I) x0 j y)) x0 :=
  koszulScalar_coordinateFrame_eq_metric_derivs_of_mem
    (I := I) g x0 (coordinateFrameAt_mem (I := I) x0) i j l



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_coordinateFrame_symm
    (g : SmoothRiemannianMetric I M)
    (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E)
    (Z : (p : M) -> TangentSpace I p) :
    (1 / 2 : Real) *
        koszulScalar (I := I) g (coordinateFrameAt (I := I) x0 i)
          (coordinateFrameAt (I := I) x0 j) Z x0 =
      (1 / 2 : Real) *
        koszulScalar (I := I) g (coordinateFrameAt (I := I) x0 j)
          (coordinateFrameAt (I := I) x0 i) Z x0 :=
  sub_eq_zero.mp (by
    simpa [coordinateFrameAt_bracket_zero (I := I) x0 i j] using
      koszulScalar_swap_sub (I := I) g (coordinateFrameAt (I := I) x0 i)
        (coordinateFrameAt (I := I) x0 j) Z x0)




omit [SigmaCompactSpace M] [T2Space M] in
theorem coordinate_torsion_coeff_eq_christoffel_skew
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff k x0
        (cov.torsion x0
          (coordinateFrameAt (I := I) x0 i x0)
          (coordinateFrameAt (I := I) x0 j x0)) =
      christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k -
        christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k := by
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have h := DifferentialGeometry.Tensor.Coordinates.torsion_coeff_eq_christoffel_skew
    (I := I) cov (coordinateFrameAt (I := I) x0) hframe i j k
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j)
  rw [coordinateFrameAt_bracket_zero (I := I) x0 i j] at h
  simpa [hframe] using h



omit [SigmaCompactSpace M] [T2Space M] in
theorem coordinate_christoffel_symm_of_torsionFree
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : IsTorsionFree (I := I) cov)
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k := by
  have hzero :
      (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff k x0
          (cov.torsion x0
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0)) = 0 := by
    rw [htf x0]
    simp
  have hskew := coordinate_torsion_coeff_eq_christoffel_skew
    (I := I) cov x0 i j k
  rw [hzero] at hskew
  exact sub_eq_zero.mp hskew.symm


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinateFrame_apply_symm
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    (leviCivitaConnectionOfMetric (I := I) g
        (coordinateFrameAt (I := I) x0 j) x0)
        (coordinateFrameAt (I := I) x0 i x0) =
        (leviCivitaConnectionOfMetric (I := I) g
        (coordinateFrameAt (I := I) x0 i) x0)
        (coordinateFrameAt (I := I) x0 j x0) := by
  apply metricFlatLinear_injective (I := I) g x0
  ext v
  have hleft := leviCivitaConnectionOfMetric_inner_eq_koszulScalar_tangent
    (I := I) g (coordinateFrameAt (I := I) x0 i)
    (coordinateFrameAt (I := I) x0 j) x0
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j) v
  have hright := leviCivitaConnectionOfMetric_inner_eq_koszulScalar_tangent
    (I := I) g (coordinateFrameAt (I := I) x0 j)
    (coordinateFrameAt (I := I) x0 i) x0
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i) v
  have hK := koszulScalar_coordinateFrame_symm (I := I) g x0 i j
    (tangentConstAt (I := I) x0 v)
  simpa [metricFlatLinear_apply] using hleft.trans (hK.trans hright.symm)



omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinate_christoffel_symm
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k := by
  unfold christoffelSymbolInFrame
  rw [leviCivitaConnectionOfMetric_coordinateFrame_apply_symm (I := I) g x0 i j]






omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinate_christoffel_formula
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x0
      (coordinateFrameAt_toBasis (I := I) x0) gInv)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l *
            (directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 j y)
                    (coordinateFrameAt (I := I) x0 l y)) x0 +
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 l y)) x0 -
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 j y)) x0) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  let basis := coordinateFrameAt_toBasis (I := I) x0
  let A : TangentSpace I x0 :=
    (leviCivitaConnectionOfMetric (I := I) g (frame j) x0) (frame i x0)
  have hcoeff :
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
          frame hframe x0 i j k = basis.coord k A := by
    unfold christoffelSymbolInFrame A
    rw [coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x0]
  have hcoord :
      basis.coord k A =
        ∑ l : CoordinateIdx (𝕜 := Real) E, gInv k l * g.inner x0 (basis l) A :=
    coordinate_basis_coord_eq_sum_inv_metric_inner
      (I := I) g basis gInv hinv k A
  have hinner :
      ∀ l : CoordinateIdx (𝕜 := Real) E,
        g.inner x0 (basis l) A =
          (1 / 2 : Real) *
            koszulScalar (I := I) g (frame i) (frame j) (frame l) x0 := by
    intro l
    have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) g (frame i) (frame j) (frame l) x0
      (coordinateFrameAt_mdifferentiableAt (I := I) x0 i)
      (coordinateFrameAt_mdifferentiableAt (I := I) x0 j)
      (coordinateFrameAt_mdifferentiableAt (I := I) x0 l)
    calc
      g.inner x0 (basis l) A = g.inner x0 A (basis l) := by
        exact g.symm x0 (basis l) A
      _ = (1 / 2 : Real) *
            koszulScalar (I := I) g (frame i) (frame j) (frame l) x0 := by
        simpa [A, basis, frame] using hKos
  rw [hcoeff, hcoord]
  calc
    (∑ l : CoordinateIdx (𝕜 := Real) E, gInv k l * g.inner x0 (basis l) A)
        = ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv k l * ((1 / 2 : Real) *
              koszulScalar (I := I) g (frame i) (frame j) (frame l) x0) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hinner l]
    _ = (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l * koszulScalar (I := I) g (frame i) (frame j) (frame l) x0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l *
            (directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 j y)
                    (coordinateFrameAt (I := I) x0 l y)) x0 +
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 l y)) x0 -
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 j y)) x0) := by
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [koszulScalar_coordinateFrame_eq_metric_derivs (I := I) g x0 i j l]


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinate_torsion_basis_zero
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    (leviCivitaConnectionOfMetric (I := I) g).torsion x0
        (coordinateFrameAt (I := I) x0 i x0)
        (coordinateFrameAt (I := I) x0 j x0) = 0 := by
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  let hx : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  apply (hframe.toBasisAt hx).repr.injective
  ext k
  have hcoeff :
      hframe.coeff k x0
          ((leviCivitaConnectionOfMetric (I := I) g).torsion x0
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0)) = 0 := by
    rw [coordinate_torsion_coeff_eq_christoffel_skew
      (I := I) (leviCivitaConnectionOfMetric (I := I) g) x0 i j k]
    rw [leviCivitaConnectionOfMetric_coordinate_christoffel_symm (I := I) g x0 i j k]
    ring
  simpa [hframe, hx, IsLocalFrameOn.coeff] using hcoeff


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isTorsionFree
    (g : SmoothRiemannianMetric I M) :
    IsTorsionFree (I := I) (leviCivitaConnectionOfMetric (I := I) g) := by
  intro x
  change (leviCivitaConnectionOfMetric (I := I) g).torsion x = 0
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  let B := coordinateFrameAt_toBasis (I := I) x
  have hu : u = ∑ i : CoordinateIdx (𝕜 := Real) E, B.repr u i • B i :=
    (B.sum_repr u).symm
  have hv : v = ∑ j : CoordinateIdx (𝕜 := Real) E, B.repr v j • B j :=
    (B.sum_repr v).symm
  rw [hu, hv]
  simp [B, coordinateFrameAt_toBasis_apply,
    leviCivitaConnectionOfMetric_coordinate_torsion_basis_zero]



omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isLeviCivita
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g :=
  isLeviCivita_of_parts (I := I)
    (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g)

end DifferentialGeometry.Integral.Connection
