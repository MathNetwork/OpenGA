import DifferentialGeometry.Geometry.Curvature.Components.Lowering

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}













def curvatureTraceOneFormAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Y : TangentSpace I x) : Real :=
  -∑ i : Idx, ∑ j : Idx,
    gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j))




def CurvatureTraceOneFormEqRicVectorAt
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    curvatureTraceOneFormAt (I := I) Rm13 alpha basis gInv Y =
      Ric x (vec2 Y curvatureVector)

omit [DecidableEq Idx] in
theorem curvatureActionTraceEqualsRicVectorCoord_of_tensor
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (hcurv : CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13 alpha
      basis gInv curvatureVector) :
    CurvatureActionTraceEqualsRicGradCoord gInv
      (fun i k j => -Rm13 x alpha (vec3 (basis i) (basis k) (basis j)))
      (fun k => Ric x (vec2 (basis k) curvatureVector)) := by
  intro k
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * -Rm13 x alpha (vec3 (basis i) (basis k) (basis j)))
        = curvatureTraceOneFormAt (I := I) Rm13 alpha basis gInv (basis k) := by
          unfold curvatureTraceOneFormAt
          simp_rw [mul_neg, Finset.sum_neg_distrib]
    _ = Ric x (vec2 (basis k) curvatureVector) := hcurv (basis k)



omit [FiniteDimensional ℝ E] in
theorem basis_coord_eq_sum_inv_inner
    (g : SmoothRiemannianMetric I M)
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

theorem rm13_dualCoord_apply_eq_sum_inv_flat
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (a : Idx) (X Y Z : TangentSpace I x) :
    Rm13 (dualToCotangent_gen (I := I) (basis.coord a)) (vec3 X Y Z) =
      ∑ k : Idx,
        gInv a k *
          Rm13 (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis k)))
            (vec3 X Y Z) := by
  have hdual :
      dualToCotangent_gen (I := I) (basis.coord a) =
        ∑ k : Idx, gInv a k •
          dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis k)) := by
    apply cotangentToDualLinear_injective_gen (I := I) (x := x)
    ext V
    simp [tangentFlatLinear_apply_gen,
      basis_coord_eq_sum_inv_inner (I := I) g basis gInv hinv a V]
  rw [hdual]
  rw [_root_.map_sum Rm13]
  rw [tensor0SSpace_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [Tensor0SSpace.smul_apply]
  simp [smul_eq_mul]

theorem curvatureTraceOneFormEqRicVectorAt_of_metric_dual
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hAlpha :
      alpha =
        dualToCotangent_gen (I := I)
          ((tangentFlatLinear_gen (I := I) g x) curvatureVector)) :
    CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13 alpha basis gInv
      curvatureVector := by
  intro Y
  unfold curvatureTraceOneFormAt
  rw [hAlpha]
  calc
    -(∑ i : Idx, ∑ j : Idx,
        gInv i j *
          Rm13 x
            (dualToCotangent_gen (I := I)
              ((tangentFlatLinear_gen (I := I) g x) curvatureVector))
            (vec3 (basis i) Y (basis j)))
        = ∑ i : Idx, ∑ j : Idx,
            gInv i j *
              Rm13 x
                (dualToCotangent_gen (I := I)
                  ((tangentFlatLinear_gen (I := I) g x) (basis j)))
                (vec3 (basis i) Y curvatureVector) := by
          have hrewrite : ∀ i j : Idx,
              Rm13 x
                (dualToCotangent_gen (I := I)
                  ((tangentFlatLinear_gen (I := I) g x) curvatureVector))
                (vec3 (basis i) Y (basis j)) =
              -Rm13 x
                (dualToCotangent_gen (I := I)
                  ((tangentFlatLinear_gen (I := I) g x) (basis j)))
                (vec3 (basis i) Y curvatureVector) := by
            intro i j
            exact hSkew curvatureVector (basis i) Y (basis j)
          simp_rw [hrewrite]
          simp_rw [mul_neg, Finset.sum_neg_distrib]
          ring
    _ = ∑ i : Idx,
          Rm13 x (dualToCotangent_gen (I := I) (basis.coord i))
            (vec3 (basis i) Y curvatureVector) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (rm13_dualCoord_apply_eq_sum_inv_flat (I := I) g basis gInv hinv
            (Rm13 x) i (basis i) Y curvatureVector).symm
    _ = ricciFromRm13At (I := I) (M := M) (Rm13 x)
          (vec2 Y curvatureVector) := by
          rw [ricciFromRm13At_apply_basis_trace (I := I) basis (Rm13 x)
            Y curvatureVector]
    _ = Ric x (vec2 Y curvatureVector) := by
          rw [hRic x]
end DifferentialGeometry.Integral.Connection
