import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm

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








omit [FiniteDimensional ℝ E] in
theorem metricInverseInBasis_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : forall i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (fun a k => if a = k then 1 else 0) := by
  classical
  intro i j
  constructor <;> simp [hON]





theorem ricciFromRm13_comp_eq_rm04_trace
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 a i j k := by
  rw [ricciCompAt_apply]
  change ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
      (scalarOne0S (I := I) x)) (vec2 (basis i) (basis j)) = _
  rw [contract_trace13_component_basis (I := I) basis Rm13 i j]
  refine Finset.sum_congr rfl fun a _ => ?_
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
  simp only [smul_eq_mul]
  rw [← hLower (basis a) (basis i) (basis j) (basis k)]
  rw [rm04CompAt_apply]



theorem ricciComp_eq_rm04_trace_of_rm13
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hRic : Ric = ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 a i j k := by
  rw [hRic]
  exact ricciFromRm13_comp_eq_rm04_trace (I := I) g basis gInv hinv Rm13 Rm04 hLower i j

theorem ricciComp_eq_rm04_trace_of_rm13_section
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x))
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis (Rm04 x) a i j k := by
  exact ricciComp_eq_rm04_trace_of_rm13 (I := I) g basis gInv hinv (Ric x) (Rm13 x)
    (Rm04 x) (hRic x) hLower i j



theorem ricci_diag_eq_sum_rm04_diag_of_orthonormal
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x))
    (hON : forall i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (i j : Idx) :
    Ric x (vec2 (basis i) (basis j)) =
      ∑ a, Rm04 x (vec4 (basis a) (basis i) (basis j) (basis a)) := by
  classical
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (fun a k => if a = k then 1 else 0) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hcomp :=
    ricciComp_eq_rm04_trace_of_rm13_section
      (I := I) g basis (fun a k => if a = k then 1 else 0) hinv
      Ric Rm13 Rm04 hRic hLower i j
  simpa [ricciCompAt_apply, rm04CompAt_apply] using hcomp

theorem ricciCompAt_eq_contractTrace_of_realizes
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      componentRS_gen (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x (Rm13 x))
        Fin.elim0 (slots2 i j) := by
  rw [hRic x]
  exact ricciCompAt_eq_contractTrace (I := I) basis (Rm13 x) i j






def RicciRealizesRm04FirstTraceAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  forall a b : Idx,
    Ric (vec2 (basis a) (basis b)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis a) (basis b) (basis l))



omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
theorem ricciSymm_of_rm04
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hTrace : RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 gInv basis)
    (hPair : forall X Y Z W : TangentSpace I x,
      Rm04 (vec4 X Y Z W) = Rm04 (vec4 Z W X Y))
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (hInput : forall X Y Z W : TangentSpace I x,
      Rm04 (vec4 Y X Z W) = -Rm04 (vec4 X Y Z W))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    Ric (vec2 (basis a) (basis b)) =
      Ric (vec2 (basis b) (basis a)) := by
  classical
  rw [hTrace a b, hTrace b a]
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis a) (basis b) (basis l)))
        =
      ∑ l : Idx, ∑ k : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis a) (basis b) (basis l)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis l) (basis a) (basis b) (basis k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hInv l k]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis b) (basis a) (basis l)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          have hP := hPair (basis l) (basis a) (basis b) (basis k)
          have hI := hInput (basis k) (basis b) (basis l) (basis a)
          have hO := hOutput (basis k) (basis b) (basis l) (basis a)
          rw [hP, hI, hO]
          ring



theorem ricciFirstTraceAt_of_rm13
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hRic : Ric = ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (_hInvSym : forall i j : Idx, gInv i j = gInv j i) :
    RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 gInv basis := by
  intro i j
  have hcomp := ricciComp_eq_rm04_trace_of_rm13
    (I := I) g basis gInv hinv Ric Rm13 Rm04 hRic hLower i j
  rw [ricciCompAt_apply] at hcomp
  rw [hcomp]
  simp_rw [rm04CompAt_apply]


theorem ricciFirstTraceAt_of_rm13_section
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x))
    (hInvSym : forall i j : Idx, gInv i j = gInv j i) :
    RicciRealizesRm04FirstTraceAt (I := I) (Ric x) (Rm04 x) gInv basis := by
  exact ricciFirstTraceAt_of_rm13 (I := I) g basis gInv hinv
    (Ric x) (Rm13 x) (Rm04 x) (hRic x) hLower hInvSym






def RicciRealizesRm04TraceAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  forall X Y : TangentSpace I x,
    Ric (vec2 X Y) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) X Y (basis l))



def ScalarRealizesRicciTraceAt
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  scalar =
    ∑ i : Idx, ∑ j : Idx, gInv i j * Ric (vec2 (basis i) (basis j))

omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
theorem ricciComp_eq_trace_rm04
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hRic : RicciRealizesRm04TraceAt (I := I) Ric Rm04 gInv basis)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * rm04CompAt (I := I) basis Rm04 k i j l := by
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hRic (basis i) (basis j)

omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
theorem scalar_eq_trace_ricci
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric gInv basis) :
    scalar =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ricciCompAt (I := I) basis Ric i j := by
  rw [hScalar]
  simp_rw [ricciCompAt_apply]
end DifferentialGeometry.Integral.Connection
