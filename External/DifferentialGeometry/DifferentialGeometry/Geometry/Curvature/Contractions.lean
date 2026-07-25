import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.Bianchi

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



theorem oneForm_eq_sum_inv_flat
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    β =
      ∑ p : Idx,
        (∑ q : Idx, gInv p q * β (fun _ : Fin 1 => basis q)) •
          dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis p)) := by
  apply cotangentToDualLinear_injective_gen (I := I) (x := x)
  ext V
  have hsharp := cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv β
  have hpair :
      cotangentToDual_gen (I := I) β V =
        g.inner x
          (∑ p : Idx,
            (∑ q : Idx, gInv p q * cotangentToDual_gen (I := I) β (basis q)) •
              basis p) V := by
    calc
      cotangentToDual_gen (I := I) β V =
          g.inner x (cotangentSharp_gen (I := I) g x β) V := by
            rw [cotangentSharp_inner_gen]
      _ =
          g.inner x
            (∑ p : Idx,
              (∑ q : Idx, gInv p q * cotangentToDual_gen (I := I) β (basis q)) •
                basis p) V := by
            rw [hsharp]
  simpa [tangentFlatLinear_apply_gen, cotangentToDual_apply_gen, map_sum, Finset.sum_mul,
    smul_eq_mul] using hpair



theorem rm13_oneForm_apply_eq_sum_inv_flat
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    Rm13 β (vec3 X Y Z) =
      ∑ p : Idx,
        (∑ q : Idx, gInv p q * β (fun _ : Fin 1 => basis q)) *
          Rm13
            (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis p)))
            (vec3 X Y Z) := by
  have hβ := oneForm_eq_sum_inv_flat (I := I) g basis gInv hinv β
  calc
    Rm13 β (vec3 X Y Z)
        =
      Rm13
        (∑ p : Idx,
          (∑ q : Idx, gInv p q * β (fun _ : Fin 1 => basis q)) •
            dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis p)))
        (vec3 X Y Z) :=
          congrArg (fun γ => Rm13 γ (vec3 X Y Z)) hβ
    _ =
      ∑ p : Idx,
        (∑ q : Idx, gInv p q * β (fun _ : Fin 1 => basis q)) *
          Rm13
            (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis p)))
            (vec3 X Y Z) := by
          rw [_root_.map_sum Rm13]
          rw [tensor0SSpace_sum_apply]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [map_smul]
          rfl


def raised02CompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv i a * gInv j b * A (vec2 (basis a) (basis b))


def oneUp02CompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (i k : Idx) : Real :=
  ∑ a : Idx, gInv k a * A (vec2 (basis i) (basis a))


def rm04RicciContractionAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (a b : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
      raised02CompAt (I := I) basis gInv A k l


def ricciQuadraticAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (a b : Idx) : Real :=
  ∑ k : Idx,
    oneUp02CompAt (I := I) basis gInv A a k *
      A (vec2 (basis k) (basis b))


omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
private theorem raised02CompAt_symm
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    raised02CompAt (I := I) basis gInv A a b =
      raised02CompAt (I := I) basis gInv A b a := by
  classical
  unfold raised02CompAt
  calc
    (∑ p : Idx, ∑ q : Idx,
        gInv a p * gInv b q * A (vec2 (basis p) (basis q)))
        =
      ∑ q : Idx, ∑ p : Idx,
        gInv a p * gInv b q * A (vec2 (basis p) (basis q)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ p : Idx, ∑ q : Idx,
        gInv b p * gInv a q * A (vec2 (basis p) (basis q)) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hInv a p, hInv b q, hA p q]
          ring



omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
private theorem ricciQuadraticAt_symm
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    ricciQuadraticAt (I := I) basis gInv A a b =
      ricciQuadraticAt (I := I) basis gInv A b a := by
  classical
  unfold ricciQuadraticAt oneUp02CompAt
  calc
    (∑ k : Idx,
        (∑ p : Idx, gInv k p * A (vec2 (basis a) (basis p))) *
          A (vec2 (basis k) (basis b)))
        =
      ∑ k : Idx, ∑ p : Idx,
        gInv k p * A (vec2 (basis a) (basis p)) *
          A (vec2 (basis k) (basis b)) := by
          simp [Finset.sum_mul, mul_assoc]
    _ =
      ∑ p : Idx, ∑ k : Idx,
        gInv k p * A (vec2 (basis a) (basis p)) *
          A (vec2 (basis k) (basis b)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ p : Idx, ∑ k : Idx,
        gInv p k * A (vec2 (basis b) (basis k)) *
          A (vec2 (basis p) (basis a)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv k p, hA a p, hA k b]
          ring
    _ =
      ∑ p : Idx,
        (∑ k : Idx, gInv p k * A (vec2 (basis b) (basis k))) *
          A (vec2 (basis p) (basis a)) := by
          simp [Finset.sum_mul, mul_assoc]



omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
private theorem rm04RicciContractionAt_symm
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 (vec4 W X Y Z) = Rm04 (vec4 Y Z W X))
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    rm04RicciContractionAt (I := I) basis Rm04 gInv A a b =
      rm04RicciContractionAt (I := I) basis Rm04 gInv A b a := by
  classical
  unfold rm04RicciContractionAt
  calc
    (∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
          raised02CompAt (I := I) basis gInv A k l)
        =
      ∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (basis b) (basis l) (basis a) (basis k)) *
          raised02CompAt (I := I) basis gInv A k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hPair (basis a) (basis k) (basis b) (basis l)]
    _ =
      ∑ l : Idx, ∑ k : Idx,
        Rm04 (vec4 (basis b) (basis l) (basis a) (basis k)) *
          raised02CompAt (I := I) basis gInv A k l := by
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (basis b) (basis k) (basis a) (basis l)) *
          raised02CompAt (I := I) basis gInv A k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [raised02CompAt_symm (I := I) basis gInv A hA hInv l k]



omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
private theorem rm04_slot1_trace_eq_neg_ricci
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hTrace : RicciRealizesRm04FirstTraceAt (I := I) A Rm04 gInv basis)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 (vec4 W X Y Z) = Rm04 (vec4 Y Z W X))
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (p a : Idx) :
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis p) (basis k) (basis a) (basis l))) =
      -A (vec2 (basis p) (basis a)) := by
  classical
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis p) (basis k) (basis a) (basis l)))
        =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis a) (basis l) (basis p) (basis k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hPair (basis p) (basis k) (basis a) (basis l)]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * (-Rm04 (vec4 (basis a) (basis l) (basis k) (basis p))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hOutput (basis a) (basis l) (basis p) (basis k)]
    _ =
      -(∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis p) (basis a) (basis l))) := by
          simp only [mul_neg, Finset.sum_neg_distrib, neg_inj]
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 1
          rw [hPair (basis a) (basis l) (basis k) (basis p)]
    _ = -A (vec2 (basis p) (basis a)) := by
          rw [hTrace p a]




omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
theorem rm04_trace_first_third_eq_neg_ricci
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hTrace : RicciRealizesRm04FirstTraceAt (I := I) A Rm04 gInv basis)
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (_hFirst : FirstBianchiAt (I := I) Rm04)
    (_hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (_hInv : forall i j : Idx, gInv i j = gInv j i)
    (k l : Idx) :
    (∑ a : Idx, ∑ b : Idx,
        gInv a b * Rm04 (vec4 (basis a) (basis k) (basis b) (basis l))) =
      -A (vec2 (basis k) (basis l)) := by
  classical
  calc
    (∑ a : Idx, ∑ b : Idx,
        gInv a b * Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)))
        =
      ∑ a : Idx, ∑ b : Idx,
        gInv a b * (-Rm04 (vec4 (basis a) (basis k) (basis l) (basis b))) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hOutput (basis a) (basis k) (basis b) (basis l)]
    _ =
      -(∑ a : Idx, ∑ b : Idx,
        gInv a b * Rm04 (vec4 (basis a) (basis k) (basis l) (basis b))) := by
          simp [Finset.sum_neg_distrib]
    _ = -A (vec2 (basis k) (basis l)) := by
        rw [hTrace k l]



omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
private theorem contracted_slot1_eq_quadratic
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hTrace : RicciRealizesRm04FirstTraceAt (I := I) A Rm04 gInv basis)
    (_hPair : forall W X Y Z : TangentSpace I x,
      Rm04 (vec4 W X Y Z) = Rm04 (vec4 Y Z W X))
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (hFirst : FirstBianchiAt (I := I) Rm04)
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    -(∑ k : Idx, ∑ l : Idx,
        gInv k l *
          (∑ p : Idx,
            (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
              Rm04 (vec4 (basis k) (basis a) (basis l) (basis p)))) =
      ricciQuadraticAt (I := I) basis gInv A a b := by
  classical
  calc
    -(∑ k : Idx, ∑ l : Idx,
        gInv k l *
          (∑ p : Idx,
            (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
              Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))))
        =
      -∑ p : Idx,
        (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l * Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))) := by
          congr 1
          calc
            (∑ k : Idx, ∑ l : Idx,
                gInv k l *
                  (∑ p : Idx,
                    (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                      Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))))
                =
              ∑ k : Idx, ∑ p : Idx, ∑ l : Idx,
                (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                  (gInv k l * Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                calc
                  (∑ l : Idx,
                      gInv k l *
                        (∑ p : Idx,
                          (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                            Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))))
                      =
                    ∑ l : Idx, ∑ p : Idx,
                      (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                        (gInv k l * Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))) := by
                      refine Finset.sum_congr rfl fun l _ => ?_
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun p _ => ?_
                      ring
                  _ =
                    ∑ p : Idx, ∑ l : Idx,
                      (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                        (gInv k l * Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))) := by
                      rw [Finset.sum_comm]
            _ =
              ∑ p : Idx, ∑ k : Idx, ∑ l : Idx,
                (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                  (gInv k l * Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))) := by
                rw [Finset.sum_comm]
            _ =
              ∑ p : Idx,
                (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                  (∑ k : Idx, ∑ l : Idx,
                    gInv k l * Rm04 (vec4 (basis k) (basis a) (basis l) (basis p))) := by
                refine Finset.sum_congr rfl fun p _ => ?_
                simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ =
      -∑ p : Idx,
        (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
          (-A (vec2 (basis a) (basis p))) := by
          refine congrArg Neg.neg ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [rm04_trace_first_third_eq_neg_ricci
            (I := I) basis Rm04 gInv A hTrace hOutput hFirst hA hInv a p]
    _ =
      ∑ p : Idx,
        (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
          A (vec2 (basis p) (basis a)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hA a p]
          ring
    _ = ricciQuadraticAt (I := I) basis gInv A a b := by
          unfold ricciQuadraticAt oneUp02CompAt
          calc
            (∑ p : Idx,
              (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
                A (vec2 (basis p) (basis a)))
                =
              ∑ p : Idx, ∑ q : Idx,
                gInv p q * A (vec2 (basis b) (basis q)) *
                  A (vec2 (basis p) (basis a)) := by
                  simp [Finset.sum_mul, mul_assoc]
            _ =
              ∑ q : Idx, ∑ p : Idx,
                gInv p q * A (vec2 (basis b) (basis q)) *
                  A (vec2 (basis p) (basis a)) := by
                  rw [Finset.sum_comm]
            _ =
              ∑ p : Idx, ∑ q : Idx,
                gInv p q * A (vec2 (basis a) (basis q)) *
                  A (vec2 (basis p) (basis b)) := by
                  refine Finset.sum_congr rfl fun p _ => ?_
                  refine Finset.sum_congr rfl fun q _ => ?_
                  rw [hInv q p, hA b p, hA q a]
                  ring
            _ =
              ∑ p : Idx,
                (∑ q : Idx, gInv p q * A (vec2 (basis a) (basis q))) *
                  A (vec2 (basis p) (basis b)) := by
                  simp [Finset.sum_mul, mul_assoc]



omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
private theorem contracted_slot0_eq_neg_rm04RicciContraction
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 (vec4 W X Y Z) = Rm04 (vec4 Y Z W X))
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (_hFirst : FirstBianchiAt (I := I) Rm04)
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (_hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    (∑ k : Idx, ∑ l : Idx,
        gInv k l *
          (∑ p : Idx,
            (∑ q : Idx, gInv p q * A (vec2 (basis q) (basis l))) *
              Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)))) =
      -rm04RicciContractionAt (I := I) basis Rm04 gInv A a b := by
  classical
  let B : Idx -> Idx -> Real :=
    fun r s => raised02CompAt (I := I) basis gInv A r s
  have hInput : forall X Y Z W : TangentSpace I x,
      Rm04 (vec4 X Y Z W) = -Rm04 (vec4 Y X Z W) := by
    intro X Y Z W
    calc
      Rm04 (vec4 X Y Z W) = Rm04 (vec4 Z W X Y) := hPair X Y Z W
      _ = -Rm04 (vec4 Z W Y X) := hOutput Z W X Y
      _ = -Rm04 (vec4 Y X Z W) := by rw [hPair Z W Y X]
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv k l *
          (∑ p : Idx,
            (∑ q : Idx, gInv p q * A (vec2 (basis q) (basis l))) *
              Rm04 (vec4 (basis k) (basis a) (basis b) (basis p))))
        =
      ∑ k : Idx, ∑ p : Idx,
        (∑ l : Idx, ∑ q : Idx,
          gInv k l * gInv p q * A (vec2 (basis q) (basis l))) *
          Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
          calc
            (∑ k : Idx, ∑ l : Idx,
                gInv k l *
                  (∑ p : Idx,
                    (∑ q : Idx, gInv p q * A (vec2 (basis q) (basis l))) *
                      Rm04 (vec4 (basis k) (basis a) (basis b) (basis p))))
                =
              ∑ k : Idx, ∑ l : Idx, ∑ p : Idx, ∑ q : Idx,
                gInv k l * gInv p q * A (vec2 (basis q) (basis l)) *
                  Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => ?_
                simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            _ =
              ∑ k : Idx, ∑ p : Idx, ∑ l : Idx, ∑ q : Idx,
                gInv k l * gInv p q * A (vec2 (basis q) (basis l)) *
                  Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Finset.sum_comm]
            _ =
              ∑ k : Idx, ∑ p : Idx,
                (∑ l : Idx, ∑ q : Idx,
                  gInv k l * gInv p q * A (vec2 (basis q) (basis l))) *
                  Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                refine Finset.sum_congr rfl fun p _ => ?_
                simp [Finset.sum_mul, mul_assoc]
    _ =
      ∑ k : Idx, ∑ p : Idx,
        B k p * Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          congr 1
          dsimp [B, raised02CompAt]
          refine Finset.sum_congr rfl fun l _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hA q l]
    _ =
      ∑ k : Idx, ∑ p : Idx,
        B k p * (-Rm04 (vec4 (basis a) (basis k) (basis b) (basis p))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hInput (basis k) (basis a) (basis b) (basis p)]
    _ =
      -∑ k : Idx, ∑ p : Idx,
        B k p * Rm04 (vec4 (basis a) (basis k) (basis b) (basis p)) := by
          simp [Finset.sum_neg_distrib, mul_neg]
    _ = -rm04RicciContractionAt (I := I) basis Rm04 gInv A a b := by
          dsimp [B]
          simp [rm04RicciContractionAt, mul_comm]




omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
theorem metricTrace_rm04RicciContractionAt_eq_neg_inner
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hTrace : RicciRealizesRm04FirstTraceAt (I := I) A Rm04 gInv basis)
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (hFirst : FirstBianchiAt (I := I) Rm04)
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i) :
    (∑ a : Idx, ∑ b : Idx,
      gInv a b * rm04RicciContractionAt (I := I) basis Rm04 gInv A a b) =
      -(∑ k : Idx, ∑ l : Idx,
        A (vec2 (basis k) (basis l)) *
          raised02CompAt (I := I) basis gInv A k l) := by
  classical
  calc
    (∑ a : Idx, ∑ b : Idx,
      gInv a b * rm04RicciContractionAt (I := I) basis Rm04 gInv A a b)
        =
      ∑ k : Idx, ∑ l : Idx,
        raised02CompAt (I := I) basis gInv A k l *
          (∑ a : Idx, ∑ b : Idx,
            gInv a b * Rm04 (vec4 (basis a) (basis k) (basis b) (basis l))) := by
        unfold rm04RicciContractionAt
        calc
          (∑ a : Idx, ∑ b : Idx,
            gInv a b *
              (∑ k : Idx, ∑ l : Idx,
                Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                  raised02CompAt (I := I) basis gInv A k l))
              =
            ∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
              gInv a b *
                (Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                  raised02CompAt (I := I) basis gInv A k l) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
          _ =
            ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
              raised02CompAt (I := I) basis gInv A k l *
                (gInv a b *
                  Rm04 (vec4 (basis a) (basis k) (basis b) (basis l))) := by
              calc
                (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
                  gInv a b *
                    (Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                      raised02CompAt (I := I) basis gInv A k l))
                    =
                  ∑ a : Idx, ∑ k : Idx, ∑ b : Idx, ∑ l : Idx,
                    gInv a b *
                      (Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                        raised02CompAt (I := I) basis gInv A k l) := by
                    refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_comm]
                _ =
                  ∑ k : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
                    gInv a b *
                      (Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                        raised02CompAt (I := I) basis gInv A k l) := by
                    rw [Finset.sum_comm]
                _ =
                  ∑ k : Idx, ∑ a : Idx, ∑ l : Idx, ∑ b : Idx,
                    gInv a b *
                      (Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                        raised02CompAt (I := I) basis gInv A k l) := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_comm]
                _ =
                  ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
                    gInv a b *
                      (Rm04 (vec4 (basis a) (basis k) (basis b) (basis l)) *
                        raised02CompAt (I := I) basis gInv A k l) := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    rw [Finset.sum_comm]
                _ =
                  ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
                    raised02CompAt (I := I) basis gInv A k l *
                      (gInv a b *
                        Rm04 (vec4 (basis a) (basis k) (basis b) (basis l))) := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    refine Finset.sum_congr rfl fun l _ => ?_
                    refine Finset.sum_congr rfl fun a _ => ?_
                    refine Finset.sum_congr rfl fun b _ => ?_
                    ring
          _ =
            ∑ k : Idx, ∑ l : Idx,
              raised02CompAt (I := I) basis gInv A k l *
                (∑ a : Idx, ∑ b : Idx,
                  gInv a b *
                    Rm04 (vec4 (basis a) (basis k) (basis b) (basis l))) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              simp [Finset.mul_sum]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        raised02CompAt (I := I) basis gInv A k l *
          (-A (vec2 (basis k) (basis l))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [rm04_trace_first_third_eq_neg_ricci
          (I := I) basis Rm04 gInv A hTrace hOutput hFirst hA hInv k l]
    _ =
      -(∑ k : Idx, ∑ l : Idx,
        A (vec2 (basis k) (basis l)) *
          raised02CompAt (I := I) basis gInv A k l) := by
        simp only [mul_neg, Finset.sum_neg_distrib, neg_inj]
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        ring








theorem contracted_curvatureAction0SAt_vec2_eq
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (A : Tensor02At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (hTrace : RicciRealizesRm04FirstTraceAt (I := I) A Rm04 gInv basis)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 (vec4 W X Y Z) = Rm04 (vec4 Y Z W X))
    (hOutput : Rm04OutputSkewAt (I := I) Rm04)
    (hFirst : FirstBianchiAt (I := I) Rm04)
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    (∑ k : Idx, ∑ l : Idx,
        gInv k l *
          curvatureAction0SAt (I := I) Rm13 A (basis k) (basis a)
            (vec2 (basis b) (basis l))) =
      rm04RicciContractionAt (I := I) basis Rm04 gInv A a b +
        ricciQuadraticAt (I := I) basis gInv A a b := by
  classical
  have hslot0 : forall k l : Idx,
      Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0)
          (vec3 (basis k) (basis a) (basis b)) =
        ∑ p : Idx,
          (∑ q : Idx, gInv p q * A (vec2 (basis q) (basis l))) *
            Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
    intro k l
    calc
      Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0)
          (vec3 (basis k) (basis a) (basis b))
          =
        ∑ p : Idx,
          (∑ q : Idx,
              gInv p q *
                oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0
                  (fun _ : Fin 1 => basis q)) *
            Rm13 x
              (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis p)))
              (vec3 (basis k) (basis a) (basis b)) := by
            exact rm13_oneForm_apply_eq_sum_inv_flat
              (I := I) g basis gInv hinv (Rm13 x)
              (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0)
              (basis k) (basis a) (basis b)
      _ =
        ∑ p : Idx,
          (∑ q : Idx, gInv p q * A (vec2 (basis q) (basis l))) *
            Rm04 (vec4 (basis k) (basis a) (basis b) (basis p)) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            have hcoeff :
                (∑ q : Idx,
                    gInv p q *
                      oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0
                        (fun _ : Fin 1 => basis q)) =
                  ∑ q : Idx, gInv p q * A (vec2 (basis q) (basis l)) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              have hupdate :
                  Function.update (vec2 (basis b) (basis l)) 0 (basis q) =
                    vec2 (basis q) (basis l) := by
                funext r
                fin_cases r <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
              simp [oneFormAtSlot0S_apply, hupdate]
            rw [hcoeff, (hLower (basis k) (basis a) (basis b) (basis p)).symm]
  have hslot1 : forall k l : Idx,
      Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1)
          (vec3 (basis k) (basis a) (basis l)) =
        ∑ p : Idx,
          (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
            Rm04 (vec4 (basis k) (basis a) (basis l) (basis p)) := by
    intro k l
    calc
      Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1)
          (vec3 (basis k) (basis a) (basis l))
          =
        ∑ p : Idx,
          (∑ q : Idx,
              gInv p q *
                oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1
                  (fun _ : Fin 1 => basis q)) *
            Rm13 x
              (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis p)))
              (vec3 (basis k) (basis a) (basis l)) := by
            exact rm13_oneForm_apply_eq_sum_inv_flat
              (I := I) g basis gInv hinv (Rm13 x)
              (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1)
              (basis k) (basis a) (basis l)
      _ =
        ∑ p : Idx,
          (∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q))) *
            Rm04 (vec4 (basis k) (basis a) (basis l) (basis p)) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            have hcoeff :
                (∑ q : Idx,
                    gInv p q *
                      oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1
                        (fun _ : Fin 1 => basis q)) =
                  ∑ q : Idx, gInv p q * A (vec2 (basis b) (basis q)) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              have hupdate :
                  Function.update (vec2 (basis b) (basis l)) 1 (basis q) =
                    vec2 (basis b) (basis q) := by
                funext r
                fin_cases r <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
              simp [oneFormAtSlot0S_apply, hupdate]
            rw [hcoeff, (hLower (basis k) (basis a) (basis l) (basis p)).symm]
  have hslot0_contracted :
      (∑ k : Idx, ∑ l : Idx,
        gInv k l *
          Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0)
            (vec3 (basis k) (basis a) (basis b))) =
        -rm04RicciContractionAt (I := I) basis Rm04 gInv A a b := by
    simp_rw [hslot0]
    exact contracted_slot0_eq_neg_rm04RicciContraction
      (I := I) basis Rm04 gInv A hPair hOutput hFirst hA hInv a b
  have hslot1_contracted :
      -(∑ k : Idx, ∑ l : Idx,
        gInv k l *
          Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1)
            (vec3 (basis k) (basis a) (basis l))) =
        ricciQuadraticAt (I := I) basis gInv A a b := by
    simp_rw [hslot1]
    exact contracted_slot1_eq_quadratic
      (I := I) basis Rm04 gInv A hTrace hPair hOutput hFirst hA hInv a b
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv k l *
          curvatureAction0SAt (I := I) Rm13 A (basis k) (basis a)
            (vec2 (basis b) (basis l)))
        =
      -(∑ k : Idx, ∑ l : Idx,
        gInv k l *
          Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 1)
            (vec3 (basis k) (basis a) (basis l))) -
      (∑ k : Idx, ∑ l : Idx,
        gInv k l *
          Rm13 x (oneFormAtSlot0S (I := I) A (vec2 (basis b) (basis l)) 0)
            (vec3 (basis k) (basis a) (basis b))) := by
          simp [curvatureAction0SAt, Fin.sum_univ_two, vec2,
            DifferentialGeometry.Integral.Connection.vec2, mul_add, sub_eq_add_neg,
            Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ =
      rm04RicciContractionAt (I := I) basis Rm04 gInv A a b +
        ricciQuadraticAt (I := I) basis gInv A a b := by
          rw [← hslot1_contracted, hslot0_contracted]
          ring


omit [FiniteDimensional ℝ E] [DecidableEq Idx] in
theorem curvature_ricci_rhs_symm
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) (M := M) x)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 (vec4 W X Y Z) = Rm04 (vec4 Y Z W X))
    (hA : forall i j : Idx, A (vec2 (basis i) (basis j)) =
      A (vec2 (basis j) (basis i)))
    (hInv : forall i j : Idx, gInv i j = gInv j i)
    (a b : Idx) :
    rm04RicciContractionAt (I := I) basis Rm04 gInv A a b +
        ricciQuadraticAt (I := I) basis gInv A a b =
      rm04RicciContractionAt (I := I) basis Rm04 gInv A b a +
        ricciQuadraticAt (I := I) basis gInv A b a := by
  rw [rm04RicciContractionAt_symm (I := I) basis Rm04 gInv A hPair hA hInv a b,
    ricciQuadraticAt_symm (I := I) basis gInv A hA hInv a b]

end DifferentialGeometry.Integral.Connection
