import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
























noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]





noncomputable def covDerivOfField
    (gRef : SmoothRiemannianMetric I M)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    A0
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)


omit [SigmaCompactSpace M] in
theorem covDerivOfField_succ
    (gRef : SmoothRiemannianMetric I M)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef A0 (a + 1)
      = metricCovDerivStep (I := I) gRef a (covDerivOfField (I := I) gRef A0 a) :=
  rfl


omit [SigmaCompactSpace M] in
theorem metricCovDeriv_succ
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) h gRef (a + 1)
      = metricCovDerivStep (I := I) gRef a (metricCovDeriv (I := I) h gRef a) :=
  rfl



omit [SigmaCompactSpace M] in
theorem metricCovDeriv_eq_covDerivOfField
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) h gRef a
      = covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) h) a :=
  rfl



omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_apply
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (x : M) :
    metricCovDerivStep (I := I) gRef a A x
      = Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 2)
          (leviCivitaConnectionOfMetric (I := I) gRef) A x :=
  rfl







omit [SigmaCompactSpace M] in
theorem metricCovDeriv_succ_eval_smooth_slots_gen
    (h gRef : SmoothRiemannianMetric I M) (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin (a + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => metricCovDeriv (I := I) h gRef a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          metricCovDeriv (I := I) h gRef a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [metricCovDeriv_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V
    (metricCovDeriv (I := I) h gRef a) x


omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a (c • A)
      = c • metricCovDerivStep (I := I) gRef a A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    metricCovDerivStep_apply, Tensor0SBundle.totalNabla0SFun_smul]


omit [SigmaCompactSpace M] in
theorem covDerivOfField_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (c • A0) a
      = c • covDerivOfField (I := I) gRef A0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [covDerivOfField_succ, covDerivOfField_succ, ih, metricCovDerivStep_smul]


omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_add
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A B :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a (A + B)
      = metricCovDerivStep (I := I) gRef a A + metricCovDerivStep (I := I) gRef a B := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, ContMDiffSection.coe_add, Pi.add_apply,
    metricCovDerivStep_apply, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_add]


omit [SigmaCompactSpace M] in
theorem covDerivOfField_add
    (gRef : SmoothRiemannianMetric I M)
    (A0 B0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (A0 + B0) a
      = covDerivOfField (I := I) gRef A0 a + covDerivOfField (I := I) gRef B0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [covDerivOfField_succ, covDerivOfField_succ, covDerivOfField_succ, ih,
        metricCovDerivStep_add]



omit [SigmaCompactSpace M] in
theorem covDerivOfField_sub
    (gRef : SmoothRiemannianMetric I M)
    (A0 B0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (A0 - B0) a
      = covDerivOfField (I := I) gRef A0 a - covDerivOfField (I := I) gRef B0 a := by
  rw [sub_eq_add_neg, covDerivOfField_add, ← neg_one_smul Real B0,
    covDerivOfField_smul, neg_one_smul, ← sub_eq_add_neg]






noncomputable def covStep
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) s cov hcov A
  exact
    Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A hreg


omit [SigmaCompactSpace M] in
@[simp] theorem covStep_apply
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    covStep (I := I) gRef s A x
      = Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) s
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          A x :=
  rfl


omit [SigmaCompactSpace M] in
theorem covStep_add
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A B : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (A + B)
      = covStep (I := I) gRef s A + covStep (I := I) gRef s B := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, ContMDiffSection.coe_add, Pi.add_apply,
    covStep_apply, covStep_apply, Tensor0SBundle.totalNabla0SFun_add]





noncomputable def iterCov
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (r + a) :=
  Nat.rec A0 (fun a A => covStep (I := I) gRef (r + a) A)


omit [SigmaCompactSpace M] in
theorem iterCov_succ
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r A0 (a + 1)
      = covStep (I := I) gRef (r + a) (iterCov (I := I) gRef r A0 a) :=
  rfl


omit [SigmaCompactSpace M] in
theorem iterCov_add
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 B0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r (A0 + B0) a
      = iterCov (I := I) gRef r A0 a + iterCov (I := I) gRef r B0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [iterCov_succ, iterCov_succ, iterCov_succ, ih, covStep_add]





noncomputable def diffStep
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  covStep (I := I) g₁ s S - covStep (I := I) g₂ s S





noncomputable def telescAccum
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    (N : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (r + N)
  | 0 => 0
  | (N + 1) =>
      covStep (I := I) g₁ (r + N) (telescAccum g₁ g₂ r T N)
        + diffStep (I := I) g₁ g₂ (r + N) (iterCov (I := I) g₂ r T N)




omit [SigmaCompactSpace M] in
theorem iterCov_telescoping
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (N : Nat) :
    iterCov (I := I) g₁ r T N
      = iterCov (I := I) g₂ r T N + telescAccum (I := I) g₁ g₂ r T N := by
  induction N with
  | zero => exact (add_zero T).symm
  | succ n ih =>
      rw [iterCov_succ, ih, covStep_add, iterCov_succ (gRef := g₂)]
      simp only [telescAccum, diffStep]
      abel

end HCGCompactness

end DifferentialGeometry
