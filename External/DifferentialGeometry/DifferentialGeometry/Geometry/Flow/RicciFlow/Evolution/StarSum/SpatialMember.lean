import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.StarRouting
import DifferentialGeometry.Geometry.Curvature.CurvatureActionLower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem cotangentSharp_ortho_expand
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    cotangentSharp_gen (I := I) g x β =
      ∑ e : Idx, (β (fun _ : Fin 1 => basis e)) • basis e := by
  classical
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis
    (identityInvMetric (Idx := Idx)) hinv β]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul, cotangentToDual_apply_gen]
  · intro j _ hj
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hj h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor05_vec5_sum_last_idx
    {Idx : Type*} [Fintype Idx] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (A B C D : TangentSpace I x)
    (coef : Idx → Real) (vecs : Idx → TangentSpace I x) :
    T (vec5 (I := I) A B C D (∑ e : Idx, coef e • vecs e)) =
      ∑ e : Idx, coef e * T (vec5 (I := I) A B C D (vecs e)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec5 (I := I) A B C D Z =
        Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4 Z := by
    intro Z
    funext i
    fin_cases i <;> simp [vec5, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (∑ e : Idx, coef e • vecs e)) =
      T.toMultilinearMap (Function.update
        (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (∑ e : Idx, coef e • vecs e)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show T.toMultilinearMap (Function.update
        (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4 (coef e • vecs e)) =
      T (Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (coef e • vecs e)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor04_vec4_sum_last_idx
    {Idx : Type*} [Fintype Idx] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (A B C : TangentSpace I x)
    (coef : Idx → Real) (vecs : Idx → TangentSpace I x) :
    T (vec4 (I := I) A B C (∑ e : Idx, coef e • vecs e)) =
      ∑ e : Idx, coef e * T (vec4 (I := I) A B C (vecs e)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec4 (I := I) A B C Z =
        Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 Z := by
    intro Z
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Idx, coef e • vecs e)) =
      T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Idx, coef e • vecs e)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 (coef e • vecs e)) =
      T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (coef e • vecs e)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
private theorem slotdiffBasisEq
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Idx) (m : Fin (4 + k) → Idx) :
    nablaKRm04Field (I := I) S (t : Real) (k + 3) x
        (Fin.cons (basis a)
          (metricTraceInput (I := I) (basis b) (basis c)
            (fun i : Fin (4 + k) => basis (m i)))) -
      nablaKRm04Field (I := I) S (t : Real) (k + 3) x
        (Fin.cons (basis a)
          (metricTraceInput (I := I) (basis c) (basis b)
            (fun i : Fin (4 + k) => basis (m i)))) =
      -∑ q : Fin (4 + k),
        ((∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 1 x
              (vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) k x
              (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))) +
          (∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 0 x
              (vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) (k + 1) x
              (Fin.cons (basis a)
                (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))))) := by
  classical
  have hconn := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  obtain ⟨Xa, hXa, hXacov⟩ := TensorLieDeriv.exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x (basis a)
  obtain ⟨Vb, hVb, hVbcov⟩ := TensorLieDeriv.exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x (basis b)
  obtain ⟨Vc, hVc, hVccov⟩ := TensorLieDeriv.exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x (basis c)
  choose Vm hVm hVmcov using fun i : Fin (4 + k) =>
    TensorLieDeriv.exists_cov_zero_at_apply (I := I)
      (S.family.connection (t : Real)) hconn x (basis (m i))
  have hraw := nablaK_antisym_eq_rm04_raise_leibniz (I := I) S hS t k x Xa Vb Vc Vm
    (hVbcov Xa) (hVccov Xa) (fun i => hVmcov i Xa)
  have hq : ∀ q : Fin (4 + k),
      nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (Xa x) (Vb x) (Vc x) (Vm q x)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x
              (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x))) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (Vb x) (Vc x) (Vm q x)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
                (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x) (Xa x)))) =
        (∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 1 x
              (vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) k x
              (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))) +
          (∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 0 x
              (vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) (k + 1) x
              (Fin.cons (basis a)
                (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e)))) := by
    intro q
    have hsharpA := cotangentSharp_ortho_expand (I := I) (S.base.metric (t : Real))
      basis horth (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x)
    have hA :
        nablaRm04Field (I := I) S (t : Real) x
            (vec5 (I := I) (Xa x) (Vb x) (Vc x) (Vm q x)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x
                (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x))) =
          ∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 1 x
              (vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) k x
              (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e)) := by
      rw [hsharpA, tensor05_vec5_sum_last_idx]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [nablaKRmFrozenSlotField_apply_vec (I := I) S (t : Real) k q Vm x (basis e)]
      rw [hXa, hVb, hVc, hVm q]
      have hslot :
          Function.update (fun i : Fin (4 + k) => Vm i x) q (basis e) =
            Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e) := by
        funext p
        by_cases hp : p = q
        · subst hp
          simp [Function.update]
        · simp [Function.update, hp, hVm p]
      rw [hslot]
      change
        nablaKRm04Field (I := I) S (t : Real) k x
            (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e)) *
          nablaKRm04Field (I := I) S (t : Real) 1 x
            (vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e)) =
        nablaKRm04Field (I := I) S (t : Real) 1 x
            (vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e)) *
          nablaKRm04Field (I := I) S (t : Real) k x
            (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))
      ring
    have hsharpB := cotangentSharp_ortho_expand (I := I) (S.base.metric (t : Real))
      basis horth
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
        (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x) (Xa x))
    have hB :
        S.base.rm04 (t : Real) x
            (vec4 (I := I) (Vb x) (Vc x) (Vm q x)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
                  (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x) (Xa x)))) =
          ∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 0 x
              (vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) (k + 1) x
              (Fin.cons (basis a)
                (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))) := by
      rw [hsharpB, tensor04_vec4_sum_last_idx]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [tensor0S_curry_apply_cons]
      have hvec :
          (Fin.cons (Xa x) (fun _ : Fin 1 => basis e) : Fin 2 → TangentSpace I x) =
            vec2 (I := I) (Xa x) (basis e) := by
        funext p
        fin_cases p <;> rfl
      rw [hvec, nablaKRmFrozenSlot_eval (I := I) S hS t k q Xa Vm x
        (fun i _ => hVmcov i Xa) (basis e)]
      rw [hVb, hVc, hVm q, hXa]
      have hslot :
          Function.update (fun i : Fin (4 + k) => Vm i x) q (basis e) =
            Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e) := by
        funext p
        by_cases hp : p = q
        · subst hp
          simp [Function.update]
        · simp [Function.update, hp, hVm p]
      rw [hslot]
      change
        nablaKRm04Field (I := I) S (t : Real) (k + 1) x
            (Fin.cons (basis a)
              (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))) *
          nablaKRm04Field (I := I) S (t : Real) 0 x
            (vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e)) =
        nablaKRm04Field (I := I) S (t : Real) 0 x
            (vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e)) *
          nablaKRm04Field (I := I) S (t : Real) (k + 1) x
            (Fin.cons (basis a)
              (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e)))
      ring
    rw [hA, hB]
  calc
    nablaKRm04Field (I := I) S (t : Real) (k + 3) x
          (Fin.cons (basis a)
            (metricTraceInput (I := I) (basis b) (basis c)
              (fun i : Fin (4 + k) => basis (m i)))) -
        nablaKRm04Field (I := I) S (t : Real) (k + 3) x
          (Fin.cons (basis a)
            (metricTraceInput (I := I) (basis c) (basis b)
              (fun i : Fin (4 + k) => basis (m i)))) =
        -∑ q : Fin (4 + k),
          (nablaRm04Field (I := I) S (t : Real) x
              (vec5 (I := I) (Xa x) (Vb x) (Vc x) (Vm q x)
                (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x
                  (nablaKRmFrozenSlotField (I := I) S (t : Real) k q Vm x))) +
            S.base.rm04 (t : Real) x
              (vec4 (I := I) (Vb x) (Vc x) (Vm q x)
                (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x
                  (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
                    (nablaKRmNablaFrozenSlotField (I := I) S (t : Real) k q Vm x) (Xa x))))) := by
          simpa [hXa, hVb, hVc, hVm] using hraw
    _ = -∑ q : Fin (4 + k),
        ((∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 1 x
              (vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) k x
              (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))) +
          (∑ e : Idx,
            nablaKRm04Field (I := I) S (t : Real) 0 x
              (vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e)) *
            nablaKRm04Field (I := I) S (t : Real) (k + 1) x
              (Fin.cons (basis a)
                (Function.update (fun i : Fin (4 + k) => basis (m i)) q (basis e))))) := by
          congr 1
          exact Finset.sum_congr rfl (fun q _ => hq q)







omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
private theorem curvactReduce
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, (S.base.metric t).inner x (basis i) (basis j)
        = if i = j then (1 : Real) else 0)
    (I0 : Fin (4 + (k + 1)) → Idx) :
    ∑ i : Idx, curvatureAction0SAt (I := I) (S.base.rm13 t)
        (nablaKRm04Field (I := I) S t (k + 1) x) (basis i) (basis (I0 0))
        (Fin.cons (basis i) (fun p : Fin (4 + k) => basis (I0 p.succ)))
      = -∑ q : Fin (4 + (k + 1)), ∑ p : Idx, ∑ i : Idx,
          nablaKRm04Field (I := I) S t (k + 1) x
              (Function.update
                (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
                  (fun l : Fin (4 + k) => basis (I0 l.succ))) q (basis p))
            * nablaKRm04Field (I := I) S t 0 x
              (vec4 (I := I) (basis i) (basis (I0 0))
                (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
                  (fun l : Fin (4 + k) => basis (I0 l.succ)) q) (basis p)) := by
  classical
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric t) x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) (S.base.metric t) basis horth
  have hcompi : ∀ i : Idx,
      curvatureAction0SAt (I := I) (S.base.rm13 t)
          (nablaKRm04Field (I := I) S t (k + 1) x) (basis i) (basis (I0 0))
          (Fin.cons (basis i) (fun l : Fin (4 + k) => basis (I0 l.succ)))
        = -∑ q : Fin (4 + (k + 1)), ∑ p : Idx,
            nablaKRm04Field (I := I) S t (k + 1) x
                (Function.update
                  (Fin.cons (basis i) (fun l : Fin (4 + k) => basis (I0 l.succ))) q (basis p))
              * nablaKRm04Field (I := I) S t 0 x
                (vec4 (I := I) (basis i) (basis (I0 0))
                  (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
                    (fun l : Fin (4 + k) => basis (I0 l.succ)) q) (basis p)) := by
    intro i
    rw [curvatureAction0SAt_eq_rm04 (I := I) (S.base.metric t) basis
      (identityInvMetric (Idx := Idx)) hinv (S.base.rm13 t) (S.base.rm04 t x)
      (solution_rm04LowersRm13At (I := I) S t x)
      (nablaKRm04Field (I := I) S t (k + 1) x) (basis i) (basis (I0 0))
      (Fin.cons (basis i) (fun l : Fin (4 + k) => basis (I0 l.succ)))]
    congr 1
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    congr 1
    rw [Finset.sum_eq_single p]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro r _ hr
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hr h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [Finset.sum_congr rfl fun i _ => hcompi i]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
private theorem slotdiffReduce
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (I0 : Fin (4 + (k + 1)) → Idx) :
    ∑ i : Idx,
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x
            (metricTraceInput (I := I) (basis i) (basis i)
              (Fin.cons (basis (I0 0))
                (fun l : Fin (4 + k) => basis (I0 l.succ)))) -
          nablaKRm04Field (I := I) S (t : Real) (k + 3) x
            (metricTraceInput (I := I) (basis i) (basis (I0 0))
              (Fin.cons (basis i)
                (fun l : Fin (4 + k) => basis (I0 l.succ))))) =
      -∑ q : Fin (4 + k),
        (starBaseField (I := I) S (t : Real) (k + 1) 1 k 0 (sigmaDiffA k q) x
            (fun p => basis (I0 p)) +
          starBaseField (I := I) S (t : Real) (k + 1) 0 (k + 1) 0 (sigmaDiffB k q) x
            (fun p => basis (I0 p))) := by
  classical
  have horth' : ∀ i j : Idx,
      (S.family.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    simpa using horth
  have hterm : ∀ i : Idx,
      (nablaKRm04Field (I := I) S (t : Real) (k + 3) x
          (metricTraceInput (I := I) (basis i) (basis i)
            (Fin.cons (basis (I0 0))
              (fun l : Fin (4 + k) => basis (I0 l.succ)))) -
        nablaKRm04Field (I := I) S (t : Real) (k + 3) x
          (metricTraceInput (I := I) (basis i) (basis (I0 0))
            (Fin.cons (basis i)
              (fun l : Fin (4 + k) => basis (I0 l.succ))))) =
        -∑ q : Fin (4 + k),
          ((∑ e : Idx,
              nablaKRm04Field (I := I) S (t : Real) 1 x
                (vec5 (I := I) (basis i) (basis i) (basis (I0 0)) (basis (I0 q.succ))
                  (basis e)) *
              nablaKRm04Field (I := I) S (t : Real) k x
                (Function.update (fun l : Fin (4 + k) => basis (I0 l.succ)) q
                  (basis e))) +
            (∑ e : Idx,
              nablaKRm04Field (I := I) S (t : Real) 0 x
                (vec4 (I := I) (basis i) (basis (I0 0)) (basis (I0 q.succ)) (basis e)) *
              nablaKRm04Field (I := I) S (t : Real) (k + 1) x
                (Fin.cons (basis i)
                  (Function.update (fun l : Fin (4 + k) => basis (I0 l.succ)) q
                    (basis e))))) := by
    intro i
    simpa [metricTraceInput] using
      (slotdiffBasisEq (I := I) S hS t k basis horth i i (I0 0)
        (fun q : Fin (4 + k) => I0 q.succ))
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    rw [← slotdiffStarA (I := I) S (t : Real) k q basis horth' I0]
  · rw [Finset.sum_comm]
    rw [← slotdiffStarB (I := I) S (t : Real) k q basis horth' I0]

private theorem sumDiag {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (X : Idx → Idx → Real) :
    (∑ i : Idx, ∑ j : Idx, identityInvMetric (Idx := Idx) i j * X i j)
      = ∑ i : Idx, X i i := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul]
  · intro j _ hj
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
private theorem curvRoute
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (I0 : Fin (4 + (k + 1)) → Idx) :
    ∑ i : Idx, curvatureAction0SAt (I := I) (S.base.rm13 t)
        (nablaKRm04Field (I := I) S t (k + 1) x) (basis i) (basis (I0 0))
        (Fin.cons (basis i) (fun l : Fin (4 + k) => basis (I0 l.succ)))
      =
      -∑ q : Fin (4 + (k + 1)),
        (if hq : q.val = 0 then
          starBaseField (I := I) S t (k + 1) (k + 1) 0 0 (sigmaCurv0 k) x
            (fun p => basis (I0 p))
        else
          starBaseField (I := I) S t (k + 1) (k + 1) 0 0 (sigmaCurvPos k q hq) x
            (fun p => basis (I0 p))) := by
  classical
  have horth' : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    simpa using horth
  rw [curvactReduce (I := I) S t k basis horth I0]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q.val = 0
  · have hq0 : q = 0 := Fin.ext hq
    subst q
    rw [dif_pos (by simp)]
    simpa using (curvactStar0 (I := I) S t k basis horth' I0).symm
  · rw [dif_neg hq]
    simpa using (curvactStarPos (I := I) S t k q hq basis horth' I0).symm










def commStarCost (n k : ℕ) : Real :=
  (n : Real) ^ 2 * (13 + 3 * k)

set_option backward.isDefEq.respectTransparency false in


omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem spatialCommStarSum
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + (k + 1)),
      StarSum2Cost (I := I) Idx S (t : Real) (k + 1) T
          (commStarCost (Fintype.card Idx) k) ∧
      ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x))
        (gInv : Idx → Idx → Real)
        (_hinv : MetricInverseInBasis_gen (I := I) (M := M)
          (S.base.metric (t : Real)) x basis gInv)
        (_horth : ∀ i j : Idx, (S.base.metric (t : Real)).inner x (basis i) (basis j)
            = if i = j then (1 : Real) else 0)
        (I0 : Fin (4 + (k + 1)) → Idx),
        metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 3) x) (fun p => basis (I0 p))
            - totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                (4 + k) (S.family.connection (t : Real))
                (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 2))) x (fun p => basis (I0 p))
          = tensor0SComponent (I := I) (T x) (fun i => basis i) I0 := by
  classical
  let TA :=
    (∑ q : Fin (4 + k),
      starBaseField (I := I) S (t : Real) (k + 1) 1 k 0 (sigmaDiffA k q))
  let TB :=
    (∑ q : Fin (4 + k),
      starBaseField (I := I) S (t : Real) (k + 1) 0 (k + 1) 0 (sigmaDiffB k q))
  let TC :=
    (∑ q : Fin (4 + (k + 1)),
      if hq : q.val = 0 then
        starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0 (sigmaCurv0 k)
      else
        starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0
          (sigmaCurvPos k q hq))
  let T := (-1 : Real) • (TA + TB + TC)
  refine ⟨T, ?_, ?_⟩
  · have hTA : StarSum2Cost (I := I) Idx S (t : Real) (k + 1) TA
        (∑ _q : Fin (4 + k), (Fintype.card Idx : Real) ^ 2) := by
      dsimp [TA]
      refine starSum2Cost_sum (I := I) (Idx := Idx) (S := S) (t := (t : Real))
        (Finset.univ : Finset (Fin (4 + k)))
        (fun q => starBaseField (I := I) S (t : Real) (k + 1) 1 k 0 (sigmaDiffA k q))
        (fun _q => (Fintype.card Idx : Real) ^ 2)
        ?_
      intro q _
      exact StarSum2Cost.base (I := I) (Idx := Idx) (S := S) (t := (t : Real))
        (k + 1) 1 k 0
        (sigmaDiffA k q)
    have hTB : StarSum2Cost (I := I) Idx S (t : Real) (k + 1) TB
        (∑ _q : Fin (4 + k), (Fintype.card Idx : Real) ^ 2) := by
      dsimp [TB]
      refine starSum2Cost_sum (I := I) (Idx := Idx) (S := S) (t := (t : Real))
        (Finset.univ : Finset (Fin (4 + k)))
        (fun q => starBaseField (I := I) S (t : Real) (k + 1) 0 (k + 1) 0
          (sigmaDiffB k q))
        (fun _q => (Fintype.card Idx : Real) ^ 2) ?_
      intro q _
      exact StarSum2Cost.base (I := I) (Idx := Idx) (S := S) (t := (t : Real))
        (k + 1) 0 (k + 1) 0
        (sigmaDiffB k q)
    have hTC : StarSum2Cost (I := I) Idx S (t : Real) (k + 1) TC
        (∑ _q : Fin (4 + (k + 1)), (Fintype.card Idx : Real) ^ 2) := by
      dsimp [TC]
      refine starSum2Cost_sum (I := I) (Idx := Idx) (S := S) (t := (t : Real))
        (Finset.univ : Finset (Fin (4 + (k + 1))))
        (fun q =>
          if hq : q.val = 0 then
            starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0 (sigmaCurv0 k)
          else
            starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0
              (sigmaCurvPos k q hq))
        (fun _q => (Fintype.card Idx : Real) ^ 2) ?_
      intro q _
      by_cases hq : q.val = 0
      · simpa [hq] using
          (StarSum2Cost.base (I := I) (Idx := Idx) (S := S) (t := (t : Real))
            (k + 1) (k + 1) 0 0
            (sigmaCurv0 k))
      · simpa [hq] using
          (StarSum2Cost.base (I := I) (Idx := Idx) (S := S) (t := (t : Real))
            (k + 1) (k + 1) 0 0
            (sigmaCurvPos k q hq))
    convert StarSum2Cost.smul (I := I) (Idx := Idx) (S := S) (t := (t : Real)) (-1)
      (StarSum2Cost.add (StarSum2Cost.add hTA hTB) hTC) using 1
    simp only [abs_neg, abs_one, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, commStarCost]
    push_cast
    ring
  · intro x basis _gInv _hinv horth I0
    let tail : Fin (4 + k) → TangentSpace I x := fun p => basis (I0 p.succ)
    have hinvId : MetricInverseInBasis_gen (I := I) (M := M)
        (S.base.metric (t : Real)) x basis (identityInvMetric (Idx := Idx)) :=
      metricInverseInBasis_identity_of_orthonormal (I := I) (S.base.metric (t : Real)) basis horth
    have hslots :
        (fun p : Fin (4 + (k + 1)) => basis (I0 p)) =
          Fin.cons (basis (I0 0)) tail := by
      funext p
      refine Fin.cases ?_ (fun q => ?_) p <;> rfl
    have hslots' :
        (fun p : Fin (4 + k + 1) => basis (I0 p)) =
          Fin.cons (basis (I0 0)) tail := by
      funext p
      refine Fin.cases ?_ (fun q => ?_) p <;> rfl
    have hTAp :
        (TA x) (fun p => basis (I0 p)) =
          ∑ q : Fin (4 + k),
            (starBaseField (I := I) S (t : Real) (k + 1) 1 k 0 (sigmaDiffA k q) x)
              (fun p => basis (I0 p)) := by
      dsimp [TA]
      let Sset : Finset (Fin (4 + k)) := Finset.univ
      change (((∑ q ∈ Sset,
          starBaseField (I := I) S (t : Real) (k + 1) 1 k 0 (sigmaDiffA k q)) :
          Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (4 + (k + 1))) x) (fun p => basis (I0 p)) =
        ∑ q ∈ Sset,
          (starBaseField (I := I) S (t : Real) (k + 1) 1 k 0 (sigmaDiffA k q) x)
            (fun p => basis (I0 p))
      induction Sset using Finset.induction_on with
      | empty =>
          simp
      | insert a Sset ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp [ih]
    have hTBp :
        (TB x) (fun p => basis (I0 p)) =
          ∑ q : Fin (4 + k),
            (starBaseField (I := I) S (t : Real) (k + 1) 0 (k + 1) 0 (sigmaDiffB k q) x)
              (fun p => basis (I0 p)) := by
      dsimp [TB]
      let Sset : Finset (Fin (4 + k)) := Finset.univ
      change (((∑ q ∈ Sset,
          starBaseField (I := I) S (t : Real) (k + 1) 0 (k + 1) 0 (sigmaDiffB k q)) :
          Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (4 + (k + 1))) x) (fun p => basis (I0 p)) =
        ∑ q ∈ Sset,
          (starBaseField (I := I) S (t : Real) (k + 1) 0 (k + 1) 0 (sigmaDiffB k q) x)
            (fun p => basis (I0 p))
      induction Sset using Finset.induction_on with
      | empty =>
          simp
      | insert a Sset ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp [ih]
    have hTCp :
        (TC x) (fun p => basis (I0 p)) =
          ∑ q : Fin (4 + (k + 1)),
            (if hq : q.val = 0 then
              (starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0 (sigmaCurv0 k) x)
                (fun p => basis (I0 p))
            else
              (starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0
                (sigmaCurvPos k q hq) x) (fun p => basis (I0 p))) := by
      dsimp [TC]
      let Sset : Finset (Fin (4 + (k + 1))) := Finset.univ
      change (((∑ q ∈ Sset,
          if hq : q.val = 0 then
            starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0 (sigmaCurv0 k)
          else
            starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0
              (sigmaCurvPos k q hq)) :
          Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (4 + (k + 1))) x) (fun p => basis (I0 p)) =
        ∑ q ∈ Sset,
          (if hq : q.val = 0 then
            (starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0 (sigmaCurv0 k) x)
              (fun p => basis (I0 p))
          else
            (starBaseField (I := I) S (t : Real) (k + 1) (k + 1) 0 0
              (sigmaCurvPos k q hq) x) (fun p => basis (I0 p)))
      induction Sset using Finset.induction_on with
      | empty =>
          simp
      | insert a Sset ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
          rw [ih]
          by_cases ha0 : a.val = 0 <;> simp [ha0]
    have hsplit :
        metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 3) x) (fun p => basis (I0 p))
            - totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                (4 + k) (S.family.connection (t : Real))
                (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
                  (nablaKRm04Field (I := I) S (t : Real) (k + 2))) x
                (fun p => basis (I0 p))
          =
          ∑ i : Idx,
            ((nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) (basis i)
                  (Fin.cons (basis (I0 0))
                    (fun l : Fin (4 + k) => basis (I0 l.succ)))) -
              nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) (basis (I0 0))
                  (Fin.cons (basis i)
                    (fun l : Fin (4 + k) => basis (I0 l.succ))))) +
              curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
                (nablaKRm04Field (I := I) S (t : Real) (k + 1) x)
                (basis i) (basis (I0 0))
                (Fin.cons (basis i) (fun l : Fin (4 + k) => basis (I0 l.succ)))) := by
      have hraw := spatialComm_nablaKRm_split (I := I) S hS t k basis
        (identityInvMetric (Idx := Idx)) hinvId (basis (I0 0)) tail
      rw [sumDiag] at hraw
      simpa [tail, hslots, hslots'] using hraw
    rw [hsplit]
    rw [Finset.sum_add_distrib]
    rw [slotdiffReduce (I := I) S hS t k basis horth I0]
    rw [curvRoute (I := I) S (t : Real) k basis horth I0]
    simp [T, tensor0SComponent_apply, hTAp, hTBp, hTCp, Finset.sum_add_distrib]
    ring_nf

end DifferentialGeometry.PDE.RicciFlow
