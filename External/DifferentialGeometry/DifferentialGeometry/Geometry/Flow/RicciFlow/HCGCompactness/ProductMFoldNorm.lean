import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTower
import DifferentialGeometry.Tensor.RSTensor.ProductNablaLeibniz
import DifferentialGeometry.Tensor.RSTensor.NormSqProduct
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContrNorm
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Components
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
























noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow (iterCov_realizes)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M]





omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem covStep_domDomCongr [FiniteDimensional Real E] {s s' : ℕ}
    (gRef : SmoothRiemannianMetric I M)
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s'
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e Z) =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (frontExtendEquiv e)
        (covStep (I := I) gRef s Z) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, totalNabla0SFun_domDomCongr]
  change _ = ContinuousMultilinearMap.domDomCongr (frontExtendEquiv e)
    ((covStep (I := I) gRef s Z) x)
  rw [covStep_apply]







omit [Module.Finite ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [I.Boundaryless] in
theorem totalNabla0SRealizes_unique {s : ℕ}
    [FiniteDimensional Real E]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {n1 n2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov α n1)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov α n2) :
    n1 = n2 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  obtain ⟨X, hX⟩ :
      ∃ X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _), X x = v 0 :=
    ⟨(ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v 0)).choose,
      (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v 0)).choose_spec⟩
  have hcons : Fin.cons (X x) (Fin.tail v) = v := by rw [hX]; exact Fin.cons_self_tail v
  have e1 := h1 X x (Fin.tail v)
  have e2 := h2 X x (Fin.tail v)
  rw [hcons] at e1 e2
  rw [e1, e2]




def shiftEquiv (r : ℕ) : (m : ℕ) → Fin ((r + 1) + m) ≃ Fin (r + (m + 1))
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (shiftEquiv r m)





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iterCov_shift [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) (m : ℕ) :
    iterCov (I := I) gRef r T (m + 1) =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (shiftEquiv r m)
        (iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m) := by
  induction m with
  | zero =>
      simp only [shiftEquiv]
      rfl
  | succ m ih =>
      simp only [shiftEquiv]
      rw [iterCov_succ, ih, covStep_domDomCongr, ← iterCov_succ]


def frontExtendIter {s s' : ℕ} (e : Fin s ≃ Fin s') : (m : ℕ) → Fin (s + m) ≃ Fin (s' + m)
  | 0 => e
  | (m + 1) => frontExtendEquiv (frontExtendIter e m)



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iterCov_domDomCongr [FiniteDimensional Real E] {s s' : ℕ}
    (gRef : SmoothRiemannianMetric I M)
    (e : Fin s ≃ Fin s')
    (Y : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (m : ℕ) :
    iterCov (I := I) gRef s'
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e Y) m =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (frontExtendIter e m)
        (iterCov (I := I) gRef s Y m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [frontExtendIter]
      rw [iterCov_succ, ih, covStep_domDomCongr, ← iterCov_succ]


omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem normSq0S_iterCov_domDomCongr [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) {s s' : ℕ} (e : Fin s ≃ Fin s')
    (Y : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (m : ℕ) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) gRef x basis (identityInvMetric (Idx := Idx))) :
    normSq0S (I := I) gRef x (s' + m)
        (iterCov (I := I) gRef s'
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) e Y) m x) =
      normSq0S (I := I) gRef x (s + m) (iterCov (I := I) gRef s Y m x) := by
  rw [iterCov_domDomCongr]
  change normSq0S (I := I) gRef x (s' + m)
      (ContinuousMultilinearMap.domDomCongr (frontExtendIter e m)
        ((iterCov (I := I) gRef s Y m) x)) = _
  exact normSq0S_domDomCongr (I := I) gRef x basis hinv (frontExtendIter e m)
    (iterCov (I := I) gRef s Y m x)



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem normSq0S_iterCov_shift [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) (m : ℕ) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) gRef x basis (identityInvMetric (Idx := Idx))) :
    normSq0S (I := I) gRef x (r + (m + 1)) (iterCov (I := I) gRef r T (m + 1) x) =
      normSq0S (I := I) gRef x ((r + 1) + m)
        (iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m x) := by
  rw [iterCov_shift]
  change normSq0S (I := I) gRef x (r + (m + 1))
      (ContinuousMultilinearMap.domDomCongr (shiftEquiv r m)
        ((iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m) x)) = _
  exact normSq0S_domDomCongr (I := I) gRef x basis hinv (shiftEquiv r m)
    (iterCov (I := I) gRef (r + 1) (covStep (I := I) gRef r T) m x)






omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iterCov_one [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) :
    iterCov (I := I) gRef r T 1 = covStep (I := I) gRef r T := rfl



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_product_one [FiniteDimensional Real E] {s q : ℕ}
    (gRef : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    iterCov (I := I) gRef (s + q)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) 1 =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := q)
            (iterCov (I := I) gRef s A 1) B)
        + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q + 1)
            A (iterCov (I := I) gRef q B 1)) :=
  totalNabla0SRealizes_unique
    (iterCov_realizes (I := I) gRef
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) 0)
    (nabla0S_product_realizes
      (leviCivitaConnectionOfMetric (I := I) gRef) A B
      (iterCov (I := I) gRef s A 1) (iterCov (I := I) gRef q B 1)
      (iterCov_realizes (I := I) gRef A 0) (iterCov_realizes (I := I) gRef B 0))




omit [Module.Finite ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] [IsManifold I 2 M] in
theorem sqrt_normSq0S_add_le [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) {s : ℕ} {x : M}
    (u v : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) gRef x basis (identityInvMetric (Idx := Idx))) :
    Real.sqrt (normSq0S (I := I) gRef x s (u + v)) ≤
      Real.sqrt (normSq0S (I := I) gRef x s u) + Real.sqrt (normSq0S (I := I) gRef x s v) := by
  rw [normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv]
  simp only [component0S_add]
  exact DifferentialGeometry.PDE.RicciFlow.compL2_add_le
    (component0S (I := I) basis u) (component0S (I := I) basis v)









omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_product_sqrtNormSq_le [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) gRef x basis (identityInvMetric (Idx := Idx)))
    (m : ℕ) : ∀ {s q : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q),
    Real.sqrt (normSq0S (I := I) gRef x ((s + q) + m)
        (iterCov (I := I) gRef (s + q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) m x)) ≤
      ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
        Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
        Real.sqrt (normSq0S (I := I) gRef x (q + (m - c)) (iterCov (I := I) gRef q B (m - c) x)) := by
  induction m with
  | zero =>
      intro s q A B
      rw [Finset.sum_range_one]
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.add_zero]
      have hnn : 0 ≤ normSq0S (I := I) gRef x s (A x) := by
        rw [normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      show Real.sqrt (normSq0S (I := I) gRef x (s + q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B x)) ≤
        Real.sqrt (normSq0S (I := I) gRef x s (A x)) *
          Real.sqrt (normSq0S (I := I) gRef x q (B x))
      rw [normSq0S_product (I := I) gRef x basis hinv A B, Real.sqrt_mul hnn]
  | succ m ih =>
      intro s q A B

      have hL : Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
          (iterCov (I := I) gRef (s + q + 1)
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
              (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := q)
                (iterCov (I := I) gRef s A 1) B)) m x)) ≤
          ∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) *
            Real.sqrt (normSq0S (I := I) gRef x (s + (c + 1)) (iterCov (I := I) gRef s A (c + 1) x)) *
            Real.sqrt (normSq0S (I := I) gRef x (q + (m - c)) (iterCov (I := I) gRef q B (m - c) x)) := by
        rw [normSq0S_iterCov_domDomCongr (I := I) gRef (leibnizLeftEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := q)
            (iterCov (I := I) gRef s A 1) B) m x basis hinv]
        refine le_trans (ih (iterCov (I := I) gRef s A 1) B) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [normSq0S_iterCov_shift (I := I) gRef A c x basis hinv, iterCov_one]

      have hR : Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
          (iterCov (I := I) gRef (s + q + 1)
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
              (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q + 1)
                A (iterCov (I := I) gRef q B 1))) m x)) ≤
          ∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) *
            Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
            Real.sqrt (normSq0S (I := I) gRef x (q + (m - c + 1)) (iterCov (I := I) gRef q B (m - c + 1) x)) := by
        rw [normSq0S_iterCov_domDomCongr (I := I) gRef (leibnizRightEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q + 1)
            A (iterCov (I := I) gRef q B 1)) m x basis hinv]
        refine le_trans (ih A (iterCov (I := I) gRef q B 1)) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [normSq0S_iterCov_shift (I := I) gRef B (m - c) x basis hinv, iterCov_one]

      calc Real.sqrt (normSq0S (I := I) gRef x ((s + q) + (m + 1))
              (iterCov (I := I) gRef (s + q)
                (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                  (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) (m + 1) x))
          = Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
              (iterCov (I := I) gRef (s + q + 1)
                (iterCov (I := I) gRef (s + q)
                  (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) 1) m x)) := by
            rw [normSq0S_iterCov_shift (I := I) gRef
              (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) m x basis hinv,
              ← iterCov_one]
        _ ≤ Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
                (iterCov (I := I) gRef (s + q + 1)
                  (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
                    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := q)
                      (iterCov (I := I) gRef s A 1) B)) m x)) +
              Real.sqrt (normSq0S (I := I) gRef x ((s + q + 1) + m)
                (iterCov (I := I) gRef (s + q + 1)
                  (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
                    (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
                    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
                      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q + 1)
                      A (iterCov (I := I) gRef q B 1))) m x)) := by
            rw [iterCov_product_one (I := I) gRef A B, iterCov_add]
            exact sqrt_normSq0S_add_le (I := I) gRef _ _ basis hinv
        _ ≤ _ := add_le_add hL hR
        _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : ℝ) *
              (Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
              Real.sqrt (normSq0S (I := I) gRef x (q + (m + 1 - c)) (iterCov (I := I) gRef q B (m + 1 - c) x))) := by
            rw [← pascal_sum m (fun c => Real.sqrt (normSq0S (I := I) gRef x (s + c)
                (iterCov (I := I) gRef s A c x)) *
              Real.sqrt (normSq0S (I := I) gRef x (q + (m + 1 - c)) (iterCov (I := I) gRef q B (m + 1 - c) x)))]
            congr 1
            · refine Finset.sum_congr rfl fun c hc => ?_
              have : m + 1 - (c + 1) = m - c := by omega
              rw [this]; ring
            · refine Finset.sum_congr rfl fun c hc => ?_
              have : m - c + 1 = m + 1 - c := by
                simp only [Finset.mem_range] at hc; omega
              rw [this]; ring
        _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : ℝ) *
              Real.sqrt (normSq0S (I := I) gRef x (s + c) (iterCov (I := I) gRef s A c x)) *
              Real.sqrt (normSq0S (I := I) gRef x (q + (m + 1 - c)) (iterCov (I := I) gRef q B (m + 1 - c) x)) :=
            Finset.sum_congr rfl fun c _ => by ring





omit [Module.Finite ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] [IsManifold I 2 M] in
theorem smulByFun_eq_product [FiniteDimensional Real E] {q : ℕ}
    (φ : M → Real) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) φ hφ B =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (finCongr (Nat.zero_add q))
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 0) (q := q)
          (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (∞ : WithTop ℕ∞) φ hφ) B) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have he : ∀ i : Fin q, finCongr (Nat.zero_add q) (Fin.natAdd 0 i) = i := by
    intro i
    ext
    simp
  show (φ x • B x) v =
    ContinuousMultilinearMap.domDomCongr (finCongr (Nat.zero_add q))
      (Bundle.continuousMultilinearMap.product_fun
        (ContinuousMultilinearMap.constOfIsEmpty Real
          (fun _ : Fin 0 => TangentSpace I x) (φ x))
        (B x)) v
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Bundle.continuousMultilinearMap.product_fun_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, smul_eq_mul]
  congr 1
  refine congrArg (B x) (funext fun i => ?_)
  show v i = v (finCongr (Nat.zero_add q) (Fin.natAdd 0 i))
  exact (congrArg v (he i)).symm







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_smulF_le [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) gRef x basis (identityInvMetric (Idx := Idx)))
    (m : ℕ) {q : ℕ} (φ : M → Real) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    Real.sqrt (normSq0S (I := I) gRef x (q + m)
        (iterCov (I := I) gRef q
          (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (∞ : WithTop ℕ∞) φ hφ B) m x)) ≤
      ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
        Real.sqrt (normSq0S (I := I) gRef x (0 + c)
          (iterCov (I := I) gRef 0
            (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (∞ : WithTop ℕ∞) φ hφ) c x)) *
        Real.sqrt (normSq0S (I := I) gRef x (q + (m - c))
          (iterCov (I := I) gRef q B (m - c) x)) := by
  rw [smulByFun_eq_product (I := I) φ hφ B,
    normSq0S_iterCov_domDomCongr (I := I) gRef (finCongr (Nat.zero_add q))
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 0) (q := q)
        (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) φ hφ) B) m x basis hinv]
  exact iterCov_product_sqrtNormSq_le (I := I) gRef x basis hinv m
    (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) φ hφ) B

end HCGCompactness
end DifferentialGeometry
