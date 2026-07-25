import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.NablaReactionAllK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant
import DifferentialGeometry.Tensor.RSTensor.ProductNablaLeibniz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckBaseProducer

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




omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem stMetricCompat
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.family.metric t) := by
  simpa [SolutionFamily.connection, SolutionOn.family_metric] using
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t)

set_option backward.isDefEq.respectTransparency false in






def starProd (S : SolutionOn (I := I) (M := M) D) (t : Real) (a b : ℕ) :
    (r : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (((4 + a) + (4 + b)) + 2 * r)
  | 0 => MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 4 + a) (q := 4 + b)
      (nablaKRm04Field (I := I) S t a) (nablaKRm04Field (I := I) S t b)
  | (r + 1) => MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
      (s := ((4 + a) + (4 + b)) + 2 * r) (q := 2)
      (starProd S t a b r) (metricTensorField (I := I) (S.family.metric t))

set_option backward.isDefEq.respectTransparency false in

def mtIter (g : SmoothRiemannianMetric I M) {s : ℕ} :
    (τ : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 * τ) →
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s
  | 0, A => A
  | (τ + 1), A => mtIter g τ
      (metricTraceFirstTwoField (I := I) (M := M) (s := s + 2 * τ) g A)

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem mtIter_add (g : SmoothRiemannianMetric I M) {s : ℕ} (τ : ℕ) :
    ∀ A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 * τ),
      mtIter (I := I) g τ (A + B) = mtIter (I := I) g τ A + mtIter (I := I) g τ B := by
  induction τ with
  | zero => intro A B; rfl
  | succ τ ih =>
      intro A B
      change mtIter (I := I) g τ
          (metricTraceFirstTwoField (I := I) (M := M) (s := s + 2 * τ) g (A + B)) = _
      rw [metricTraceFirstTwoField_add, ih]
      rfl

set_option backward.isDefEq.respectTransparency false in



def starBaseField
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k a b r : ℕ)
    (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k) :=
  mtIter (I := I) (S.family.metric t) (2 + r)
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) σ (starProd (I := I) S t a b r))

set_option backward.isDefEq.respectTransparency false in










inductive StarSum2 (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (k : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k) → Prop
  | zero (k : ℕ) :
      StarSum2 S t k
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (4 + k))
  | add {k : ℕ}
      {A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)} :
      StarSum2 S t k A → StarSum2 S t k B → StarSum2 S t k (A + B)
  | smul {k : ℕ} (c : Real)
      {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)} :
      StarSum2 S t k A → StarSum2 S t k (c • A)
  | base (k a b r : ℕ)
      (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
      StarSum2 S t k (starBaseField (I := I) S t k a b r σ)

set_option backward.isDefEq.respectTransparency false in




inductive StarSum2Cost (Idx : Type*) [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (k : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k) → Real → Prop
  | zero (k : ℕ) :
      StarSum2Cost Idx S t k
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (4 + k)) 0
  | add {k : ℕ}
      {A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)} {Ca Cb : Real} :
      StarSum2Cost Idx S t k A Ca → StarSum2Cost Idx S t k B Cb →
        StarSum2Cost Idx S t k (A + B) (Ca + Cb)
  | smul {k : ℕ} (c : Real)
      {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)} {C : Real} :
      StarSum2Cost Idx S t k A C → StarSum2Cost Idx S t k (c • A) (|c| * C)
  | base (k a b r : ℕ)
      (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
      StarSum2Cost Idx S t k (starBaseField (I := I) S t k a b r σ)
        ((Fintype.card Idx : Real) ^ (2 + r))


omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem StarSum2Cost.mem {Idx : Type*} [Fintype Idx]
    {S : SolutionOn (I := I) (M := M) D} {t : Real} {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)} {C : Real}
    (hT : StarSum2Cost (I := I) Idx S t k T C) :
    StarSum2 (I := I) S t k T := by
  induction hT with
  | zero => exact StarSum2.zero _
  | add _ _ ihA ihB => exact StarSum2.add ihA ihB
  | smul c _ ih => exact StarSum2.smul c ih
  | base a b r σ => exact StarSum2.base _ a b r σ


omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem StarSum2Cost.nonneg {Idx : Type*} [Fintype Idx]
    {S : SolutionOn (I := I) (M := M) D} {t : Real} {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)} {C : Real}
    (hT : StarSum2Cost (I := I) Idx S t k T C) : 0 ≤ C := by
  induction hT with
  | zero => exact le_rfl
  | add _ _ ihA ihB => exact add_nonneg ihA ihB
  | smul _ _ ih => exact mul_nonneg (abs_nonneg _) ih
  | base => positivity


omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem StarSum2.cost {Idx : Type*} [Fintype Idx]
    {S : SolutionOn (I := I) (M := M) D} {t : Real} {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)}
    (hT : StarSum2 (I := I) S t k T) :
    ∃ C : Real, StarSum2Cost (I := I) Idx S t k T C := by
  induction hT with
  | zero => exact ⟨0, StarSum2Cost.zero _⟩
  | add _ _ ihA ihB =>
      obtain ⟨Ca, hCa⟩ := ihA
      obtain ⟨Cb, hCb⟩ := ihB
      exact ⟨Ca + Cb, StarSum2Cost.add hCa hCb⟩
  | smul c _ ih =>
      obtain ⟨C, hC⟩ := ih
      exact ⟨|c| * C, StarSum2Cost.smul c hC⟩
  | base a b r σ => exact ⟨_, StarSum2Cost.base _ a b r σ⟩

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem starSum2_sum {S : SolutionOn (I := I) (M := M) D} {t : Real} {k : ℕ}
    {ι : Type*} (s : Finset ι)
    (T : ι → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k))
    (h : ∀ q ∈ s, StarSum2 (I := I) S t k (T q)) :
    StarSum2 (I := I) S t k (∑ q ∈ s, T q) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      exact StarSum2.zero k
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact StarSum2.add (h a (Finset.mem_insert_self a s))
        (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))

set_option backward.isDefEq.respectTransparency false in


omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem starSum2Cost_sum {Idx : Type*} [Fintype Idx]
    {S : SolutionOn (I := I) (M := M) D} {t : Real} {k : ℕ}
    {ι : Type*} (s : Finset ι)
    (T : ι → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) (C : ι → Real)
    (h : ∀ q ∈ s, StarSum2Cost (I := I) Idx S t k (T q) (C q)) :
    StarSum2Cost (I := I) Idx S t k (∑ q ∈ s, T q) (∑ q ∈ s, C q) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact StarSum2Cost.zero k
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact StarSum2Cost.add (h a (Finset.mem_insert_self a s))
        (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))









set_option backward.isDefEq.respectTransparency false in


def stNabla (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + (k + 1)) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (4 + k) (S.family.connection t) T
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t) T)

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem stNabla_realizes (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) T (stNabla (I := I) S t T) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (4 + k) (S.family.connection t) T
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t) T)

set_option backward.isDefEq.respectTransparency false in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem stNabla_zero
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ} :
    stNabla (I := I) S t
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (4 + k))
      = 0 := by
  have hc := stNabla_realizes (I := I) S t
    (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k))
  have h2 := hc.smul (0 : Real)
  rw [smul_zero] at h2
  have h3 := totalNabla0SRealizes_unique (I := I) hc h2
  rw [h3, zero_smul]

set_option backward.isDefEq.respectTransparency false in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem stNabla_add
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ}
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    stNabla (I := I) S t (A + B) = stNabla (I := I) S t A + stNabla (I := I) S t B :=
  totalNabla0SRealizes_unique (I := I) (stNabla_realizes (I := I) S t (A + B))
    ((stNabla_realizes (I := I) S t A).add (stNabla_realizes (I := I) S t B))

set_option backward.isDefEq.respectTransparency false in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem stNabla_smul
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ} (c : Real)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    stNabla (I := I) S t (c • A) = c • stNabla (I := I) S t A :=
  totalNabla0SRealizes_unique (I := I) (stNabla_realizes (I := I) S t (c • A))
    ((stNabla_realizes (I := I) S t A).smul c)









set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in


omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem starProdNabla
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (a b : ℕ) :
    ∀ r : ℕ,
      ∃ (e₁ : Fin (((4 + (a + 1)) + (4 + b)) + 2 * r)
            ≃ Fin ((((4 + a) + (4 + b)) + 2 * r) + 1))
        (e₂ : Fin (((4 + a) + (4 + (b + 1))) + 2 * r)
            ≃ Fin ((((4 + a) + (4 + b)) + 2 * r) + 1)),
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (((4 + a) + (4 + b)) + 2 * r) (S.family.connection t)
          (starProd (I := I) S t a b r)
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) e₁
              (starProd (I := I) S t (a + 1) b r)
            + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) e₂
              (starProd (I := I) S t a (b + 1) r)) := by
  intro r
  induction r with
  | zero =>
      exact ⟨leibnizLeftEquiv (4 + a) (4 + b), leibnizRightEquiv (4 + a) (4 + b),
        nabla0S_product_realizes (I := I) (M := M) (S.family.connection t)
          (nablaKRm04Field (I := I) S t a) (nablaKRm04Field (I := I) S t b)
          (nablaKRm04Field (I := I) S t (a + 1)) (nablaKRm04Field (I := I) S t (b + 1))
          (nablaKRm04Field_realizes (I := I) S t a)
          (nablaKRm04Field_realizes (I := I) S t b)⟩
  | succ r ih =>
      obtain ⟨e₁, e₂, hr⟩ := ih
      have h0 := zero_realizes_metric (I := I) (S.family.connection t)
        (S.family.metric t) (stMetricCompat (I := I) S t)
      have hp := nabla0S_product_realizes (I := I) (M := M) (S.family.connection t)
        (starProd (I := I) S t a b r)
        (metricTensorField (I := I) (S.family.metric t)) _ 0 hr h0
      rw [MultilinearSection.product_zero, MultilinearSection.domDomCongr_zero, add_zero,
        MultilinearSection.product_add_left, MultilinearSection.product_domDomCongr_left,
        MultilinearSection.product_domDomCongr_left, MultilinearSection.domDomCongr_add,
        MultilinearSection.domDomCongr_trans, MultilinearSection.domDomCongr_trans] at hp
      exact ⟨_, _, hp⟩

set_option backward.isDefEq.respectTransparency false in


omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem stNablaMtIter
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {s : ℕ} (τ : ℕ) :
    ∀ (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 2 * τ))
      (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((s + 2 * τ) + 1)),
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2 * τ) cov A nablaA →
      ∃ ρ : Fin ((s + 2 * τ) + 1) ≃ Fin ((s + 1) + 2 * τ),
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (mtIter (I := I) g τ A)
          (mtIter (I := I) g τ
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) ρ nablaA)) := by
  induction τ with
  | zero =>
      intro A nablaA h
      refine ⟨Equiv.refl _, ?_⟩
      rw [MultilinearSection.domDomCongr_refl]
      exact h
  | succ τ ih =>
      intro A nablaA h
      have h1 := nablaRealizes_metricTraceFirstTwo (I := I) (M := M) (s := s + 2 * τ)
        cov hcov1 g hmc A nablaA h
      obtain ⟨ρ', h2⟩ := ih
        (metricTraceFirstTwoField (I := I) (M := M) (s := s + 2 * τ) g A)
        (metricTraceFirstTwoField (I := I) (M := M) (s := (s + 2 * τ) + 1) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (traceNablaShuffle (s + 2 * τ)) nablaA)) h1
      rw [← metricTraceFirstTwoField_domDomCongr (I := I) (M := M) g ρ'
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞)
              (traceNablaShuffle (s + 2 * τ)) nablaA),
          MultilinearSection.domDomCongr_trans] at h2
      exact ⟨_, h2⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem stNabla_starBase
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (k a b r : ℕ)
    (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
    ∃ (σL : Fin (((4 + (a + 1)) + (4 + b)) + 2 * r) ≃ Fin ((4 + (k + 1)) + 2 * (2 + r)))
      (σR : Fin (((4 + a) + (4 + (b + 1))) + 2 * r) ≃ Fin ((4 + (k + 1)) + 2 * (2 + r))),
      stNabla (I := I) S t (starBaseField (I := I) S t k a b r σ)
    = starBaseField (I := I) S t (k + 1) (a + 1) b r σL
        + starBaseField (I := I) S t (k + 1) a (b + 1) r σR := by
  classical
  have hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (1 : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  obtain ⟨e₁, e₂, hP⟩ := starProdNabla (I := I) S t a b r
  have h2 := totalNabla0SRealizes_domDomCongr (I := I) (S.family.connection t) σ _ _ hP
  obtain ⟨ρ, h3⟩ := stNablaMtIter (I := I) (S.family.metric t) (S.family.connection t)
    hcov1 (stMetricCompat (I := I) S t) (s := 4 + k) (2 + r) _ _ h2
  have heq := totalNabla0SRealizes_unique (I := I)
    (stNabla_realizes (I := I) S t (starBaseField (I := I) S t k a b r σ)) h3
  refine ⟨e₁.trans ((frontExtendEquiv σ).trans ρ),
    e₂.trans ((frontExtendEquiv σ).trans ρ), ?_⟩
  rw [heq]
  simp only [MultilinearSection.domDomCongr_add, MultilinearSection.domDomCongr_trans,
    Equiv.trans_assoc, starBaseField]
  rw [mtIter_add]

set_option backward.isDefEq.respectTransparency false in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem StarSum2.nabla
    [Module.Finite ℝ E]
    {S : SolutionOn (I := I) (M := M) D} {t : Real}
    {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)}
    (hT : StarSum2 (I := I) S t k T) :
    StarSum2 (I := I) S t (k + 1) (stNabla (I := I) S t T) := by
  induction hT with
  | zero =>
      rw [stNabla_zero]
      exact StarSum2.zero _
  | add hA hB ihA ihB =>
      rw [stNabla_add]
      exact StarSum2.add ihA ihB
  | smul c hA ih =>
      rw [stNabla_smul]
      exact StarSum2.smul c ih
  | base a b r σ =>
      obtain ⟨σL, σR, h⟩ := stNabla_starBase (I := I) S t _ a b r σ
      rw [h]
      exact StarSum2.add (StarSum2.base _ (a + 1) b r σL)
        (StarSum2.base _ a (b + 1) r σR)

set_option backward.isDefEq.respectTransparency false in



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem StarSum2Cost.nabla
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx]
    {S : SolutionOn (I := I) (M := M) D} {t : Real} {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)} {C : Real}
    (hT : StarSum2Cost (I := I) Idx S t k T C) :
    StarSum2Cost (I := I) Idx S t (k + 1) (stNabla (I := I) S t T) (2 * C) := by
  induction hT with
  | zero =>
      rw [stNabla_zero]
      simpa using (StarSum2Cost.zero (I := I) (Idx := Idx) (S := S) (t := t) (k + 1))
  | add hA hB ihA ihB =>
      rw [stNabla_add]
      simpa [mul_add] using StarSum2Cost.add ihA ihB
  | smul c hA ih =>
      rw [stNabla_smul]
      simpa [mul_assoc, mul_left_comm, mul_comm] using StarSum2Cost.smul c ih
  | base a b r σ =>
      obtain ⟨σL, σR, h⟩ := stNabla_starBase (I := I) S t _ a b r σ
      rw [h]
      simpa [two_mul] using
        (StarSum2Cost.add
          (StarSum2Cost.base (I := I) (Idx := Idx) (S := S) (t := t)
            _ (a + 1) b r σL)
          (StarSum2Cost.base (I := I) (Idx := Idx) (S := S) (t := t)
            _ a (b + 1) r σR))











set_option backward.isDefEq.respectTransparency false in


def stNormSq (S : SolutionOn (I := I) (M := M) D) (t : Real) (j : ℕ) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  compNormSqMulti (fun m : Fin (4 + j) → Idx =>
    nablaKRm04Field (I := I) S t j x (fun p => basis (m p)))


private theorem sumIdentityDiag {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
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



omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mtInputBasis {x : M} {Idx : Type*} {s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (r r' : Idx) (mm : Fin s' → Idx) :
    ∃ mIdx : Fin (s' + 2) → Idx,
      metricTraceInput (I := I) (basis r) (basis r') (fun p => basis (mm p))
        = fun q => basis (mIdx q) := by
  refine ⟨fun q => if h0 : (q : ℕ) = 0 then r else if h1 : (q : ℕ) = 1 then r'
    else mm ⟨(q : ℕ) - 2, by have := q.isLt; omega⟩, ?_⟩
  funext q
  simp only [metricTraceInput_apply]
  split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mtfOrthoBd
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s' + 2))
    (c : Real)
    (hX : ∀ mm : Fin (s' + 2) → Idx, |X x (fun q => basis (mm q))| ≤ c)
    (mm : Fin s' → Idx) :
    |metricTraceFirstTwoField (I := I) (M := M) g X x (fun q => basis (mm q))| ≤
      (Fintype.card Idx : Real) * c := by
  classical
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx)) hinv (X x) (fun q => basis (mm q))]
  unfold metricTrace0S2InBasis
  rw [sumIdentityDiag (fun i j => (X x)
    (metricTraceInput (I := I) (basis i) (basis j) (fun q => basis (mm q))))]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [show (Fintype.card Idx : Real) * c = ∑ _i : Idx, c from by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨mIdx, hmt⟩ := mtInputBasis (I := I) basis i i mm
  rw [hmt]
  exact hX _

set_option backward.isDefEq.respectTransparency false in


omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mtIterOrthoBd
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    {s' : ℕ} (τ : ℕ) :
    ∀ (X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s' + 2 * τ)) (c : Real),
      (∀ mm : Fin (s' + 2 * τ) → Idx, |X x (fun q => basis (mm q))| ≤ c) →
      ∀ mm : Fin s' → Idx,
        |mtIter (I := I) g τ X x (fun q => basis (mm q))| ≤
          (Fintype.card Idx : Real) ^ τ * c := by
  induction τ with
  | zero =>
      intro X c hX mm
      simpa using hX mm
  | succ τ ih =>
      intro X c hX mm
      have h1 : ∀ mm' : Fin ((s' + 2 * τ) + 2) → Idx,
          |X x (fun q => basis (mm' q))| ≤ c := fun mm' => hX mm'
      have h2 := ih (metricTraceFirstTwoField (I := I) (M := M) (s := s' + 2 * τ) g X)
        ((Fintype.card Idx : Real) * c)
        (fun mm' => mtfOrthoBd (I := I) g basis horth (s' := s' + 2 * τ) X c h1 mm') mm
      refine le_trans h2 (le_of_eq ?_)
      ring

set_option backward.isDefEq.respectTransparency false in



omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem starProdBd {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (a b : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    ∀ (r : ℕ) (mm : Fin ((((4 + a) + (4 + b)) + 2 * r)) → Idx),
      |starProd (I := I) S t a b r x (fun q => basis (mm q))| ≤
        Real.sqrt (stNormSq (I := I) S t a x basis) *
          Real.sqrt (stNormSq (I := I) S t b x basis) := by
  intro r
  induction r with
  | zero =>
      intro mm
      have hpf := Bundle.continuousMultilinearMap.product_fun_apply
        (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
        (s := 4 + a) (q := 4 + b) (x := x)
        (nablaKRm04Field (I := I) S t a x) (nablaKRm04Field (I := I) S t b x)
        (fun q => basis (mm q))
      refine le_trans (le_of_eq (congrArg abs hpf)) ?_
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (Real.sqrt_nonneg _)
      · exact Real.abs_le_sqrt (sq_le_compNormSqMulti
          (fun m' : Fin (4 + a) → Idx =>
            nablaKRm04Field (I := I) S t a x (fun p => basis (m' p))) _)
      · exact Real.abs_le_sqrt (sq_le_compNormSqMulti
          (fun m' : Fin (4 + b) → Idx =>
            nablaKRm04Field (I := I) S t b x (fun p => basis (m' p))) _)
  | succ r ih =>
      intro mm
      have hpf := Bundle.continuousMultilinearMap.product_fun_apply
        (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
        (s := (4 + a) + (4 + b) + 2 * r) (q := 2) (x := x)
        (starProd (I := I) S t a b r x)
        (metricTensorField (I := I) (S.family.metric t) x)
        (fun q => basis (mm q))
      refine le_trans (le_of_eq (congrArg abs hpf)) ?_
      rw [abs_mul, metricTensorField_apply]
      refine le_trans (mul_le_mul (ih _) ?_ (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (le_of_eq (mul_one _))
      change |(S.family.metric t).inner x
          (basis (mm (Fin.natAdd (((4 + a) + (4 + b)) + 2 * r) (0 : Fin 2))))
          (basis (mm (Fin.natAdd (((4 + a) + (4 + b)) + 2 * r) (1 : Fin 2))))| ≤ 1
      rw [horth]
      split_ifs <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in


omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem StarSum2Cost.bound
    [Module.Finite ℝ E]
    {S : SolutionOn (I := I) (M := M) D} {t : Real}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)} {C : Real}
    (hT : StarSum2Cost (I := I) Idx S t k T C) :
    ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x)),
      (∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j)
          = if i = j then (1 : Real) else 0) →
      ∀ m : Fin (4 + k) → Idx,
        |T x (fun p => basis (m p))| ≤
          C * ∑ j ∈ Finset.range (k + 1),
            Real.sqrt (stNormSq (I := I) S t j x basis) *
              Real.sqrt (stNormSq (I := I) S t (k - j) x basis) := by
  classical
  induction hT with
  | zero =>
      intro x basis _ m
      simp [ContMDiffSection.coe_zero]
  | @add A B Ca Cb hA hB ihA ihB =>
      intro x basis horth m
      have h1 := ihA x basis horth m
      have h2 := ihB x basis horth m
      have hval : (A + B) x (fun p => basis (m p))
          = A x (fun p => basis (m p)) + B x (fun p => basis (m p)) := rfl
      rw [hval]
      refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq (by ring)))
  | @smul c A C hA ih =>
      intro x basis horth m
      have h1 := ih x basis horth m
      have hval : (c • A) x (fun p => basis (m p))
          = c * (A x (fun p => basis (m p))) := rfl
      rw [hval, abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg c)) (le_of_eq (by ring))
  | base a b r σ =>
      intro x basis horth m
      have hcard := Fintype.card_congr σ
      simp only [Fintype.card_fin] at hcard
      have hab : a + b = k := by omega
      have hinner : ∀ mm : Fin ((4 + k) + 2 * (2 + r)) → Idx,
          |(MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) σ
              (starProd (I := I) S t a b r)) x (fun q => basis (mm q))| ≤
            Real.sqrt (stNormSq (I := I) S t a x basis) *
              Real.sqrt (stNormSq (I := I) S t b x basis) := by
        intro mm
        rw [MultilinearSection.domDomCongr_apply,
          ContinuousMultilinearMap.domDomCongr_apply]
        exact starProdBd (I := I) S t a b basis horth r (fun p => mm (σ p))
      have htop := mtIterOrthoBd (I := I) (S.family.metric t) basis horth
        (s' := 4 + k) (2 + r) _ _ hinner m
      have hmem : a ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have hb : k - a = b := by omega
      have hsingle : Real.sqrt (stNormSq (I := I) S t a x basis) *
            Real.sqrt (stNormSq (I := I) S t b x basis) ≤
          ∑ j ∈ Finset.range (k + 1),
            Real.sqrt (stNormSq (I := I) S t j x basis) *
              Real.sqrt (stNormSq (I := I) S t (k - j) x basis) := by
        have hs := Finset.single_le_sum
          (f := fun j => Real.sqrt (stNormSq (I := I) S t j x basis) *
            Real.sqrt (stNormSq (I := I) S t (k - j) x basis))
          (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hmem
        simp only [hb] at hs
        exact hs
      exact le_trans htop (mul_le_mul_of_nonneg_left hsingle (by positivity))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in







omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem StarSum2.bound
    [Module.Finite ℝ E]
    {S : SolutionOn (I := I) (M := M) D} {t : Real}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)}
    (hT : StarSum2 (I := I) S t k T) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x)),
        (∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j)
            = if i = j then (1 : Real) else 0) →
        ∀ m : Fin (4 + k) → Idx,
          |T x (fun p => basis (m p))| ≤
            C * ∑ j ∈ Finset.range (k + 1),
              Real.sqrt (stNormSq (I := I) S t j x basis) *
                Real.sqrt (stNormSq (I := I) S t (k - j) x basis) := by
  classical
  induction hT with
  | zero =>
      refine ⟨0, le_refl 0, fun x basis _ m => ?_⟩
      simp [ContMDiffSection.coe_zero]
  | @add A B hA hB ihA ihB =>
      obtain ⟨Ca, hCa0, hCa⟩ := ihA
      obtain ⟨Cb, hCb0, hCb⟩ := ihB
      refine ⟨Ca + Cb, add_nonneg hCa0 hCb0, fun x basis horth m => ?_⟩
      have h1 := hCa x basis horth m
      have h2 := hCb x basis horth m
      have hval : (A + B) x (fun p => basis (m p))
          = A x (fun p => basis (m p)) + B x (fun p => basis (m p)) := rfl
      rw [hval]
      refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq (by ring)))
  | @smul c A hA ih =>
      obtain ⟨Ca, hCa0, hCa⟩ := ih
      refine ⟨|c| * Ca, mul_nonneg (abs_nonneg c) hCa0, fun x basis horth m => ?_⟩
      have h1 := hCa x basis horth m
      have hval : (c • A) x (fun p => basis (m p))
          = c * (A x (fun p => basis (m p))) := rfl
      rw [hval, abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg c)) (le_of_eq (by ring))
  | base a b r σ =>
      have hcard := Fintype.card_congr σ
      simp only [Fintype.card_fin] at hcard
      have hab : a + b = k := by omega
      refine ⟨(Fintype.card Idx : Real) ^ (2 + r), by positivity,
        fun x basis horth m => ?_⟩

      have hinner : ∀ mm : Fin ((4 + k) + 2 * (2 + r)) → Idx,
          |(MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) σ
              (starProd (I := I) S t a b r)) x (fun q => basis (mm q))| ≤
            Real.sqrt (stNormSq (I := I) S t a x basis) *
              Real.sqrt (stNormSq (I := I) S t b x basis) := by
        intro mm
        rw [MultilinearSection.domDomCongr_apply,
          ContinuousMultilinearMap.domDomCongr_apply]
        exact starProdBd (I := I) S t a b basis horth r (fun p => mm (σ p))

      have htop := mtIterOrthoBd (I := I) (S.family.metric t) basis horth
        (s' := 4 + k) (2 + r) _ _ hinner m
      have hmem : a ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have hb : k - a = b := by omega
      have hsingle : Real.sqrt (stNormSq (I := I) S t a x basis) *
            Real.sqrt (stNormSq (I := I) S t b x basis) ≤
          ∑ j ∈ Finset.range (k + 1),
            Real.sqrt (stNormSq (I := I) S t j x basis) *
              Real.sqrt (stNormSq (I := I) S t (k - j) x basis) := by
        have hs := Finset.single_le_sum
          (f := fun j => Real.sqrt (stNormSq (I := I) S t j x basis) *
            Real.sqrt (stNormSq (I := I) S t (k - j) x basis))
          (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hmem
        simp only [hb] at hs
        exact hs
      exact le_trans htop (mul_le_mul_of_nonneg_left hsingle (by positivity))









set_option backward.isDefEq.respectTransparency false in



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mtfDiag
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s' + 2))
    (mm : Fin s' → Idx) :
    metricTraceFirstTwoField (I := I) (M := M) g X x (fun q => basis (mm q))
      = ∑ i : Idx, X x
          (metricTraceInput (I := I) (basis i) (basis i) (fun q => basis (mm q))) := by
  classical
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx)) hinv (X x) (fun q => basis (mm q))]
  unfold metricTrace0S2InBasis
  rw [sumIdentityDiag (fun i j => (X x)
    (metricTraceInput (I := I) (basis i) (basis j) (fun q => basis (mm q))))]

set_option backward.isDefEq.respectTransparency false in






omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem starBase_comp_eq
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k a b : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (σ : Fin (((4 + a) + (4 + b)) + 2 * 0) ≃ Fin ((4 + k) + 2 * (2 + 0)))
    (m : Fin (4 + k) → Idx) :
    starBaseField (I := I) S t k a b 0 σ x (fun p => basis (m p))
      = ∑ j : Idx, ∑ i : Idx,
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) σ (starProd (I := I) S t a b 0)) x
            (metricTraceInput (I := I) (basis i) (basis i)
              (metricTraceInput (I := I) (basis j) (basis j)
                (fun p => basis (m p)))) := by
  classical
  rw [starBaseField]
  set A := MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (∞ : WithTop ℕ∞) σ (starProd (I := I) S t a b 0) with hA


  rw [show mtIter (I := I) (S.family.metric t) (2 + 0) A
      = metricTraceFirstTwoField (I := I) (M := M) (S.family.metric t)
          (metricTraceFirstTwoField (I := I) (M := M) (S.family.metric t) A) from rfl]

  rw [mtfDiag (I := I) (S.family.metric t) basis horth
    (metricTraceFirstTwoField (I := I) (M := M) (S.family.metric t) A) m]
  refine Finset.sum_congr rfl fun j _ => ?_

  obtain ⟨mIdx, hmIdx⟩ := mtInputBasis (I := I) basis j j m
  rw [hmIdx, mtfDiag (I := I) (S.family.metric t) basis horth A mIdx, ← hmIdx]
  rfl

set_option backward.isDefEq.respectTransparency false in




omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem starBaseProd_eq
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k a b : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (σ : Fin (((4 + a) + (4 + b)) + 2 * 0) ≃ Fin ((4 + k) + 2 * (2 + 0)))
    (m : Fin (4 + k) → Idx) :
    starBaseField (I := I) S t k a b 0 σ x (fun p => basis (m p))
      = ∑ j : Idx, ∑ i : Idx,
          nablaKRm04Field (I := I) S t a x
              (fun p => metricTraceInput (I := I) (basis i) (basis i)
                (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p)))
                (σ (Fin.castAdd (4 + b) p)))
            * nablaKRm04Field (I := I) S t b x
              (fun p => metricTraceInput (I := I) (basis i) (basis i)
                (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p)))
                (σ (Fin.natAdd (4 + a) p))) := by
  rw [starBase_comp_eq (I := I) S t k a b basis horth σ m]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [MultilinearSection.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]


  exact Bundle.continuousMultilinearMap.product_fun_apply
    (nablaKRm04Field (I := I) S t a x) (nablaKRm04Field (I := I) S t b x)
    (fun p => metricTraceInput (I := I) (basis i) (basis i)
      (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p))) (σ p))










def btPermE : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![4, 0, 5, 2, 6, 1, 7, 3] (by decide)

set_option backward.isDefEq.respectTransparency false in



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem btStar_eq
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (m : Fin (4 + 0) → Idx) :
    starBaseField (I := I) S t 0 0 0 0 btPermE x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, e, m 1, f] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 2, e, m 3, f] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth btPermE m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (btPermE (Fin.castAdd (4 + 0) p)))
      = (fun p => basis (![m 0, e, m 1, f] p)) := by
    funext p
    fin_cases p <;>
      simp [btPermE, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (btPermE (Fin.natAdd (4 + 0) p)))
      = (fun p => basis (![m 2, e, m 3, f] p)) := by
    funext p
    fin_cases p <;>
      simp [btPermE, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]









def σBt2 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![4, 0, 5, 2, 7, 1, 6, 3] (by decide)


def σBt3 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![4, 0, 6, 2, 5, 1, 7, 3] (by decide)


def σBt4 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![4, 0, 7, 2, 5, 1, 6, 3] (by decide)


def σD1 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![4, 0, 2, 1, 3, 5, 6, 7] (by decide)


def σD2 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![5, 0, 2, 1, 4, 3, 6, 7] (by decide)


def σD3 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![6, 0, 2, 1, 4, 5, 3, 7] (by decide)


def σD4 : Fin (((4 + 0) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + 0) + 2 * (2 + 0)) :=
  Equiv.ofBijective ![7, 0, 2, 1, 4, 5, 6, 3] (by decide)

set_option backward.isDefEq.respectTransparency false in




def e0Field (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + 0) :=
  (-2 : Real) • starBaseField (I := I) S t 0 0 0 0 btPermE
    + (2 : Real) • starBaseField (I := I) S t 0 0 0 0 σBt2
    + (-2 : Real) • starBaseField (I := I) S t 0 0 0 0 σBt3
    + (2 : Real) • starBaseField (I := I) S t 0 0 0 0 σBt4
    + starBaseField (I := I) S t 0 0 0 0 σD1
    + starBaseField (I := I) S t 0 0 0 0 σD2
    + starBaseField (I := I) S t 0 0 0 0 σD3
    + starBaseField (I := I) S t 0 0 0 0 σD4

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem e0Field_mem (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    StarSum2 (I := I) S t 0 (e0Field (I := I) S t) := by
  unfold e0Field
  refine StarSum2.add (StarSum2.add (StarSum2.add (StarSum2.add (StarSum2.add
    (StarSum2.add (StarSum2.add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact StarSum2.smul (-2) (StarSum2.base 0 0 0 0 btPermE)
  · exact StarSum2.smul 2 (StarSum2.base 0 0 0 0 σBt2)
  · exact StarSum2.smul (-2) (StarSum2.base 0 0 0 0 σBt3)
  · exact StarSum2.smul 2 (StarSum2.base 0 0 0 0 σBt4)
  · exact StarSum2.base 0 0 0 0 σD1
  · exact StarSum2.base 0 0 0 0 σD2
  · exact StarSum2.base 0 0 0 0 σD3
  · exact StarSum2.base 0 0 0 0 σD4

set_option backward.isDefEq.respectTransparency false in


omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem e0Field_cost (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    StarSum2Cost (I := I) (Fin 3) S t 0 (e0Field (I := I) S t) 108 := by
  unfold e0Field
  convert StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add
    (StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add
      (StarSum2Cost.smul (-2) (StarSum2Cost.base 0 0 0 0 btPermE))
      (StarSum2Cost.smul 2 (StarSum2Cost.base 0 0 0 0 σBt2)))
      (StarSum2Cost.smul (-2) (StarSum2Cost.base 0 0 0 0 σBt3)))
      (StarSum2Cost.smul 2 (StarSum2Cost.base 0 0 0 0 σBt4)))
      (StarSum2Cost.base 0 0 0 0 σD1))
      (StarSum2Cost.base 0 0 0 0 σD2))
      (StarSum2Cost.base 0 0 0 0 σD3))
      (StarSum2Cost.base 0 0 0 0 σD4) using 1
  norm_num








section ComponentIdentity

open DifferentialGeometry.Dim3Reaction

set_option backward.isDefEq.respectTransparency false in



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem rmComp_eq_rm
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (basis : Fin 3 → TangentSpace I x)
    (horth : ∀ i j : Fin 3,
      (S.base.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (R : Fin 3 → Fin 3 → Real)
    (hR : ∀ i j : Fin 3, R i j = S.ricciAt t x (vec2 (I := I) (basis i) (basis j)))
    (htr : S.scalar t x = sc R)
    (n : Fin 4 → Fin 3) :
    nablaKRm04Field (I := I) S t 0 x (fun p => basis (n p))
      = rm R (n 0) (n 1) (n 2) (n 3) := by
  haveI : NeZero (Module.finrank Real E) :=
    ⟨by have h : Module.finrank Real E = 3 := hdim; omega⟩
  rw [nablaKRm04Field_zero,
    solution_rm04_kn_all (I := I) S t x hdim (fun p => basis (n p))]
  simp only [← hR, horth, htr, rm, sc, kd]



theorem ricTrace (R : Fin 3 → Fin 3 → Real) (a c : Fin 3) :
    ∑ b : Fin 3, rm R a b c b = - R a c := by
  fin_cases a <;> fin_cases c <;>
    simp only [Fin.sum_univ_three, rm, sc, kd, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq,
      reduceIte] <;>
    ring




theorem driftPiece (R : Fin 3 → Fin 3 → Real) (a : Fin 3) (g : Fin 3 → Real) :
    (∑ e : Fin 3, ∑ f : Fin 3, rm R a e f e * g f) = - ∑ p : Fin 3, R a p * g p := by
  rw [Finset.sum_comm]
  have h : ∀ f : Fin 3, (∑ e : Fin 3, rm R a e f e * g f) = -(R a f * g f) := by
    intro f
    rw [← Finset.sum_mul, ricTrace, neg_mul]
  simp only [h, Finset.sum_neg_distrib]






section TermIdentities
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
variable (basis : Module.Basis Idx Real (TangentSpace I x))
variable (horth : ∀ i j : Idx,
  (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
variable (m : Fin (4 + 0) → Idx)

include horth

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem btStar2
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σBt2 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, e, m 1, f] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 3, e, m 2, f] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σBt2 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σBt2 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 0, e, m 1, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σBt2, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σBt2 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![m 3, e, m 2, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σBt2, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem btStar3
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σBt3 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, e, m 2, f] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 1, e, m 3, f] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σBt3 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σBt3 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 0, e, m 2, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σBt3, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σBt3 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![m 1, e, m 3, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σBt3, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem btStar4
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σBt4 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, e, m 3, f] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 1, e, m 2, f] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σBt4 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σBt4 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 0, e, m 3, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σBt4, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σBt4 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![m 1, e, m 2, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σBt4, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem drStar1
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σD1 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, e, f, e] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![f, m 1, m 2, m 3] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σD1 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD1 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 0, e, f, e] p)) := by
    funext p
    fin_cases p <;>
      simp [σD1, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD1 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![f, m 1, m 2, m 3] p)) := by
    funext p
    fin_cases p <;>
      simp [σD1, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem drStar2
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σD2 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 1, e, f, e] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, f, m 2, m 3] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σD2 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD2 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 1, e, f, e] p)) := by
    funext p
    fin_cases p <;>
      simp [σD2, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD2 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![m 0, f, m 2, m 3] p)) := by
    funext p
    fin_cases p <;>
      simp [σD2, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem drStar3
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σD3 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 2, e, f, e] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, m 1, f, m 3] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σD3 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD3 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 2, e, f, e] p)) := by
    funext p
    fin_cases p <;>
      simp [σD3, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD3 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![m 0, m 1, f, m 3] p)) := by
    funext p
    fin_cases p <;>
      simp [σD3, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem drStar4
    [Module.Finite ℝ E]
    :
    starBaseField (I := I) S t 0 0 0 0 σD4 x (fun p => basis (m p))
      = ∑ e : Idx, ∑ f : Idx,
          nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 3, e, f, e] p))
            * nablaKRm04Field (I := I) S t 0 x (fun p => basis (![m 0, m 1, m 2, f] p)) := by
  classical
  rw [starBaseProd_eq (I := I) S t 0 0 0 basis horth σD4 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD4 (Fin.castAdd (4 + 0) p))) = (fun p => basis (![m 3, e, f, e] p)) := by
    funext p
    fin_cases p <;>
      simp [σD4, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hR : (fun p => metricTraceInput (I := I) (basis e) (basis e)
        (metricTraceInput (I := I) (basis f) (basis f) (fun p => basis (m p)))
        (σD4 (Fin.natAdd (4 + 0) p))) = (fun p => basis (![m 0, m 1, m 2, f] p)) := by
    funext p
    fin_cases p <;>
      simp [σD4, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hL, hR]

end TermIdentities

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in


omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem e0Field_comp
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3,
      (S.base.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (R : Fin 3 → Fin 3 → Real)
    (hR : ∀ i j : Fin 3, R i j = S.ricciAt t x (vec2 (I := I) (basis i) (basis j)))
    (htr : S.scalar t x = sc R)
    (n : Fin 4 → Fin 3) :
    e0Field (I := I) S t x (fun p => basis (n p))
      = -2 * (Bt R (n 0) (n 1) (n 2) (n 3) - Bt R (n 0) (n 1) (n 3) (n 2)
            + Bt R (n 0) (n 2) (n 1) (n 3) - Bt R (n 0) (n 3) (n 1) (n 2))
        - drift R (n 0) (n 1) (n 2) (n 3) := by
  classical

  have hev : e0Field (I := I) S t x (fun p => basis (n p))
      = -2 * starBaseField (I := I) S t 0 0 0 0 btPermE x (fun p => basis (n p))
        + 2 * starBaseField (I := I) S t 0 0 0 0 σBt2 x (fun p => basis (n p))
        + -2 * starBaseField (I := I) S t 0 0 0 0 σBt3 x (fun p => basis (n p))
        + 2 * starBaseField (I := I) S t 0 0 0 0 σBt4 x (fun p => basis (n p))
        + starBaseField (I := I) S t 0 0 0 0 σD1 x (fun p => basis (n p))
        + starBaseField (I := I) S t 0 0 0 0 σD2 x (fun p => basis (n p))
        + starBaseField (I := I) S t 0 0 0 0 σD3 x (fun p => basis (n p))
        + starBaseField (I := I) S t 0 0 0 0 σD4 x (fun p => basis (n p)) := rfl
  rw [hev, btStar_eq (I := I) S t basis horth n, btStar2 (I := I) S t basis horth n,
    btStar3 (I := I) S t basis horth n, btStar4 (I := I) S t basis horth n,
    drStar1 (I := I) S t basis horth n, drStar2 (I := I) S t basis horth n,
    drStar3 (I := I) S t basis horth n, drStar4 (I := I) S t basis horth n]

  simp only [rmComp_eq_rm (I := I) S t hdim basis horth R hR htr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]

  rw [driftPiece R (n 0) (fun f => rm R f (n 1) (n 2) (n 3)),
    driftPiece R (n 1) (fun f => rm R (n 0) f (n 2) (n 3)),
    driftPiece R (n 2) (fun f => rm R (n 0) (n 1) f (n 3)),
    driftPiece R (n 3) (fun f => rm R (n 0) (n 1) (n 2) f)]
  simp only [Bt, drift, Finset.sum_add_distrib]
  ring

end ComponentIdentity











open DifferentialGeometry.Dim3Reaction in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in




omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem residualStarSum_zero
    [Module.Finite ℝ E]
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hbase : ∀ (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
        (_horth : ∀ i j : Fin 3,
          (S.base.metric (t : Real)).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
        (I0 : Fin 4 → Fin 3),
        HasDerivWithinAt
          (fun r : Real => S.base.rm04 r x (fun p => basis (I0 p)))
          (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : Real) 2 x)) (fun i => basis i) I0
            + (-2 * (Bt (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j)))
                      (I0 0) (I0 1) (I0 2) (I0 3)
                    - Bt (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j)))
                      (I0 0) (I0 1) (I0 3) (I0 2)
                    + Bt (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j)))
                      (I0 0) (I0 2) (I0 1) (I0 3)
                    - Bt (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j)))
                      (I0 0) (I0 3) (I0 1) (I0 2))
                - drift (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j)))
                      (I0 0) (I0 1) (I0 2) (I0 3)))
          D.carrier (t : Real)) :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + 0),
      StarSum2 (I := I) S (t : Real) 0 T ∧
      ∀ (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
        (_horth : ∀ i j : Fin 3,
          (S.base.metric (t : Real)).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
        (I0 : Fin (4 + 0) → Fin 3),
        HasDerivWithinAt
          (fun r : Real =>
            tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r 0 x)
              (fun i => basis i) I0)
          (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : Real) (0 + 2) x)
              + (e0Field (I := I) S (t : Real)) x)
            (fun i => basis i) I0)
          D.carrier (t : Real) := by
  refine ⟨e0Field (I := I) S (t : Real), e0Field_mem (I := I) S (t : Real), ?_⟩
  intro x basis horth I0
  haveI : NeZero (Module.finrank Real E) :=
    ⟨by have h : Module.finrank Real E = 3 := hdim x; omega⟩
  have htr : S.scalar (t : Real) x
      = sc (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j))) := by
    rw [scalar_eq_trace_ortho (I := I) S (t : Real) x horth]
    simp only [sc]

  have hlhs : (fun r : Real => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r 0 x)
        (fun i => basis i) I0)
      = (fun r : Real => S.base.rm04 r x (fun p => basis (I0 p))) := rfl

  have hval : tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
            (nablaKRm04Field (I := I) S (t : Real) (0 + 2) x) + (e0Field (I := I) S (t : Real)) x)
        (fun i => basis i) I0
      = tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
            (nablaKRm04Field (I := I) S (t : Real) 2 x)) (fun i => basis i) I0
        + e0Field (I := I) S (t : Real) x (fun p => basis (I0 p)) := rfl
  rw [hlhs, hval, e0Field_comp (I := I) S (t : Real) (hdim x) basis horth
    (fun i j => S.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j))) (fun i j => rfl) htr I0]
  exact hbase x basis horth I0

end DifferentialGeometry.PDE.RicciFlow
