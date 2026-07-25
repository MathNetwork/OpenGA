import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000











noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open TensorMetricLowering Tensor0SNabla TensorRSNabla
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


noncomputable def lowerAllSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSSpace r s I x) : Tensor0SSpace (r + s) I x :=
  Tensor0SSpace.ofModel
    (lowerAllUpperIndices (I := I) (M := M) g r s x (TensorRSSpace.toModel A))




omit [InnerProductSpace ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem normSqRS_eq_normSq0S_lowerAllSpace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      normSq0S (I := I) g x (r + s) (lowerAllSpace g r s x A) := by
  classical
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x r s basis hinv A,
    normSq0S_identity_eq_sum_sq (I := I) g x (r + s) basis hinv (lowerAllSpace g r s x A)]
  unfold componentL2SqRS
  have hbij :
      (∑ slots : Fin (r + s) → Idx,
          component0S (I := I) basis (lowerAllSpace g r s x A) slots ^ 2) =
        ∑ up : Fin r → Idx, ∑ low : Fin s → Idx,
          component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append up low) ^ 2 := by
    rw [show (∑ up : Fin r → Idx, ∑ low : Fin s → Idx,
            component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append up low) ^ 2)
          = ∑ p : (Fin r → Idx) × (Fin s → Idx),
            component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append p.1 p.2) ^ 2 from
      (Fintype.sum_prod_type (fun p : (Fin r → Idx) × (Fin s → Idx) =>
        component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append p.1 p.2) ^ 2)).symm]
    refine Fintype.sum_equiv
      { toFun := fun slots => (fun i => slots (Fin.castAdd s i), fun j => slots (Fin.natAdd r j))
        invFun := fun p => Fin.append p.1 p.2
        left_inv := fun slots => by
          funext k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · simp [Fin.append_left]
          · simp [Fin.append_right]
        right_inv := fun p => by
          refine Prod.ext ?_ ?_
          · funext i; simp [Fin.append_left]
          · funext j; simp [Fin.append_right] } _ _ ?_
    intro slots
    refine congrArg (fun t => component0S (I := I) basis (lowerAllSpace g r s x A) t ^ 2) ?_
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  rw [hbij]
  refine Finset.sum_congr rfl fun up _ => Finset.sum_congr rfl fun low _ => ?_
  congr 1


  have hgram : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have hsum : (∑ k : Idx, identityInvMetric (Idx := Idx) i k * g.inner x (basis k) (basis j))
        = g.inner x (basis i) (basis j) := by
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro k _ hk
        rw [show identityInvMetric (Idx := Idx) i k = 0 from
          diagonalInvMetric_eq_zero_of_ne (Ne.symm hk), zero_mul]
      · intro hni; exact absurd (Finset.mem_univ i) hni
    rw [← hsum]; exact (hinv i j).1

  have hsep : separableFormAt (I := I) (M := M) g x r (fun i => basis (up i)) =
      basisTensor0S (I := I) basis up := by
    apply ext0S_basis (I := I) basis
    intro jdx
    rw [basisTensor0S_component]
    change (∏ i : Fin r, g.inner x (basis (up i)) (basis (jdx i))) = if up = jdx then (1 : Real) else 0
    rw [Finset.prod_congr rfl (fun i _ => hgram (up i) (jdx i))]
    by_cases h : up = jdx
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)


  rw [componentRS_apply_gen, component0S_apply]
  unfold lowerAllSpace
  rw [show (Tensor0SSpace.ofModel
        (lowerAllUpperIndices (I := I) (M := M) g r s x (TensorRSSpace.toModel A)))
        (fun a => basis (Fin.append up low a))
      = lowerAllUpperIndices (I := I) (M := M) g r s x (TensorRSSpace.toModel A)
        (fun a => basis (Fin.append up low a)) from rfl]
  rw [lowerAllUpperIndices_apply]
  simp only [Fin.append_left, Fin.append_right]
  rw [hsep]
  rfl

end Connection
end Integral
end DifferentialGeometry
