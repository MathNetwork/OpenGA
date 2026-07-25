import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false























noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]









omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem lemma45_cor_II_of_intrinsic
    (g gRef : SmoothRiemannianMetric I M) {q₂ : ℕ}
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) {x : M} {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * gRef.inner x v v)
    (eps Cc : Real) (heps0 : 0 ≤ eps) (hCc0 : 0 ≤ Cc)
    (hF3 : ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
        eps * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))) :
    ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt (C ^ (q₂ + r)) *
          (Real.sqrt (normSq0S (I := I) gRef x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
            eps * Cc * ∑ k ∈ Finset.range r,
              Real.sqrt (normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  intro r hr0 hrp
  classical
  have hC0 : (0 : Real) ≤ C := le_trans zero_le_one hC

  have hFr0 : (0 : Real) ≤ Real.sqrt (C ^ (q₂ + r)) := Real.sqrt_nonneg _

  have hconv : ∀ k : ℕ, k ≤ r →
      Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) ≤
        Real.sqrt (C ^ (q₂ + r)) *
          Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    intro k hk
    have hbase := sqrt_normSq0S_le_of_metric_equiv (I := I) gRef g x (q₂ + k) hC hequiv
      (iterCov (I := I) gRef q₂ T k x)

    have hpow : C ^ (q₂ + k) ≤ C ^ (q₂ + r) := pow_le_pow_right₀ hC (by omega)
    have hfac : Real.sqrt (C ^ (q₂ + k)) ≤ Real.sqrt (C ^ (q₂ + r)) := Real.sqrt_le_sqrt hpow
    have hgRefnn : (0 : Real) ≤
        Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) :=
      Real.sqrt_nonneg _
    calc Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))
        ≤ Real.sqrt (C ^ (q₂ + k)) *
            Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := hbase
      _ ≤ Real.sqrt (C ^ (q₂ + r)) *
            Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) :=
          mul_le_mul_of_nonneg_right hfac hgRefnn

  have hlead := hconv r le_rfl
  have hsum : (∑ k ∈ Finset.range r,
        Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))) ≤
      Real.sqrt (C ^ (q₂ + r)) * ∑ k ∈ Finset.range r,
        Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hconv k (le_of_lt (Finset.mem_range.mp hk))

  have hsum0 : (0 : Real) ≤ eps * Cc := mul_nonneg heps0 hCc0
  have hrhs :
      Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
        eps * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) ≤
      Real.sqrt (C ^ (q₂ + r)) *
        (Real.sqrt (normSq0S (I := I) gRef x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
          eps * Cc * ∑ k ∈ Finset.range r,
            Real.sqrt (normSq0S (I := I) gRef x (q₂ + k)
              (iterCov (I := I) gRef q₂ T k x))) := by
    have hmulsum : eps * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) ≤
        eps * Cc * (Real.sqrt (C ^ (q₂ + r)) * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))) :=
      mul_le_mul_of_nonneg_left hsum hsum0
    rw [mul_add]
    nlinarith [hlead, hmulsum, hFr0, hsum0]
  exact le_trans (hF3 r hr0 hrp) hrhs

end HCGCompactness
end DifferentialGeometry
