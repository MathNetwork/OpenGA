import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.Lemma45F4
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ProductMFoldNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryComp
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false


















universe u

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











omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem comp_cov_le
    [FiniteDimensional Real E]
    {u : Set M} (hu : IsOpen u)
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ) (eps0 eps1 : Real)
    (heps0_0 : 0 ≤ eps0) (heps0_1 : eps0 ≤ 1) (heps1_0 : 0 ≤ eps1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
        (iterCov (I := I) g₁ 2 (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0)
    (hδ₀ : ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0)
    (hδ₁ : ∀ x ∈ u, ∀ k, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k) (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) :
    ∃ Cp : Real, 0 ≤ Cp ∧ ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
        (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * Cp := by
  classical
  obtain ⟨Cc, hCc0, hcorII⟩ :=
    lemma45_corII (I := I) hu g₀ g₁ δ₁ p eps0 heps0_0 heps0_1 hequiv hgK
  have hCp0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  refine ⟨Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)), hCp0, fun x hx r hr0 hrp => ?_⟩

  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON

  have hsplit : iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x =
      iterCov (I := I) g₀ 2 δ₀ r x + iterCov (I := I) g₀ 2 δ₁ r x := by
    rw [iterCov_add]
    rfl
  rw [hsplit]
  have htri := sqrt_normSq0S_add_le (I := I) g₀ (iterCov (I := I) g₀ 2 δ₀ r x)
    (iterCov (I := I) g₀ 2 δ₁ r x) basis hinv

  have ht0 := hδ₀ x hx r hr0 hrp

  have ht1 := hcorII x hx r hr0 hrp

  have hfac : Real.sqrt ((1 + eps0) ^ (2 + r)) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := by
    apply Real.sqrt_le_sqrt
    calc (1 + eps0) ^ (2 + r) ≤ (2 : Real) ^ (2 + r) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ (2 : Real) ^ (2 + p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfac0 : (0 : Real) ≤ Real.sqrt ((1 + eps0) ^ (2 + r)) := Real.sqrt_nonneg _
  have hsq0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := Real.sqrt_nonneg _

  have hlead : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
      (iterCov (I := I) g₁ 2 δ₁ r x)) ≤ eps1 := hδ₁ x hx r hrp

  have hsum : (∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x))) ≤ (r : Real) * eps1 := by
    have hb : ∀ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
          (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1 :=
      fun k hk => hδ₁ x hx k (le_trans (le_of_lt (Finset.mem_range.mp hk)) hrp)
    have h1 := Finset.sum_le_card_nsmul (Finset.range r) _ eps1 hb
    rwa [Finset.card_range, nsmul_eq_mul] at h1

  have hsum0 : (0 : Real) ≤ ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) :=
    Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hrp' : (r : Real) ≤ (p : Real) := by exact_mod_cast hrp
  have hCcS0 : (0 : Real) ≤ Cc * ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) := mul_nonneg hCc0 hsum0
  have hbracket :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
        (iterCov (I := I) g₁ 2 δ₁ r x)) +
        eps0 * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤
      eps1 * (1 + Cc * (p : Real)) := by
    nlinarith [hlead, mul_le_mul_of_nonneg_left hsum hCc0,
      mul_nonneg (sub_nonneg.mpr heps0_1) hCcS0,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrp' heps1_0) hCc0]

  have ht1' : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
      (iterCov (I := I) g₀ 2 δ₁ r x)) ≤
      Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) := by
    refine le_trans ht1 ?_
    refine le_trans (mul_le_mul_of_nonneg_left hbracket hfac0) ?_
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  refine le_trans htri ?_
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₀ r x)) +
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₁ r x))
      ≤ eps0 + Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) :=
        add_le_add ht0 ht1'
    _ = eps0 + eps1 * (Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real))) := by ring





theorem comp_cov_accum {C : Real} {e δ : Nat → Real}
    (h0 : e 0 ≤ C * δ 0)
    (hstep : ∀ k : Nat, e (k + 1) ≤ e k + C * δ (k + 1)) (n : Nat) :
    e n ≤ C * Finset.sum (Finset.range (n + 1)) (fun i => δ i) :=
  compEpsAccum h0 hstep n







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
theorem comp_cov_le_unif
    [FiniteDimensional Real E]
    (p : ℕ) :
    ∃ Cp : Real, 0 ≤ Cp ∧
      ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
        [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
        [IsManifold I 1 M'] [IsManifold I 2 M']
        [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
        {u : Set M'} (_ : IsOpen u)
        (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * Cp := by
  classical
  obtain ⟨Cc, hCc0, hcorII⟩ := lemma45_corII_unif (E := E) (H := H) (I := I) 2 p
  have hCp0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (by nlinarith [mul_nonneg hCc0 (Nat.cast_nonneg (α := ℝ) p)])
  refine ⟨Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)), hCp0, ?_⟩
  intro M' _ _ _ _ _ _ _ _ u hu g₀ g₁ δ₀ δ₁ eps0 eps1 heps0_0 heps0_1 heps1_0
    hequiv hgK hδ₀ hδ₁ x hx r hr0 hrp
  have hcorII' := hcorII hu g₀ g₁ δ₁ eps0 heps0_0 heps0_1 hequiv hgK

  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON

  have hsplit : iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x =
      iterCov (I := I) g₀ 2 δ₀ r x + iterCov (I := I) g₀ 2 δ₁ r x := by
    rw [iterCov_add]
    rfl
  rw [hsplit]
  have htri := sqrt_normSq0S_add_le (I := I) g₀ (iterCov (I := I) g₀ 2 δ₀ r x)
    (iterCov (I := I) g₀ 2 δ₁ r x) basis hinv

  have ht0 := hδ₀ x hx r hr0 hrp

  have ht1 := hcorII' x hx r hr0 hrp

  have hfac : Real.sqrt ((1 + eps0) ^ (2 + r)) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := by
    apply Real.sqrt_le_sqrt
    calc (1 + eps0) ^ (2 + r) ≤ (2 : Real) ^ (2 + r) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ (2 : Real) ^ (2 + p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfac0 : (0 : Real) ≤ Real.sqrt ((1 + eps0) ^ (2 + r)) := Real.sqrt_nonneg _
  have hsq0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := Real.sqrt_nonneg _

  have hlead : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
      (iterCov (I := I) g₁ 2 δ₁ r x)) ≤ eps1 := hδ₁ x hx r hrp

  have hsum : (∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x))) ≤ (r : Real) * eps1 := by
    have hb : ∀ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
          (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1 :=
      fun k hk => hδ₁ x hx k (le_trans (le_of_lt (Finset.mem_range.mp hk)) hrp)
    have h1 := Finset.sum_le_card_nsmul (Finset.range r) _ eps1 hb
    rwa [Finset.card_range, nsmul_eq_mul] at h1

  have hsum0 : (0 : Real) ≤ ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) :=
    Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hrp' : (r : Real) ≤ (p : Real) := by exact_mod_cast hrp
  have hCcS0 : (0 : Real) ≤ Cc * ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) := mul_nonneg hCc0 hsum0
  have hbracket :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
        (iterCov (I := I) g₁ 2 δ₁ r x)) +
        eps0 * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤
      eps1 * (1 + Cc * (p : Real)) := by
    nlinarith [hlead, mul_le_mul_of_nonneg_left hsum hCc0,
      mul_nonneg (sub_nonneg.mpr heps0_1) hCcS0,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrp' heps1_0) hCc0]

  have ht1' : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
      (iterCov (I := I) g₀ 2 δ₁ r x)) ≤
      Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) := by
    refine le_trans ht1 ?_
    refine le_trans (mul_le_mul_of_nonneg_left hbracket hfac0) ?_
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  refine le_trans htri ?_
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₀ r x)) +
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₁ r x))
      ≤ eps0 + Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) :=
        add_le_add ht0 ht1'
    _ = eps0 + eps1 * (Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real))) := by ring

end HCGCompactness
end DifferentialGeometry
