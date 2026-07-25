import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option linter.style.longLine false































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection



theorem sqrt_sum_sq_add_le {ι : Type*} [Fintype ι] (a b : ι → Real) :
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤
      Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2) := by
  have hA : 0 ≤ ∑ i, (a i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, (b i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (b i) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    have h2 : Real.sqrt ((∑ i, a i * b i) ^ 2)
        ≤ Real.sqrt ((∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2)) := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hA] at h2
    exact le_trans (le_abs_self _) h2
  have hexpand : ∑ i, (a i + b i) ^ 2
      = (∑ i, (a i) ^ 2) + 2 * (∑ i, a i * b i) + ∑ i, (b i) ^ 2 := by
    have hpt : ∀ i, (a i + b i) ^ 2 = (a i) ^ 2 + 2 * (a i * b i) + (b i) ^ 2 :=
      fun i => by ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hle : ∑ i, (a i + b i) ^ 2
      ≤ (Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2)) ^ 2 := by
    rw [hexpand, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
    nlinarith [hcs]
  calc Real.sqrt (∑ i, (a i + b i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2) :=
        Real.sqrt_sq (by positivity)






theorem sqrt_sum_sq_sub_le_of_hasDerivAt {ι : Type*} [Fintype ι] {β ψ L : Real}
    (c c' : ι → Real → Real)
    (hderiv : ∀ i : ι, ∀ r ∈ Set.Icc β ψ, HasDerivAt (c i) (c' i r) r)
    (hbnd : ∀ r ∈ Set.Icc β ψ, Real.sqrt (∑ i, (c' i r) ^ 2) ≤ L)
    {s t : Real} (hs : s ∈ Set.Icc β ψ) (ht : t ∈ Set.Icc β ψ) :
    Real.sqrt (∑ i, (c i s - c i t) ^ 2) ≤ L * |s - t| := by
  classical
  set e := PiLp.continuousLinearEquiv 2 Real (fun _ : ι => Real) with he
  set f : Real → EuclideanSpace Real ι := fun r => e.symm (fun i => c i r) with hf
  set f' : Real → EuclideanSpace Real ι := fun r => e.symm (fun i => c' i r) with hf'
  have hnorm : ∀ d : ι → Real,
      ‖(e.symm d : EuclideanSpace Real ι)‖ = Real.sqrt (∑ i, (d i) ^ 2) := by
    intro d
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [he, PiLp.continuousLinearEquiv_symm_apply, Real.norm_eq_abs, sq_abs]
  have hderivf : ∀ r ∈ Set.Icc β ψ, HasDerivAt f (f' r) r := by
    intro r hr
    have hg : HasDerivAt (fun ρ : Real => (fun i => c i ρ : ι → Real))
        (fun i => c' i r) r := by
      rw [hasDerivAt_pi]
      intro i
      exact hderiv i r hr
    exact (e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hg)
  have hnf' : ∀ r ∈ Set.Icc β ψ, ‖f' r‖ ≤ L := by
    intro r hr
    rw [hf', hnorm]
    exact hbnd r hr
  have hmvt : ‖f s - f t‖ ≤ L * ‖s - t‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hderivf r hr).hasDerivWithinAt)
      (fun r hr => hnf' r hr) (convex_Icc β ψ) ht hs
  have hfst : f s - f t = e.symm (fun i => c i s - c i t) := by
    simp only [hf, ← map_sub]
    congr 1
  rw [hfst, hnorm] at hmvt
  rwa [← Real.norm_eq_abs (s - t)]

noncomputable section ManifoldSection

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]




omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem sqrtNormSq0S_add_le
    (gRef : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (u w : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s (u + w)) ≤
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s u) +
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s w) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i' j'
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i' j'
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv u,
    Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv w,
    Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv (u + w)]
  have hcomp : ∀ slots : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      Tensor0SBundle.component0S (I := I) basis (u + w) slots
        = Tensor0SBundle.component0S (I := I) basis u slots
          + Tensor0SBundle.component0S (I := I) basis w slots :=
    fun slots => rfl
  simp_rw [hcomp]
  exact sqrt_sum_sq_add_le _ _




omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_triangle
    (a : Nat) (A B C gRef : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) a A C gRef x ≤
      metricDerivNorm (I := I) a A B gRef x + metricDerivNorm (I := I) a B C gRef x := by
  simp only [metricDerivNorm, metricDiffCovDerivAt]
  have htel : metricCovDeriv (I := I) A gRef a x - metricCovDeriv (I := I) C gRef a x
      = (metricCovDeriv (I := I) A gRef a x - metricCovDeriv (I := I) B gRef a x)
        + (metricCovDeriv (I := I) B gRef a x - metricCovDeriv (I := I) C gRef a x) :=
    (sub_add_sub_cancel _ _ _).symm
  rw [htel]
  exact sqrtNormSq0S_add_le (I := I) gRef x (a + 2) _ _


omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricDerivNormSupOn_le_of_forall
    (K : Set M) (p : Nat) (gk gInf gRef : SmoothRiemannianMetric I M)
    (c : Real) (hc : 0 ≤ c)
    (h : ∀ a : Nat, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a gk gInf gRef x ≤ c) :
    metricDerivNormSupOn (I := I) K p gk gInf gRef ≤ c := by
  apply Real.sSup_le _ hc
  rintro r ⟨a, hap, x, hxK, rfl⟩
  exact h a hap x hxK











omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem timeLipschitz_of_hasDerivAt
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (g : Real → SmoothRiemannianMetric I M)
    (Ev : Real → (x : M) → Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 2) x)
    (K : Set M) (β ψ : Real) (L : Real)
    (hev : ∀ x ∈ K, ∀ s ∈ Set.Icc β ψ, ∀ v : Fin (a + 2) → TangentSpace I x,
      HasDerivAt (fun r : Real => metricCovDeriv (I := I) (g r) gRef a x v)
        (Ev s x v) s)
    (hbound : ∀ x ∈ K, ∀ s ∈ Set.Icc β ψ,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2) (Ev s x)) ≤ L) :
    ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
      metricDerivNorm (I := I) a (g s) (g t) gRef x ≤ L * |s - t| := by
  classical
  intro s hs t ht x hxK
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i' j'
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i' j'
  set c : (Fin (a + 2) → Fin (Module.finrank Real (TangentSpace I x))) → Real → Real :=
    fun slots r => Tensor0SBundle.component0S (I := I) basis
      (metricCovDeriv (I := I) (g r) gRef a x) slots with hc
  set c' : (Fin (a + 2) → Fin (Module.finrank Real (TangentSpace I x))) → Real → Real :=
    fun slots r => Tensor0SBundle.component0S (I := I) basis (Ev r x) slots with hc'
  have hderiv : ∀ slots, ∀ r ∈ Set.Icc β ψ, HasDerivAt (c slots) (c' slots r) r := by
    intro slots r hr
    have hh := hev x hxK r hr (fun q => basis (slots q))
    simpa [hc, hc', Tensor0SBundle.component0S_apply] using hh
  have hbnd : ∀ r ∈ Set.Icc β ψ,
      Real.sqrt (∑ slots, (c' slots r) ^ 2) ≤ L := by
    intro r hr
    have hsum : (∑ slots, (c' slots r) ^ 2)
        = Tensor0SBundle.normSq0S (I := I) gRef x (a + 2) (Ev r x) := by
      rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (a + 2) basis hinv (Ev r x)]
    rw [hsum]
    exact hbound x hxK r hr
  have hkey := sqrt_sum_sq_sub_le_of_hasDerivAt c c' hderiv hbnd hs ht
  have hmd : metricDerivNorm (I := I) a (g s) (g t) gRef x
      = Real.sqrt (∑ slots, (c slots s - c slots t) ^ 2) := by
    rw [metricDerivNorm, metricDiffCovDerivAt,
      Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (a + 2) basis hinv]
    congr 1
  rw [hmd]
  exact hkey








omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem windowPreconv
    (K : Set M) (β ψ : Real) (p : Nat)
    (gSeq : Nat → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (L : Real) (hL : 0 ≤ L)
    (hgLip : ∀ k : Nat, ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x ≤ L * |s - t|)
    (hInfLip : ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x ≤ L * |s - t|)
    (S : Set Real)
    (hdense : ∀ t ∈ Set.Icc β ψ, ∀ δ : Real, 0 < δ →
      ∃ τ, τ ∈ S ∧ τ ∈ Set.Icc β ψ ∧ |t - τ| < δ)
    (hconv : ∀ τ ∈ S, τ ∈ Set.Icc β ψ → ∀ ε : Real, 0 < ε →
      ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ a : Nat, a ≤ p → ∀ x ∈ K,
        metricDerivNorm (I := I) a (gSeq k τ) (gInf τ) gRef x < ε) :
    ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
      metricDerivNormSupOn (I := I) K p (gSeq k t) (gInf t) gRef < ε := by
  intro ε hε
  have hLpos : (0 : Real) < L + 1 := by linarith
  set δ : Real := ε / (3 * (L + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity

  have hcover : Set.Icc β ψ ⊆ ⋃ τ : {τ : Real // τ ∈ S ∧ τ ∈ Set.Icc β ψ},
      Metric.ball (τ : Real) δ := by
    intro t ht
    obtain ⟨τ, hτS, hτIcc, hτd⟩ := hdense t ht δ hδpos
    refine Set.mem_iUnion.2 ⟨⟨τ, hτS, hτIcc⟩, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hτd
  obtain ⟨F, hF⟩ := (isCompact_Icc (a := β) (b := ψ)).elim_finite_subcover
    (fun τ : {τ : Real // τ ∈ S ∧ τ ∈ Set.Icc β ψ} => Metric.ball (τ : Real) δ)
    (fun _ => Metric.isOpen_ball) hcover

  have hk0 : ∀ τ : {τ : Real // τ ∈ S ∧ τ ∈ Set.Icc β ψ},
      ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ a : Nat, a ≤ p → ∀ x ∈ K,
        metricDerivNorm (I := I) a (gSeq k (τ : Real)) (gInf (τ : Real)) gRef x < ε / 3 :=
    fun τ => hconv (τ : Real) τ.2.1 τ.2.2 (ε / 3) (by positivity)
  choose k0fun hk0fun using hk0
  refine ⟨F.sup k0fun, fun k hk t ht => ?_⟩
  set c : Real := 2 * L * δ + ε / 3 with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  have hc_lt : c < ε := by
    have hstep : 2 * L * δ < 2 * (L + 1) * δ := by nlinarith [hδpos]
    have heq : 2 * (L + 1) * δ = 2 * ε / 3 := by
      rw [hδdef]; field_simp
    rw [hcdef]; rw [heq] at hstep; linarith
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p (gSeq k t) (gInf t) gRef c hcnn ?_) hc_lt
  intro a hap x hxK

  obtain ⟨τ, hτF, htτ⟩ := Set.mem_iUnion₂.1 (hF ht)
  have hdist : |t - (τ : Real)| < δ := by
    rw [Metric.mem_ball, Real.dist_eq] at htτ; exact htτ

  have h1 : metricDerivNorm (I := I) a (gSeq k t) (gSeq k (τ : Real)) gRef x ≤ L * |t - (τ : Real)| :=
    hgLip k t ht (τ : Real) τ.2.2 a hap x hxK
  have h3 : metricDerivNorm (I := I) a (gInf (τ : Real)) (gInf t) gRef x ≤ L * |t - (τ : Real)| := by
    have := hInfLip (τ : Real) τ.2.2 t ht a hap x hxK
    rwa [abs_sub_comm] at this
  have h2 : metricDerivNorm (I := I) a (gSeq k (τ : Real)) (gInf (τ : Real)) gRef x < ε / 3 :=
    hk0fun τ k (le_trans (Finset.le_sup hτF) hk) a hap x hxK
  have htri : metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x ≤
      metricDerivNorm (I := I) a (gSeq k t) (gSeq k (τ : Real)) gRef x
      + (metricDerivNorm (I := I) a (gSeq k (τ : Real)) (gInf (τ : Real)) gRef x
        + metricDerivNorm (I := I) a (gInf (τ : Real)) (gInf t) gRef x) := by
    refine le_trans
      (metricDerivNorm_triangle (I := I) a (gSeq k t) (gSeq k (τ : Real)) (gInf t) gRef x) ?_
    have := metricDerivNorm_triangle (I := I) a (gSeq k (τ : Real)) (gInf (τ : Real)) (gInf t) gRef x
    linarith
  have hδbound : L * |t - (τ : Real)| ≤ L * δ := mul_le_mul_of_nonneg_left hdist.le hL
  nlinarith [htri, h1, h2, h3, hδbound, hcdef.ge]

end ManifoldSection

end HCGCompactness
end DifferentialGeometry
