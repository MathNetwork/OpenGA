import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Curvature.QuadraticFormBound
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Metric.CompactMetricLowerBound

set_option autoImplicit false
set_option linter.style.longLine false












noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]





omit [SigmaCompactSpace M] in
theorem ricciFlow_metric_hasDerivAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S)
    {t : Real} (ht : t ∈ D.regular) (x : M) (v : TangentSpace I x) :
    HasDerivAt
      (fun s : Real => (S.family.metric s).inner x v v)
      ((-2 : Real) *
        S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
      t := by
  have hwithin := hS.equation ⟨t, ht⟩ x v v
  exact hwithin.hasDerivAt (D.regular_mem_nhds ht)






omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
theorem twoTensorQuadBound_of_unit_bound
    (K : Set M) (β ψ A : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T : forall _i : Nat, Real -> forall x : M,
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hA : 0 <= A)
    (hunit :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall u : TangentSpace I x, (gSeq i t).inner x u u = 1 ->
          |T i t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) u u)| <= A) :
    TwoTensorQuadBoundOnWindow (I := I) K β ψ gSeq T A :=
  ⟨hA, fun i t ht x hx v =>
    DifferentialGeometry.Integral.Connection.tensor02_quadForm_abs_le_of_unit_bound
      (gSeq i t) (T i t x) (fun u hu => hunit i t ht x hx u hu) v⟩







omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOn_of_quadFormDiff
    {K : Set M} {g h : SmoothRiemannianMetric I M} {δ : Real}
    (hδ0 : 0 <= δ) (hδ1 : δ < 1)
    (hdiff : forall x : M, x ∈ K -> forall v : TangentSpace I x,
      |h.inner x v v - g.inner x v v| <= δ * g.inner x v v) :
    MetricUniformEquivalentOn (I := I) K g h (1 - δ)⁻¹ := by
  have h1δ : (0 : Real) < 1 - δ := by linarith
  refine ⟨?_, ?_⟩
  · rw [le_inv_comm₀ (by norm_num) h1δ]; linarith
  · intro x hx v
    have hg0 : 0 <= g.inner x v v := by
      by_cases hv : v = 0
      · subst hv; simp
      · exact (g.pos x v hv).le
    have hd := hdiff x hx v
    rw [abs_le] at hd
    refine ⟨?_, ?_⟩
    · rw [inv_inv]; nlinarith [hd.1]
    · have hub : h.inner x v v <= (1 + δ) * g.inner x v v := by nlinarith [hd.2]
      have hfac : (1 + δ) <= (1 - δ)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ h1δ]; nlinarith
      calc h.inner x v v <= (1 + δ) * g.inner x v v := hub
        _ <= (1 - δ)⁻¹ * g.inner x v v := mul_le_mul_of_nonneg_right hfac hg0







omit [SigmaCompactSpace M] in
theorem metricQuadFormDiff_le_metricDerivNorm
    (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    |gk.inner x v v - gInf.inner x v v|
      <= (Module.finrank Real (TangentSpace I x) : Real)
          * metricDerivNorm (I := I) 0 gk gInf gRef x * gRef.inner x v v := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M; infer_instance
  have heval :
      metricDiffCovDerivAt (I := I) 0 gk gInf gRef x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)
        = gk.inner x v v - gInf.inner x v v := by
    show (metricCovDeriv (I := I) gk gRef 0 x - metricCovDeriv (I := I) gInf gRef 0 x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) = _
    have hk : metricCovDeriv (I := I) gk gRef 0 x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) = gk.inner x v v := by
      show Tensor0SBundle.metricTensorField (I := I) gk x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) = gk.inner x v v
      rw [Tensor0SBundle.metricTensorField_apply]
      simp [DifferentialGeometry.Integral.Connection.vec2]
    have hI : metricCovDeriv (I := I) gInf gRef 0 x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) = gInf.inner x v v := by
      show Tensor0SBundle.metricTensorField (I := I) gInf x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) = gInf.inner x v v
      rw [Tensor0SBundle.metricTensorField_apply]
      simp [DifferentialGeometry.Integral.Connection.vec2]
    calc
      (metricCovDeriv (I := I) gk gRef 0 x - metricCovDeriv (I := I) gInf gRef 0 x)
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) =
          metricCovDeriv (I := I) gk gRef 0 x
              (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) -
            metricCovDeriv (I := I) gInf gRef 0 x
              (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) :=
        Tensor0SBundle.Tensor0SSpace.sub_apply 2 x _ _ _
      _ = gk.inner x v v - gInf.inner x v v := by rw [hk, hI]
  have hbound :=
    DifferentialGeometry.Integral.Connection.tensor02_quadForm_abs_le_normSq0S
      (I := I) gRef (metricDiffCovDerivAt (I := I) 0 gk gInf gRef x) v
  rw [heval] at hbound
  rw [metricDerivNorm]
  exact hbound


omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metric_add_self (g : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g.inner x (a + b) (a + b)
      = g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
  have hs1 : g.inner x (a + b) (a + b)
      = g.inner x a (a + b) + g.inner x b (a + b) := by
    rw [(g.inner x).map_add]; rfl
  have hs2a : g.inner x a (a + b) = g.inner x a a + g.inner x a b := by
    rw [(g.inner x a).map_add]
  have hs2b : g.inner x b (a + b) = g.inner x b a + g.inner x b b := by
    rw [(g.inner x b).map_add]
  rw [hs1, hs2a, hs2b, g.symm x b a]; ring



omit [SigmaCompactSpace M] in
theorem metricDiffCovDerivAt_zero_apply
    (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    metricDiffCovDerivAt (I := I) 0 gk gInf gRef x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b)
      = gk.inner x a b - gInf.inner x a b := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M; infer_instance
  show (metricCovDeriv (I := I) gk gRef 0 x - metricCovDeriv (I := I) gInf gRef 0 x)
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) = _
  have hk : metricCovDeriv (I := I) gk gRef 0 x
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) = gk.inner x a b := by
    show Tensor0SBundle.metricTensorField (I := I) gk x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) = gk.inner x a b
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [DifferentialGeometry.Integral.Connection.vec2]
  have hI : metricCovDeriv (I := I) gInf gRef 0 x
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) = gInf.inner x a b := by
    show Tensor0SBundle.metricTensorField (I := I) gInf x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) = gInf.inner x a b
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [DifferentialGeometry.Integral.Connection.vec2]
  calc
    (metricCovDeriv (I := I) gk gRef 0 x - metricCovDeriv (I := I) gInf gRef 0 x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) =
        metricCovDeriv (I := I) gk gRef 0 x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) -
          metricCovDeriv (I := I) gInf gRef 0 x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) a b) :=
      Tensor0SBundle.Tensor0SSpace.sub_apply 2 x _ _ _
    _ = gk.inner x a b - gInf.inner x a b := by rw [hk, hI]



omit [SigmaCompactSpace M] in
theorem metricDiff_abs_le
    (gk gInf gRef : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    |gk.inner x v w - gInf.inner x v w| ≤
      metricDerivNorm (I := I) 0 gk gInf gRef x *
        Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
      (I := I) gRef x
  have hbound := Tensor0SBundle.abs_apply_le_sqrt_normSq0S
    (I := I) (g := gRef) (x := x) (s := 2) basis hON
    (metricDiffCovDerivAt (I := I) 0 gk gInf gRef x)
    (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w)
  rw [metricDiffCovDerivAt_zero_apply (I := I) gk gInf gRef x v w] at hbound
  rw [metricDerivNorm]
  refine hbound.trans_eq ?_
  rw [Fin.prod_univ_two]
  simp [DifferentialGeometry.Integral.Connection.vec2, mul_assoc]




omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricDiff_comp_le
    (gk gInf : SmoothRiemannianMetric I M) {C : Real} (hCge : (1 : Real) ≤ C)
    (y : M) {n : ℕ} (basis : Module.Basis (Fin n) Real (TangentSpace I y))
    (hON : ∀ i j : Fin n, gInf.inner y (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (hq : ∀ v : TangentSpace I y,
      |gk.inner y v v - gInf.inner y v v| <= (C - 1) * gInf.inner y v v)
    (i j : Fin n) :
    |gk.inner y (basis i) (basis j) - gInf.inner y (basis i) (basis j)| <= 4 * (C - 1) := by
  have hdiff : gk.inner y (basis i) (basis j) - gInf.inner y (basis i) (basis j)
      = ((gk.inner y (basis i + basis j) (basis i + basis j)
            - gInf.inner y (basis i + basis j) (basis i + basis j))
         - (gk.inner y (basis i) (basis i) - gInf.inner y (basis i) (basis i))
         - (gk.inner y (basis j) (basis j) - gInf.inner y (basis j) (basis j))) / 2 := by
    rw [metric_add_self gk y (basis i) (basis j),
      metric_add_self gInf y (basis i) (basis j)]; ring
  have hgii : gInf.inner y (basis i) (basis i) = 1 := by simpa using hON i i
  have hgjj : gInf.inner y (basis j) (basis j) = 1 := by simpa using hON j j
  have hgij_le : gInf.inner y (basis i + basis j) (basis i + basis j) <= 4 := by
    rw [metric_add_self gInf y (basis i) (basis j), hgii, hgjj]
    have hle1 : gInf.inner y (basis i) (basis j) <= 1 := by
      rw [hON i j]; split <;> norm_num
    linarith
  have hgij_nonneg : 0 <= gInf.inner y (basis i + basis j) (basis i + basis j) := by
    by_cases hab : basis i + basis j = 0
    · rw [hab]; simp
    · exact (gInf.pos y _ hab).le
  have hqij := hq (basis i + basis j)
  have hqi := hq (basis i)
  have hqj := hq (basis j)
  rw [hgii] at hqi
  rw [hgjj] at hqj
  rw [abs_le] at hqij hqi hqj
  have hC1 : 0 <= C - 1 := by linarith
  have hprod : (C - 1) * gInf.inner y (basis i + basis j) (basis i + basis j) <= (C - 1) * 4 :=
    mul_le_mul_of_nonneg_left hgij_le hC1
  rw [hdiff, hgii, hgjj, abs_le]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num : (0:Real) < 2)]
    nlinarith [hqij.1, hqij.2, hqi.1, hqi.2, hqj.1, hqj.2, hprod, hC1]
  · rw [div_le_iff₀ (by norm_num : (0:Real) < 2)]
    nlinarith [hqij.1, hqij.2, hqi.1, hqi.2, hqj.1, hqj.2, hprod, hC1]



omit [SigmaCompactSpace M] in
theorem metricDerivNorm_le_of_equiv
    (gk gInf : SmoothRiemannianMetric I M) {C : Real} (hCge : (1 : Real) ≤ C)
    (hbounds : ∀ (y : M) (v : TangentSpace I y),
      C⁻¹ * gInf.inner y v v ≤ gk.inner y v v ∧ gk.inner y v v ≤ C * gInf.inner y v v)
    (y : M) :
    metricDerivNorm (I := I) 0 gk gInf gInf y
      ≤ 4 * (Module.finrank Real (TangentSpace I y) : Real) * (C - 1) := by
  classical
  set nE : ℕ := Module.finrank Real (TangentSpace I y) with hnE
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) gInf y
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gInf y basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I y)))) := by
    have h := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) gInf basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hCge
  have hq : ∀ v : TangentSpace I y,
      |gk.inner y v v - gInf.inner y v v| <= (C - 1) * gInf.inner y v v := by
    intro v
    have hgnn : 0 <= gInf.inner y v v := by
      by_cases hv : v = 0
      · subst hv; simp
      · exact (gInf.pos y v hv).le
    obtain ⟨hlow, hhigh⟩ := hbounds y v
    have hCC : C⁻¹ * C = 1 := inv_mul_cancel₀ (ne_of_gt hCpos)
    have hinvnn : 0 <= C⁻¹ * gInf.inner y v v :=
      mul_nonneg (le_of_lt (inv_pos.mpr hCpos)) hgnn
    rw [abs_le]
    constructor <;> nlinarith [hlow, hhigh, hgnn, hCC, hinvnn, hCge, mul_nonneg hgnn hgnn]
  have hcomp := metricDiff_comp_le gk gInf hCge y basis hON hq
  have hnsq : Tensor0SBundle.normSq0S (I := I) gInf y 2
        (metricDiffCovDerivAt (I := I) 0 gk gInf gInf y)
      ≤ (nE : Real) ^ 2 * (4 * (C - 1)) ^ 2 := by
    rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gInf y 2 basis hinv _]
    have hterm : ∀ slots : Fin 2 → Fin nE,
        (Tensor0SBundle.component0S (I := I) basis
          (metricDiffCovDerivAt (I := I) 0 gk gInf gInf y) slots) ^ 2
          ≤ (4 * (C - 1)) ^ 2 := by
      intro slots
      have heq : Tensor0SBundle.component0S (I := I) basis
            (metricDiffCovDerivAt (I := I) 0 gk gInf gInf y) slots
          = gk.inner y (basis (slots 0)) (basis (slots 1))
            - gInf.inner y (basis (slots 0)) (basis (slots 1)) := by
        rw [Tensor0SBundle.component0S_apply]
        rw [show (fun a => basis (slots a))
            = DifferentialGeometry.Integral.Connection.vec2 (I := I)
                (basis (slots 0)) (basis (slots 1)) from by
          funext a; fin_cases a <;> rfl]
        exact metricDiffCovDerivAt_zero_apply gk gInf gInf y _ _
      rw [heq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcomp (slots 0) (slots 1)) 2
    calc ∑ slots : Fin 2 → Fin nE,
            (Tensor0SBundle.component0S (I := I) basis
              (metricDiffCovDerivAt (I := I) 0 gk gInf gInf y) slots) ^ 2
        ≤ ∑ _slots : Fin 2 → Fin nE, (4 * (C - 1)) ^ 2 :=
          Finset.sum_le_sum (fun slots _ => hterm slots)
      _ = (nE : Real) ^ 2 * (4 * (C - 1)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hCnn : 0 <= C - 1 := by linarith
  rw [metricDerivNorm]
  have hbnn : 0 <= 4 * (nE : Real) * (C - 1) := by positivity
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gInf y 2
          (metricDiffCovDerivAt (I := I) 0 gk gInf gInf y))
      ≤ Real.sqrt ((nE : Real) ^ 2 * (4 * (C - 1)) ^ 2) := Real.sqrt_le_sqrt hnsq
    _ = 4 * (nE : Real) * (C - 1) := by
        rw [show (nE : Real) ^ 2 * (4 * (C - 1)) ^ 2 = (4 * (nE : Real) * (C - 1)) ^ 2 from by ring,
          Real.sqrt_sq hbnn]






omit [SigmaCompactSpace M] in
theorem metricUniformEquivalentOn_of_metricDerivNorm
    {K : Set M} (gk gInf : SmoothRiemannianMetric I M) {δ : Real}
    (hδ0 : 0 <= δ) (hδ1 : δ < 1)
    (hsmall : forall x : M, x ∈ K ->
      (Module.finrank Real (TangentSpace I x) : Real)
        * metricDerivNorm (I := I) 0 gk gInf gInf x <= δ) :
    MetricUniformEquivalentOn (I := I) K gInf gk (1 - δ)⁻¹ := by
  refine metricUniformEquivalentOn_of_quadFormDiff hδ0 hδ1 ?_
  intro x hx v
  have hgnn : 0 <= gInf.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (gInf.pos x v hv).le
  calc |gk.inner x v v - gInf.inner x v v|
      <= (Module.finrank Real (TangentSpace I x) : Real)
          * metricDerivNorm (I := I) 0 gk gInf gInf x * gInf.inner x v v :=
        metricQuadFormDiff_le_metricDerivNorm gk gInf gInf x v
    _ <= δ * gInf.inner x v v :=
        mul_le_mul_of_nonneg_right (hsmall x hx) hgnn






omit [CompleteSpace E] in
theorem metricUniformEquivalentOn_of_compact [CompactSpace M]
    (gRef h : SmoothRiemannianMetric I M) :
    ∃ C : Real, MetricUniformEquivalentOn (I := I) Set.univ gRef h C := by
  obtain ⟨c, hc, hlow⟩ := DifferentialGeometry.metric_lower_bound_of_compact h gRef
  obtain ⟨c', hc', hup⟩ := DifferentialGeometry.metric_lower_bound_of_compact gRef h
  set C : Real := max (max c⁻¹ c'⁻¹) 1 with hCdef
  have hc_inv_le_C : c⁻¹ <= C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hc'_inv_le_C : c'⁻¹ <= C := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x _ v
  have hgnn : 0 <= gRef.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (gRef.pos x v hv).le
  refine ⟨?_, ?_⟩
  · have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hCinv_le_c : C⁻¹ <= c := by
      have h1 : 1 <= c * C := by
        have h2 := mul_le_mul_of_nonneg_left hc_inv_le_C hc.le
        rwa [mul_inv_cancel₀ (ne_of_gt hc)] at h2
      have h3 : C⁻¹ * C <= c * C := by
        rw [inv_mul_cancel₀ (ne_of_gt hC_pos)]; exact h1
      exact le_of_mul_le_mul_right h3 hC_pos
    calc C⁻¹ * gRef.inner x v v <= c * gRef.inner x v v :=
          mul_le_mul_of_nonneg_right hCinv_le_c hgnn
      _ <= h.inner x v v := hlow x v
  · have hub : h.inner x v v <= c'⁻¹ * gRef.inner x v v := by
      rw [inv_mul_eq_div, le_div_iff₀ hc']
      linarith [hup x v]
    calc h.inner x v v <= c'⁻¹ * gRef.inner x v v := hub
      _ <= C * gRef.inner x v v := mul_le_mul_of_nonneg_right hc'_inv_le_C hgnn




theorem metricDerivNorm_le_metricDerivNormSupOn [CompactSpace M]
    (gk gInf : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) 0 gk gInf gInf x
      <= metricDerivNormSupOn (I := I) Set.univ 0 gk gInf gInf := by
  obtain ⟨C, hC1, hCbounds⟩ := metricUniformEquivalentOn_of_compact gInf gk
  have hper : ∀ y : M, metricDerivNorm (I := I) 0 gk gInf gInf y
      <= 4 * (Module.finrank Real E : Real) * (C - 1) := fun y =>
    metricDerivNorm_le_of_equiv gk gInf hC1 (fun z v => hCbounds z (Set.mem_univ z) v) y
  have hbdd : BddAbove {r : Real | ∃ a : Nat, a <= 0 ∧
      ∃ z : M, z ∈ (Set.univ : Set M) ∧ metricDerivNorm (I := I) a gk gInf gInf z = r} := by
    refine ⟨4 * (Module.finrank Real E : Real) * (C - 1), ?_⟩
    rintro r ⟨a, ha, z, _, rfl⟩
    obtain rfl : a = 0 := Nat.le_zero.mp ha
    exact hper z
  exact le_csSup hbdd ⟨0, le_refl 0, x, Set.mem_univ x, rfl⟩








theorem exists_uniform_equiv_of_metricCPConv [CompactSpace M]
    (gSeq : Nat -> SmoothRiemannianMetric I M) (gInf : SmoothRiemannianMetric I M)
    (hconv : MetricCPConvOn (I := I) Set.univ isCompact_univ 0 gSeq gInf gInf) :
    ∃ C : Real, forall k : Nat,
      MetricUniformEquivalentOn (I := I) Set.univ gInf (gSeq k) C := by
  classical
  set n : Real := (Module.finrank Real E : Real) with hn
  have hn0 : 0 <= n := by rw [hn]; positivity
  set ε0 : Real := 1 / (2 * n + 2) with hε0def
  have hε0_pos : 0 < ε0 := by rw [hε0def]; positivity
  obtain ⟨k0, hk0⟩ := hconv ε0 hε0_pos
  have htail : forall k : Nat, k0 <= k ->
      MetricUniformEquivalentOn (I := I) Set.univ gInf (gSeq k) 2 := by
    intro k hk
    have hsup := hk0 k hk
    have h2eq : (2 : Real) = (1 - (1 / 2 : Real))⁻¹ := by norm_num
    rw [h2eq]
    refine metricUniformEquivalentOn_of_metricDerivNorm (gSeq k) gInf
      (by norm_num) (by norm_num) ?_
    intro x _
    have hfr : (Module.finrank Real (TangentSpace I x) : Real) = n := by rw [hn]; rfl
    rw [hfr]
    have hmd : metricDerivNorm (I := I) 0 (gSeq k) gInf gInf x <= ε0 :=
      le_trans (metricDerivNorm_le_metricDerivNormSupOn (gSeq k) gInf x) (le_of_lt hsup)
    calc n * metricDerivNorm (I := I) 0 (gSeq k) gInf gInf x
        <= n * ε0 := mul_le_mul_of_nonneg_left hmd hn0
      _ <= 1 / 2 := by rw [hε0def]; rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have hA : forall k : Nat, ∃ Ck : Real,
      MetricUniformEquivalentOn (I := I) Set.univ gInf (gSeq k) Ck := fun k =>
    metricUniformEquivalentOn_of_compact gInf (gSeq k)
  choose Cfun hCfun using hA
  have hCfun_nonneg : forall k : Nat, 0 <= Cfun k := fun k =>
    le_trans zero_le_one (hCfun k).1
  refine ⟨2 + ∑ k ∈ Finset.range k0, Cfun k, fun k => ?_⟩
  by_cases hk : k0 <= k
  · refine metricUniformEquivalentOn_of_le (htail k hk) ?_
    have : (0 : Real) <= ∑ k ∈ Finset.range k0, Cfun k :=
      Finset.sum_nonneg (fun j _ => hCfun_nonneg j)
    linarith
  · rw [not_le] at hk
    refine metricUniformEquivalentOn_of_le (hCfun k) ?_
    have hsum : Cfun k <= ∑ j ∈ Finset.range k0, Cfun j :=
      Finset.single_le_sum (fun j _ => hCfun_nonneg j) (Finset.mem_range.mpr hk)
    linarith



omit [SigmaCompactSpace M] in
theorem log_integrable_of_sol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) (t0 t : Real)
    (hsub : Set.uIcc t0 t ⊆ D.carrier) :
    IntervalIntegrable
      (fun s : Real =>
        ((-2 : Real) * S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) /
          (S.family.metric s).inner x v v)
      MeasureTheory.volume t0 t := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M; infer_instance
  apply ContinuousOn.intervalIntegrable
  have hnum : ContinuousOn
      (fun s : Real =>
        (-2 : Real) * S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
      (Set.uIcc t0 t) := by
    rw [continuousOn_iff_continuous_restrict]
    have hev := DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.eval_continuous
      (hA := hS.ricciCont) (P := {s : Real // s ∈ Set.uIcc t0 t})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun p => hsub p.2) continuous_const (v := fun _ _ => v) (fun _ => continuous_const)
    refine continuous_const.mul ?_
    refine hev.congr ?_
    intro p
    rw [show (fun _i : Fin 2 => v) = DifferentialGeometry.Integral.Connection.vec2 (I := I) v v from by
      funext i; fin_cases i <;> rfl]
    simp [DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt]
  have hden : ContinuousOn (fun s : Real => (S.family.metric s).inner x v v) (Set.uIcc t0 t) := by
    rw [continuousOn_iff_continuous_restrict]
    have hev := DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.eval_continuous
      (hA := DifferentialGeometry.Integral.Connection.metricTensor_cont_of_metricFamilySmoothOn
        S.family hS.smoothMetric)
      (P := {s : Real // s ∈ Set.uIcc t0 t})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun p => hsub p.2) continuous_const (v := fun _ _ => v) (fun _ => continuous_const)
    refine hev.congr ?_
    intro p
    simp only [Set.restrict]
    rw [Tensor0SBundle.metricTensorField_apply]
  exact hnum.div hden (fun s _ => ne_of_gt ((S.family.metric s).pos x v hv))

section FixedDomain

variable [SigmaCompactSpace M]







omit [SigmaCompactSpace M] in
theorem metricLogDerivativeInput_of_solutions
    [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 A : Real)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (hA : 0 <= A)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v)
    (hint :
      forall i : Nat, forall x : M, x ∈ K -> forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) *
                (S i).ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) /
                ((S i).family.metric s).inner x v v)
            MeasureTheory.volume t0 t) :
    MetricLogDerivativeInput (I := I) K β ψ t0
      (fun i s => (S i).family.metric s)
      (fun i t x => (S i).ricciAt t x) A where
  quad_bound := ⟨hA, fun i t ht x hx v => hquad i t ht x hx v⟩
  metric_deriv := fun i x _hx v _hv _t ht =>
    ricciFlow_metric_hasDerivAt (S i) (hS i) (hwin ht) x v
  log_integrable := fun i x hx v hv t ht => hint i x hx v hv t ht




omit [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_of_solutions
    [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hA : 0 <= A)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef ((S i).family.metric t0) C)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v)
    (hint :
      forall i : Nat, forall x : M, x ∈ K -> forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) *
                (S i).ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) /
                ((S i).family.metric s).inner x v v)
            MeasureTheory.volume t0 t) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i s => (S i).family.metric s)
      (fun t : Real => metricEquivalenceFactor C A t t0) :=
  metricUniformEquivalentOnWindow_of_logDerivativeInput (I := I) K β ψ t0 C A gRef
    (fun i s => (S i).family.metric s) (fun i t x => (S i).ricciAt t x)
    ht0 hC hequiv0
    (metricLogDerivativeInput_of_solutions (I := I) S hS K β ψ t0 A hwin hA hquad hint)






omit [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_of_solutions'
    [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hA : 0 <= A)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef ((S i).family.metric t0) C)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i s => (S i).family.metric s)
      (fun t : Real => metricEquivalenceFactor C A t t0) :=
  metricUniformEquivalentOnWindow_of_solutions S hS K β ψ t0 C A gRef hwin ht0 hC hA hequiv0 hquad
    (fun i _x _hx v hv t ht => log_integrable_of_sol (S i) (hS i) _x v hv t0 t
      ((Set.uIcc_subset_Icc ht0 ht).trans (hwin.trans D.regular_subset)))

end FixedDomain

end HCGCompactness
end DifferentialGeometry
