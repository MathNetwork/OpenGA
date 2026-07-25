import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowGInf
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBoundsFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity

set_option autoImplicit false
set_option linter.style.longLine false






















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv
open Filter Topology
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]



omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metric_ext_inner
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (h : forall x : M, g₁.inner x = g₂.inner x) :
    g₁ = g₂ := by
  cases g₁; cases g₂
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x; exact h x





omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricInnerApply_diff_le
    (A B gRef : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |A.inner x v w - B.inner x v w|
      <= (Module.finrank Real (TangentSpace I x) : Real)
          * metricDerivNorm (I := I) 0 A B gRef x
          * (gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w) := by
  classical
  set n : Real := (Module.finrank Real (TangentSpace I x) : Real) with hn
  set D := metricDiffCovDerivAt (I := I) 0 A B gRef x with hD

  have hsymmA : A.inner x v w = A.inner x w v := A.symm x v w
  have hsymmB : B.inner x v w = B.inner x w v := B.symm x v w
  have hpol : A.inner x v w - B.inner x v w
      = ((A.inner x (v + w) (v + w) - B.inner x (v + w) (v + w))
         - (A.inner x v v - B.inner x v v)
         - (A.inner x w w - B.inner x w w)) / 2 := by
    rw [metric_add_self A x v w, metric_add_self B x v w]; rw [hsymmA, hsymmB]; ring

  have hqf : forall u : TangentSpace I x,
      |A.inner x u u - B.inner x u u|
        <= n * metricDerivNorm (I := I) 0 A B gRef x * gRef.inner x u u := fun u =>
    metricQuadFormDiff_le_metricDerivNorm (I := I) A B gRef x u
  have hvw := hqf (v + w)
  have hv := hqf v
  have hw := hqf w
  have hmn : 0 <= n := by rw [hn]; positivity
  have hmd : 0 <= metricDerivNorm (I := I) 0 A B gRef x := Real.sqrt_nonneg _
  have hgnn : forall u : TangentSpace I x, 0 <= gRef.inner x u u := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp
    · exact (gRef.pos x u hu).le
  rw [hpol, abs_div, abs_of_pos (by norm_num : (0:Real) < 2)]
  rw [div_le_iff₀ (by norm_num : (0:Real) < 2)]
  set p1 := A.inner x (v + w) (v + w) - B.inner x (v + w) (v + w) with hp1
  set p2 := A.inner x v v - B.inner x v v with hp2
  set p3 := A.inner x w w - B.inner x w w with hp3
  have htri : |p1 - p2 - p3| <= |p1| + |p2| + |p3| := by
    have h1 := abs_add_le (p1 - p2) (-p3)
    have h2 := abs_add_le p1 (-p2)
    simp only [abs_neg, sub_eq_add_neg] at h1 h2 ⊢
    linarith [h1, h2]
  nlinarith [htri, hvw, hv, hw, hmn, hmd, hgnn (v + w), hgnn v, hgnn w,
    mul_nonneg (mul_nonneg hmn hmd) (hgnn v),
    mul_nonneg (mul_nonneg hmn hmd) (hgnn w),
    mul_nonneg (mul_nonneg hmn hmd) (hgnn (v + w))]



omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCInf_inner
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef)
    (x : M) (v w : TangentSpace I x) :
    Tendsto (fun k => (gSeq k).inner x v w) atTop (nhds (gInf.inner x v w)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let n : ℝ := Module.finrank ℝ (TangentSpace I x)
  let S : ℝ := gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hS : 0 ≤ S := by
    have hnonneg : ∀ z : TangentSpace I x, 0 ≤ gRef.inner x z z := by
      intro z
      by_cases hz : z = 0
      · subst hz
        simp
      · exact (gRef.pos x z hz).le
    dsimp only [S]
    linarith [hnonneg (v + w), hnonneg v, hnonneg w]
  have hden : 0 < n * S + 1 := by positivity
  obtain ⟨k₀, hk₀⟩ := hconv {x} isCompact_singleton 0 (ε / (n * S + 1)) (by positivity)
  refine ⟨k₀, fun k hk => ?_⟩
  have hpoint : metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x <
      ε / (n * S + 1) := lt_of_le_of_lt
    (derivNorm_le_sup (I := I) isCompact_singleton le_rfl
      (gSeq k) gInf gRef (Set.mem_singleton x))
    (hk₀ k hk)
  have hbound := metricInnerApply_diff_le (I := I) (gSeq k) gInf gRef x v w
  change |(gSeq k).inner x v w - gInf.inner x v w| ≤
    n * metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x * S at hbound
  rw [Real.dist_eq]
  have hprod : n * metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x * S ≤
      (n * S) * (ε / (n * S + 1)) := by
    have hnorm : 0 ≤ metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x :=
      Real.sqrt_nonneg _
    nlinarith [hpoint.le, mul_nonneg hn hS]
  have hfrac : (n * S) * (ε / (n * S + 1)) < ε := by
    have hid : (n * S) * (ε / (n * S + 1)) = (n * S) * ε / (n * S + 1) := by
      rw [mul_div_assoc]
    rw [hid, div_lt_iff₀ hden]
    nlinarith [hε, mul_nonneg hn hS]
  exact lt_of_le_of_lt (le_trans hbound hprod) hfrac



omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCInf_unique
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (A B gRefA gRefB : SmoothRiemannianMetric I M)
    (hA : MetricCInfConvOnCompacts (I := I) gSeq A gRefA)
    (hB : MetricCInfConvOnCompacts (I := I) gSeq B gRefB) : A = B := by
  refine metric_ext_inner A B fun x => ?_
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  exact tendsto_nhds_unique
    (metricCInf_inner (I := I) gSeq A gRefA hA x v w)
    (metricCInf_inner (I := I) gSeq B gRefB hB x v w)




omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricInner_cauchy
    (gk : Nat -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x)
    (hcauchy : forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall m : Nat, k0 <= m -> forall l : Nat, k0 <= l ->
        metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x < eps) :
    CauchySeq (fun k => (gk k).inner x v w) := by
  set n : Real := (Module.finrank Real (TangentSpace I x) : Real) with hn
  set S : Real := gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w with hS
  have hSnn : 0 <= S := by
    rw [hS]
    have hgnn : forall u : TangentSpace I x, 0 <= gRef.inner x u u := by
      intro u
      by_cases hu : u = 0
      · subst hu; simp
      · exact (gRef.pos x u hu).le
    have := hgnn (v + w); have := hgnn v; have := hgnn w; linarith
  have hnnn : 0 <= n := by rw [hn]; positivity
  rw [Metric.cauchySeq_iff]
  intro eps heps

  obtain ⟨k0, hk0⟩ := hcauchy (eps / (n * S + 1)) (by positivity)
  refine ⟨k0, fun m hm l hl => ?_⟩
  rw [Real.dist_eq]
  have hbound : |(gk m).inner x v w - (gk l).inner x v w|
      <= n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S := by
    have h := metricInnerApply_diff_le (I := I) (gk m) (gk l) gRef x v w
    rw [← hn, ← hS] at h
    exact h
  have hmd : metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x < eps / (n * S + 1) :=
    hk0 m hm l hl
  have hmdnn : 0 <= metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x := Real.sqrt_nonneg _
  have hdenpos : 0 < n * S + 1 := by positivity

  have hkey : n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S <
      eps := by
    have hprod : n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S
        <= (n * S) * (eps / (n * S + 1)) := by
      have h1 : metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x
          <= eps / (n * S + 1) := hmd.le
      nlinarith [h1, hnnn, hmdnn, hSnn, mul_nonneg hnnn hSnn]
    have hfrac : (n * S) * (eps / (n * S + 1)) < eps := by
      have hid : (n * S) * (eps / (n * S + 1)) = (n * S) * eps / (n * S + 1) := by
        rw [mul_div_assoc]
      rw [hid, div_lt_iff₀ hdenpos]
      nlinarith [heps, mul_nonneg hnnn hSnn]
    linarith
  calc |(gk m).inner x v w - (gk l).inner x v w|
      <= n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S := hbound
    _ < eps := hkey





omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metricLimit_uniq
    (gk : Nat -> SmoothRiemannianMetric I M) (A B : SmoothRiemannianMetric I M)
    (hcauchy : forall x : M, forall v w : TangentSpace I x,
      CauchySeq (fun k => (gk k).inner x v w))
    (psiA : Nat -> Nat) (hpsiA : StrictMono psiA)
    (psiB : Nat -> Nat) (hpsiB : StrictMono psiB)
    (hA : forall x : M, Filter.Tendsto (fun m => (gk (psiA m)).inner x) Filter.atTop
      (nhds (A.inner x)))
    (hB : forall x : M, Filter.Tendsto (fun m => (gk (psiB m)).inner x) Filter.atTop
      (nhds (B.inner x))) :
    A = B := by
  refine metric_ext_inner A B fun x => ?_
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_

  have hAvw : Filter.Tendsto (fun m => (gk (psiA m)).inner x v w) Filter.atTop
      (nhds (A.inner x v w)) := by
    have hc : Continuous fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
        T v w :=
      (ContinuousLinearMap.apply Real Real w).continuous.comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) v).continuous
    exact (hc.tendsto _).comp (hA x)
  have hBvw : Filter.Tendsto (fun m => (gk (psiB m)).inner x v w) Filter.atTop
      (nhds (B.inner x v w)) := by
    have hc : Continuous fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
        T v w :=
      (ContinuousLinearMap.apply Real Real w).continuous.comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) v).continuous
    exact (hc.tendsto _).comp (hB x)

  have hfullA : Filter.Tendsto (fun k => (gk k).inner x v w) Filter.atTop
      (nhds (A.inner x v w)) :=
    tendsto_nhds_of_cauchySeq_of_subseq (hcauchy x v w) hpsiA.tendsto_atTop hAvw
  have hfullB : Filter.Tendsto (fun k => (gk k).inner x v w) Filter.atTop
      (nhds (B.inner x v w)) :=
    tendsto_nhds_of_cauchySeq_of_subseq (hcauchy x v w) hpsiB.tendsto_atTop hBvw
  exact tendsto_nhds_unique hfullA hfullB









theorem windowGInfPt (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hbdd : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) t) gRef z <= C)
    (hlow : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) t).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gInf : Real -> SmoothRiemannianMetric I M,
        (forall t, t ∈ Set.Icc beta psiT -> exists psi : Nat -> Nat, StrictMono psi /\
          forall x : M, Filter.Tendsto (fun m => (gSeq (phi (psi m)) t).inner x)
            Filter.atTop (nhds ((gInf t).inner x))) /\
        (forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t, t ∈ Set.Icc beta psiT -> forall a : Nat, a <= p -> forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps) := by
  classical
  obtain ⟨phi, hphi, gNet, _hnetInner, hnetNorm⟩ :=
    netFullDiag (I := I) hne K hK p gRef gSeq e
      (fun n rho hrho q K' hK' => hbdd rho hrho (e n) (he n) q K' hK')
      (fun n rho hrho => hlow rho hrho (e n) (he n))
  have htime : forall t, t ∈ Set.Icc beta psiT ->
      exists psi : Nat -> Nat, StrictMono psi /\
        exists gT : SmoothRiemannianMetric I M,
          (forall x : M, Filter.Tendsto (fun m => (gSeq (phi (psi m)) t).inner x)
            Filter.atTop (nhds (gT.inner x))) /\
          forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall a : Nat, a <= p -> forall x, x ∈ K ->
              metricDerivNorm (I := I) a (gSeq (phi (psi k)) t) gT gRef x < eps := by
    intro t ht
    obtain ⟨psi, hpsi, gT, hinner, hnorm⟩ :=
      metricPreconvFull (I := I) hne K hK p gRef (fun k => gSeq (phi k) t)
        (hbdd phi hphi t ht) (hlow phi hphi t ht)
    refine ⟨psi, hpsi, gT, ?_, ?_⟩
    · intro x
      simpa only [Function.comp_apply] using hinner x
    · intro eps heps
      obtain ⟨k0, hk0⟩ := hnorm eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩
  let psiAt : (t : Real) -> t ∈ Set.Icc beta psiT -> Nat -> Nat :=
    fun t ht => Classical.choose (htime t ht)
  have hpsiAt : forall t ht, StrictMono (psiAt t ht) := by
    intro t ht
    exact (Classical.choose_spec (htime t ht)).1
  let gAt : (t : Real) -> t ∈ Set.Icc beta psiT -> SmoothRiemannianMetric I M :=
    fun t ht => Classical.choose (Classical.choose_spec (htime t ht)).2
  have hgAt : forall t ht,
      (forall x : M, Filter.Tendsto (fun m => (gSeq (phi ((psiAt t ht) m)) t).inner x)
        Filter.atTop (nhds ((gAt t ht).inner x))) /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi ((psiAt t ht) k)) t) (gAt t ht) gRef x < eps := by
    intro t ht
    exact Classical.choose_spec (Classical.choose_spec (htime t ht)).2
  let gInf : Real -> SmoothRiemannianMetric I M :=
    fun t => if ht : t ∈ Set.Icc beta psiT then gAt t ht else gRef
  have hfull : forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps := by
    intro t ht eps heps
    have hcauchy :=
      netCauchyAt (I := I) K beta psiT p gSeq gNet gRef phi L hL hgLip e he hdense hnetNorm
        t ht
    have hsub : forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a ((fun k => gSeq (phi k) t) ((psiAt t ht) k))
            (gAt t ht) gRef x < eps := by
      intro eps heps
      exact (hgAt t ht).2 eps heps
    obtain ⟨k0, hk0⟩ :=
      fullOfSubseq (I := I) K p (fun k => gSeq (phi k) t) (gAt t ht) gRef
        (psiAt t ht) (hpsiAt t ht) hcauchy hsub eps heps
    refine ⟨k0, fun k hk a ha x hx => ?_⟩
    have hgInf_t : gInf t = gAt t ht := by
      dsimp [gInf]
      exact dif_pos ht
    rw [hgInf_t]
    exact hk0 k hk a ha x hx
  have hInfLip :
      forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t| :=
    infLipOfConv (I := I) K beta psiT p gSeq gInf gRef phi L hgLip hfull

  have hwinPt : forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall t, t ∈ Set.Icc beta psiT -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps := by
    intro eps heps
    have hLpos : (0 : Real) < L + 1 := by linarith
    set delta : Real := eps / (3 * (L + 1)) with hdeltadef
    have hdeltapos : 0 < delta := by rw [hdeltadef]; positivity
    have hcover : Set.Icc beta psiT ⊆ ⋃ tau : {tau : Real // tau ∈ Set.range e ∧ tau ∈ Set.Icc beta psiT},
        Metric.ball (tau : Real) delta := by
      intro t ht
      obtain ⟨n, hn⟩ := hdense t ht delta hdeltapos
      refine Set.mem_iUnion.2 ⟨⟨e n, ⟨n, rfl⟩, he n⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      exact hn
    obtain ⟨F, hF⟩ := (isCompact_Icc (a := beta) (b := psiT)).elim_finite_subcover
      (fun tau : {tau : Real // tau ∈ Set.range e ∧ tau ∈ Set.Icc beta psiT} =>
        Metric.ball (tau : Real) delta)
      (fun _ => Metric.isOpen_ball) hcover
    have hk0 : forall tau : {tau : Real // tau ∈ Set.range e ∧ tau ∈ Set.Icc beta psiT},
        exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) gRef x < eps / 3 :=
      fun tau => hfull (tau : Real) tau.2.2 (eps / 3) (by positivity)
    choose k0fun hk0fun using hk0
    refine ⟨F.sup k0fun, fun k hk t ht a hap x hxK => ?_⟩
    obtain ⟨tau, htauF, httau⟩ := Set.mem_iUnion₂.1 (hF ht)
    have hdist : |t - (tau : Real)| < delta := by
      rw [Metric.mem_ball, Real.dist_eq] at httau; exact httau
    have h1 : metricDerivNorm (I := I) a (gSeq (phi k) t) (gSeq (phi k) (tau : Real)) gRef x
        <= L * |t - (tau : Real)| :=
      hgLip (phi k) t ht (tau : Real) tau.2.2 a hap x hxK
    have h3 : metricDerivNorm (I := I) a (gInf (tau : Real)) (gInf t) gRef x
        <= L * |t - (tau : Real)| := by
      have := hInfLip (tau : Real) tau.2.2 t ht a hap x hxK
      rwa [abs_sub_comm] at this
    have h2 : metricDerivNorm (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) gRef x < eps / 3 :=
      hk0fun tau k (le_trans (Finset.le_sup htauF) hk) a hap x hxK
    have htri : metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x <=
        metricDerivNorm (I := I) a (gSeq (phi k) t) (gSeq (phi k) (tau : Real)) gRef x
        + (metricDerivNorm (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) gRef x
          + metricDerivNorm (I := I) a (gInf (tau : Real)) (gInf t) gRef x) := by
      refine le_trans
        (metricDerivNorm_triangle (I := I) a (gSeq (phi k) t) (gSeq (phi k) (tau : Real)) (gInf t) gRef x) ?_
      have := metricDerivNorm_triangle (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) (gInf t) gRef x
      linarith
    have hdb : L * |t - (tau : Real)| <= L * delta := mul_le_mul_of_nonneg_left hdist.le hL
    have hsmall : 2 * L * delta < 2 * eps / 3 := by
      have hstep : 2 * L * delta < 2 * (L + 1) * delta := by nlinarith [hdeltapos]
      have heq : 2 * (L + 1) * delta = 2 * eps / 3 := by rw [hdeltadef]; field_simp
      linarith
    nlinarith [htri, h1, h2, h3, hdb, hsmall]
  refine ⟨phi, hphi, gInf, ?_, hwinPt⟩
  intro t ht
  refine ⟨psiAt t ht, hpsiAt t ht, ?_⟩
  have hgInf_t : gInf t = gAt t ht := by dsimp [gInf]; exact dif_pos ht
  rw [hgInf_t]
  exact (hgAt t ht).1







theorem windowGInfAll
    [WeaklyLocallyCompactSpace M]
    (hne : Nonempty M)
    (beta psiT : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hgLip : forall K' : Set M, IsCompact K' -> forall p : Nat,
      exists L : Real, 0 <= L /\
        forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
          forall a : Nat, a <= p -> forall x, x ∈ K' ->
            metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hbdd : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) t) gRef z <= C)
    (hlow : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) t).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gInf : Real -> SmoothRiemannianMetric I M,
        forall K : Set M, IsCompact K -> forall p : Nat, forall eps : Real, 0 < eps ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t, t ∈ Set.Icc beta psiT ->
              metricDerivNormSupOn (I := I) K p (gSeq (phi k) t) (gInf t) gRef < eps := by
  classical

  let Kx : CompactExhaustion M := CompactExhaustion.choice M
  have hKxc : forall j : Nat, IsCompact (Kx j) := fun j => Kx.isCompact j



  set P : Nat -> (Nat -> Nat) -> Prop := fun j phi =>
    exists gNet : Nat -> SmoothRiemannianMetric I M,
      (forall n : Nat, forall x : M,
        Filter.Tendsto (fun k => (gSeq (phi k) (e n)).inner x) Filter.atTop
          (nhds ((gNet n).inner x))) /\
      (forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= j -> forall z, z ∈ Kx j ->
          metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef z < eps) with hPdef
  have hstep : forall j : Nat, forall phi : Nat -> Nat, StrictMono phi ->
      exists psi : Nat -> Nat, StrictMono psi /\ P j (phi ∘ psi) := by
    intro j phi hphi
    obtain ⟨psi, hpsi, gNet, htend, hconv⟩ :=
      netFullDiag (I := I) hne (Kx j) (hKxc j) j gRef (fun k => gSeq (phi k)) e
        (fun n rho hrho q K' hK' => hbdd (phi ∘ rho) (hphi.comp hrho) (e n) (he n) q K' hK')
        (fun n rho hrho => hlow (phi ∘ rho) (hphi.comp hrho) (e n) (he n))
    refine ⟨psi, hpsi, gNet, ?_, ?_⟩
    · intro n x
      simpa only [Function.comp_apply] using htend n x
    · intro n eps heps
      obtain ⟨k0, hk0⟩ := hconv n eps heps
      exact ⟨k0, fun k hk a ha z hz => by
        simpa only [Function.comp_apply] using hk0 k hk a ha z hz⟩
  have hsub : forall j : Nat, forall phi psi : Nat -> Nat, StrictMono psi ->
      P j phi -> P j (phi ∘ psi) := by
    intro j phi psi hpsi ⟨gNet, htend, hconv⟩
    refine ⟨gNet, ?_, ?_⟩
    · intro n x
      exact (htend n x).comp hpsi.tendsto_atTop
    · intro n eps heps
      obtain ⟨k0, hk0⟩ := hconv n eps heps
      exact ⟨k0, fun k hk a ha z hz => by
        simpa only [Function.comp_apply] using hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha z hz⟩
  have hextend : forall j : Nat, forall phi : Nat -> Nat, forall m : Nat,
      P j (fun k => phi (k + m)) -> P j phi := by
    intro j phi m ⟨gNet, htend, hconv⟩
    refine ⟨gNet, ?_, ?_⟩
    · intro n x
      exact (Filter.tendsto_add_atTop_iff_nat
        (f := fun k => (gSeq (phi k) (e n)).inner x) m).1 (htend n x)
    · intro n eps heps
      obtain ⟨k0, hk0⟩ := hconv n eps heps
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval
  obtain ⟨phi, hphi, hPphi⟩ := exists_diag_subseq P hstep hsub hextend

  choose gNetF hgNetTend hgNetConv using hPphi
  have hgNetUniq : forall i j : Nat, gNetF i = gNetF j := by
    intro i j
    refine funext fun n => metric_ext_inner (gNetF i n) (gNetF j n) fun x => ?_
    exact tendsto_nhds_unique (hgNetTend i n x) (hgNetTend j n x)
  set gNet : Nat -> SmoothRiemannianMetric I M := gNetF 0 with hgNetDef
  have hnetTend : forall n : Nat, forall x : M,
      Filter.Tendsto (fun k => (gSeq (phi k) (e n)).inner x) Filter.atTop
        (nhds ((gNet n).inner x)) := hgNetTend 0
  have hnetConv : forall j : Nat, forall n : Nat, forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= j ->
        forall z, z ∈ Kx j -> metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef z < eps := by
    intro j n eps heps
    have := hgNetConv j n eps heps
    rw [show gNetF j = gNet from (hgNetUniq j 0)] at this
    exact this

  choose Lf hLf using fun j : Nat => hgLip (Kx j) (hKxc j) j
  have hLfnn : forall j, 0 <= Lf j := fun j => (hLf j).1

  have hLipAll : forall j : Nat, forall k : Nat, forall s, s ∈ Set.Icc beta psiT ->
      forall t, t ∈ Set.Icc beta psiT -> forall a : Nat, a <= j -> forall x, x ∈ Kx j ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= Lf j * |s - t| :=
    fun j => (hLf j).2

  have hcauchy0 : forall t, t ∈ Set.Icc beta psiT -> forall x : M,
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall m : Nat, k0 <= m ->
        forall l : Nat, k0 <= l ->
          metricDerivNorm (I := I) 0 (gSeq (phi m) t) (gSeq (phi l) t) gRef x < eps := by
    intro t ht x eps heps
    obtain ⟨m0, hm0⟩ := Kx.exists_superset_of_isCompact (isCompact_singleton (x := x))
    have hxKm : x ∈ Kx m0 := hm0 (Set.mem_singleton x)
    obtain ⟨k0, hk0⟩ :=
      netCauchyAt (I := I) (Kx m0) beta psiT m0 gSeq gNet gRef phi (Lf m0) (hLfnn m0)
        (hLipAll m0) e he hdense (hnetConv m0) t ht eps heps
    exact ⟨k0, fun m hm l hl => hk0 m hm l hl 0 (Nat.zero_le m0) x hxKm⟩
  have hcauchyInner : forall t, t ∈ Set.Icc beta psiT -> forall x : M,
      forall v w : TangentSpace I x, CauchySeq (fun k => (gSeq (phi k) t).inner x v w) := by
    intro t ht x v w
    exact metricInner_cauchy (I := I) (fun k => gSeq (phi k) t) gRef x v w
      (fun eps heps => hcauchy0 t ht x eps heps)

  have htime0 : forall t, t ∈ Set.Icc beta psiT ->
      exists psi : Nat -> Nat, StrictMono psi /\
        exists gT : SmoothRiemannianMetric I M,
          (forall x : M, Filter.Tendsto (fun m => (gSeq (phi (psi m)) t).inner x)
            Filter.atTop (nhds (gT.inner x))) := by
    intro t ht
    obtain ⟨psi, hpsi, gT, hinner, _⟩ :=
      metricPreconvFull (I := I) hne (Kx 0) (hKxc 0) 0 gRef (fun k => gSeq (phi k) t)
        (hbdd phi hphi t ht) (hlow phi hphi t ht)
    exact ⟨psi, hpsi, gT, fun x => by simpa only [Function.comp_apply] using hinner x⟩
  let psi0 : (t : Real) -> t ∈ Set.Icc beta psiT -> Nat -> Nat :=
    fun t ht => Classical.choose (htime0 t ht)
  have hpsi0 : forall t ht, StrictMono (psi0 t ht) := fun t ht =>
    (Classical.choose_spec (htime0 t ht)).1
  let gAt0 : (t : Real) -> t ∈ Set.Icc beta psiT -> SmoothRiemannianMetric I M :=
    fun t ht => Classical.choose (Classical.choose_spec (htime0 t ht)).2
  have hgAt0 : forall t ht, forall x : M,
      Filter.Tendsto (fun m => (gSeq (phi ((psi0 t ht) m)) t).inner x)
        Filter.atTop (nhds ((gAt0 t ht).inner x)) := fun t ht =>
    Classical.choose_spec (Classical.choose_spec (htime0 t ht)).2
  set gInf : Real -> SmoothRiemannianMetric I M :=
    fun t => if ht : t ∈ Set.Icc beta psiT then gAt0 t ht else gRef with hgInfDef
  have hgInf_eq : forall t (ht : t ∈ Set.Icc beta psiT), gInf t = gAt0 t ht := by
    intro t ht; rw [hgInfDef]; exact dif_pos ht

  have hfullj : forall j : Nat, forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= j -> forall x, x ∈ Kx j ->
        metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps := by
    intro j t ht eps heps

    obtain ⟨psi, hpsi, gT, hinnerT, hnormT⟩ :=
      metricPreconvFull (I := I) hne (Kx j) (hKxc j) j gRef (fun k => gSeq (phi k) t)
        (hbdd phi hphi t ht) (hlow phi hphi t ht)
    have hinnerT' : forall x : M, Filter.Tendsto (fun m => (gSeq (phi (psi m)) t).inner x)
        Filter.atTop (nhds (gT.inner x)) := fun x => by
      simpa only [Function.comp_apply] using hinnerT x
    have hgTeq : gT = gInf t := by
      rw [hgInf_eq t ht]
      exact metricLimit_uniq (I := I) (fun k => gSeq (phi k) t) gT (gAt0 t ht)
        (hcauchyInner t ht) psi hpsi (psi0 t ht) (hpsi0 t ht) hinnerT' (hgAt0 t ht)
    have hcauchyj := netCauchyAt (I := I) (Kx j) beta psiT j gSeq gNet gRef phi (Lf j)
      (hLfnn j) (hLipAll j) e he hdense (hnetConv j) t ht
    have hsubj : forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= j -> forall x, x ∈ Kx j ->
          metricDerivNorm (I := I) a ((fun k => gSeq (phi k) t) (psi k)) gT gRef x < eps := by
      intro eps heps
      obtain ⟨k0, hk0⟩ := hnormT eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩
    obtain ⟨k0, hk0⟩ :=
      fullOfSubseq (I := I) (Kx j) j (fun k => gSeq (phi k) t) gT gRef psi hpsi
        hcauchyj hsubj eps heps
    refine ⟨k0, fun k hk a ha x hx => ?_⟩
    rw [← hgTeq]; exact hk0 k hk a ha x hx

  have hInfLipj : forall j : Nat,
      forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
        forall a : Nat, a <= j -> forall x, x ∈ Kx j ->
          metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= Lf j * |s - t| := fun j =>
    infLipOfConv (I := I) (Kx j) beta psiT j gSeq gInf gRef phi (Lf j) (hLipAll j)
      (fun t ht eps heps => hfullj j t ht eps heps)

  have hwinj : forall j : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall t, t ∈ Set.Icc beta psiT -> forall a : Nat, a <= j ->
        forall x, x ∈ Kx j -> metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps := by
    intro j eps heps
    have hLpos : (0 : Real) < Lf j + 1 := by linarith [hLfnn j]
    set delta : Real := eps / (3 * (Lf j + 1)) with hdeltadef
    have hdeltapos : 0 < delta := by rw [hdeltadef]; positivity
    have hcover : Set.Icc beta psiT ⊆ ⋃ tau : {tau : Real // tau ∈ Set.range e ∧ tau ∈ Set.Icc beta psiT},
        Metric.ball (tau : Real) delta := by
      intro t ht
      obtain ⟨n, hn⟩ := hdense t ht delta hdeltapos
      refine Set.mem_iUnion.2 ⟨⟨e n, ⟨n, rfl⟩, he n⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]; exact hn
    obtain ⟨F, hF⟩ := (isCompact_Icc (a := beta) (b := psiT)).elim_finite_subcover
      (fun tau : {tau : Real // tau ∈ Set.range e ∧ tau ∈ Set.Icc beta psiT} =>
        Metric.ball (tau : Real) delta)
      (fun _ => Metric.isOpen_ball) hcover
    have hk0 : forall tau : {tau : Real // tau ∈ Set.range e ∧ tau ∈ Set.Icc beta psiT},
        exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= j -> forall x, x ∈ Kx j ->
          metricDerivNorm (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) gRef x < eps / 3 :=
      fun tau => hfullj j (tau : Real) tau.2.2 (eps / 3) (by positivity)
    choose k0fun hk0fun using hk0
    refine ⟨F.sup k0fun, fun k hk t ht a hap x hxK => ?_⟩
    obtain ⟨tau, htauF, httau⟩ := Set.mem_iUnion₂.1 (hF ht)
    have hdist : |t - (tau : Real)| < delta := by
      rw [Metric.mem_ball, Real.dist_eq] at httau; exact httau
    have h1 : metricDerivNorm (I := I) a (gSeq (phi k) t) (gSeq (phi k) (tau : Real)) gRef x
        <= Lf j * |t - (tau : Real)| := (hLipAll j) (phi k) t ht (tau : Real) tau.2.2 a hap x hxK
    have h3 : metricDerivNorm (I := I) a (gInf (tau : Real)) (gInf t) gRef x
        <= Lf j * |t - (tau : Real)| := by
      have := hInfLipj j (tau : Real) tau.2.2 t ht a hap x hxK
      rwa [abs_sub_comm] at this
    have h2 : metricDerivNorm (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) gRef x < eps / 3 :=
      hk0fun tau k (le_trans (Finset.le_sup htauF) hk) a hap x hxK
    have htri : metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x <=
        metricDerivNorm (I := I) a (gSeq (phi k) t) (gSeq (phi k) (tau : Real)) gRef x
        + (metricDerivNorm (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) gRef x
          + metricDerivNorm (I := I) a (gInf (tau : Real)) (gInf t) gRef x) := by
      refine le_trans
        (metricDerivNorm_triangle (I := I) a (gSeq (phi k) t) (gSeq (phi k) (tau : Real)) (gInf t) gRef x) ?_
      have := metricDerivNorm_triangle (I := I) a (gSeq (phi k) (tau : Real)) (gInf (tau : Real)) (gInf t) gRef x
      linarith
    have hdb : Lf j * |t - (tau : Real)| <= Lf j * delta :=
      mul_le_mul_of_nonneg_left hdist.le (hLfnn j)
    have hsmall : 2 * Lf j * delta < 2 * eps / 3 := by
      have hstep : 2 * Lf j * delta < 2 * (Lf j + 1) * delta := by nlinarith [hdeltapos]
      have heq : 2 * (Lf j + 1) * delta = 2 * eps / 3 := by
        rw [hdeltadef]; field_simp
      linarith
    nlinarith [htri, h1, h2, h3, hdb, hsmall]

  refine ⟨phi, hphi, gInf, ?_⟩
  intro K hK p eps heps
  obtain ⟨j1, hj1⟩ := Kx.exists_superset_of_isCompact hK
  set j : Nat := max j1 p with hjdef
  have hKj : K ⊆ Kx j := hj1.trans (Kx.subset (le_max_left j1 p))
  have hpj : p <= j := le_max_right j1 p
  obtain ⟨k0, hk0⟩ := hwinj j (eps / 2) (by positivity)
  refine ⟨k0, fun k hk t ht => ?_⟩
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p (gSeq (phi k) t) (gInf t) gRef
      (eps / 2) (by positivity) ?_) (by linarith)
  intro a hap x hxK
  exact (hk0 k hk t ht a (le_trans hap hpj) x (hKj hxK)).le

end HCGCompactness
end DifferentialGeometry
