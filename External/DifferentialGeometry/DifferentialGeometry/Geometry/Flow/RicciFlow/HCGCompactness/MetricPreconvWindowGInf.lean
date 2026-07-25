import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindow

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

set_option maxHeartbeats 800000 in


omit [Module.Finite ℝ E] in
theorem metricPreconvFull
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M) (gSeq : Nat -> SmoothRiemannianMetric I M)
    (hbdd : forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
      forall k : Nat, forall z, z ∈ K' ->
        metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C)
    (hlow : exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v <= (gSeq k).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\ exists gInf : SmoothRiemannianMetric I M,
      (forall x : M, Filter.Tendsto (fun m => (gSeq (phi m)).inner x) Filter.atTop
        (nhds (gInf.inner x))) /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k)) gInf gRef x < eps := by
  classical
  obtain ⟨phi0, hphi0, gInf, hconv⟩ := metricPreconv_gInf (I := I) hne gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_uniform_patch (I := I) gRef gSeq hbdd phi0 gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : Nat, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨phid, hphid, hPphid⟩ := exists_diag_subseq
    (fun n phi => forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phi k))) gInf gRef z < eps)
    (fun n phi hphi => by
      obtain ⟨psi, hpsi, hu⟩ := hpatch (e n) phi hphi
      refine ⟨psi, hpsi, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p eps heps
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n phi psi hpsi hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      exact ⟨k0, fun k hk a ha z hz =>
        hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha z hz⟩)
    (fun n phi m hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  refine ⟨phi0 ∘ phid, hphi0.comp hphid, gInf, ?_, fun eps heps => ?_⟩
  · intro x
    simpa only [Function.comp_apply] using (hconv x).comp hphid.tendsto_atTop
  · obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
      (fun z hz => hcovN (Set.mem_univ z))
    have perN : forall n, n ∈ F -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phid k))) gInf gRef z < eps :=
      fun n _ => hPphid n eps heps
    choose k0fn hk0fn using perN
    refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
    obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
    simpa only [Function.comp_apply] using
      hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
        (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)

set_option maxHeartbeats 800000 in



omit [Module.Finite ℝ E] in
theorem metricPreconvNorm
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M) (gSeq : Nat -> SmoothRiemannianMetric I M)
    (hbdd : forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
      forall k : Nat, forall z, z ∈ K' ->
        metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C)
    (hlow : exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v <= (gSeq k).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\ exists gInf : SmoothRiemannianMetric I M,
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k)) gInf gRef x < eps := by
  classical
  obtain ⟨phi0, hphi0, gInf, hconv⟩ := metricPreconv_gInf (I := I) hne gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_uniform_patch (I := I) gRef gSeq hbdd phi0 gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : Nat, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨phid, hphid, hPphid⟩ := exists_diag_subseq
    (fun n phi => forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phi k))) gInf gRef z < eps)
    (fun n phi hphi => by
      obtain ⟨psi, hpsi, hu⟩ := hpatch (e n) phi hphi
      refine ⟨psi, hpsi, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p eps heps
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n phi psi hpsi hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      exact ⟨k0, fun k hk a ha z hz =>
        hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha z hz⟩)
    (fun n phi m hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  refine ⟨phi0 ∘ phid, hphi0.comp hphid, gInf, fun eps heps => ?_⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
    (fun z hz => hcovN (Set.mem_univ z))
  have perN : forall n, n ∈ F -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= p -> forall z, z ∈ C (e n) ->
        metricDerivNorm (I := I) a (gSeq (phi0 (phid k))) gInf gRef z < eps :=
    fun n _ => hPphid n eps heps
  choose k0fn hk0fn using perN
  refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
  obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
  simpa only [Function.comp_apply] using
    hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
      (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)




omit [Module.Finite ℝ E] in
theorem netNormDiag
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (e : Nat -> Real)
    (hbdd : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) (e n)) gRef z <= C)
    (hlow : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) (e n)).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gNet : Nat -> SmoothRiemannianMetric I M,
        forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
          forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps := by
  classical
  obtain ⟨phi, hphi, hPphi⟩ := exists_diag_subseq
    (fun n rho => exists gLim : SmoothRiemannianMetric I M,
      forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (rho k) (e n)) gLim gRef x < eps)
    (fun n rho hrho => by
      obtain ⟨psi, hpsi, gLim, hlim⟩ :=
        metricPreconvNorm (I := I) hne K hK p gRef (fun k => gSeq (rho k) (e n))
          (hbdd n rho hrho) (hlow n rho hrho)
      refine ⟨psi, hpsi, gLim, ?_⟩
      intro eps heps
      obtain ⟨k0, hk0⟩ := hlim eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩)
    (fun n rho psi hpsi hP => by
      obtain ⟨gLim, hlim⟩ := hP
      refine ⟨gLim, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hlim eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using
          hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha x hx⟩)
    (fun n rho m hP => by
      obtain ⟨gLim, hlim⟩ := hP
      refine ⟨gLim, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hlim eps heps
      refine ⟨k0 + m, fun k hk a ha x hx => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha x hx
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  choose gNet hgNet using hPphi
  exact ⟨phi, hphi, gNet, hgNet⟩




omit [Module.Finite ℝ E] in
theorem netFullDiag
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (e : Nat -> Real)
    (hbdd : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) (e n)) gRef z <= C)
    (hlow : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) (e n)).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gNet : Nat -> SmoothRiemannianMetric I M,
        (forall n : Nat, forall x : M,
          Filter.Tendsto (fun k => (gSeq (phi k) (e n)).inner x) Filter.atTop
            (nhds ((gNet n).inner x))) /\
        forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
          forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps := by
  classical
  obtain ⟨phi, hphi, hPphi⟩ := exists_diag_subseq
    (fun n rho => exists gLim : SmoothRiemannianMetric I M,
      (forall x : M, Filter.Tendsto (fun k => (gSeq (rho k) (e n)).inner x)
        Filter.atTop (nhds (gLim.inner x))) /\
      forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (rho k) (e n)) gLim gRef x < eps)
    (fun n rho hrho => by
      obtain ⟨psi, hpsi, gLim, hinner, hlim⟩ :=
        metricPreconvFull (I := I) hne K hK p gRef (fun k => gSeq (rho k) (e n))
          (hbdd n rho hrho) (hlow n rho hrho)
      refine ⟨psi, hpsi, gLim, ?_, ?_⟩
      · intro x
        simpa only [Function.comp_apply] using hinner x
      · intro eps heps
        obtain ⟨k0, hk0⟩ := hlim eps heps
        exact ⟨k0, fun k hk a ha x hx => by
          simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩)
    (fun n rho psi hpsi hP => by
      obtain ⟨gLim, hinner, hlim⟩ := hP
      refine ⟨gLim, ?_, fun eps heps => ?_⟩
      · intro x
        simpa only [Function.comp_apply] using (hinner x).comp hpsi.tendsto_atTop
      · obtain ⟨k0, hk0⟩ := hlim eps heps
        exact ⟨k0, fun k hk a ha x hx => by
          simpa only [Function.comp_apply] using
            hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha x hx⟩)
    (fun n rho m hP => by
      obtain ⟨gLim, hinner, hlim⟩ := hP
      refine ⟨gLim, ?_, fun eps heps => ?_⟩
      · intro x
        exact (Filter.tendsto_add_atTop_iff_nat
          (f := fun k => (gSeq (rho k) (e n)).inner x) m).1 (hinner x)
      · obtain ⟨k0, hk0⟩ := hlim eps heps
        refine ⟨k0 + m, fun k hk a ha x hx => ?_⟩
        have hval := hk0 (k - m) (by omega) a ha x hx
        simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
        exact hval)
  choose gNet hgNet using hPphi
  exact ⟨phi, hphi, gNet, fun n => (hgNet n).1, fun n => (hgNet n).2⟩


omit [Module.Finite ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem normSq0S_neg
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x) :
    Tensor0SBundle.normSq0S (I := I) gRef x s (-T) =
      Tensor0SBundle.normSq0S (I := I) gRef x s T := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i' j'
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i' j'
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv (-T),
    Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x s basis hinv T]
  refine Finset.sum_congr rfl fun slots _ => ?_
  simp [Tensor0SBundle.component0S_apply]


omit [Module.Finite ℝ E] [IsManifold I 1 M] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_symm
    [Module.Finite ℝ E]
    (a : Nat) (A B gRef : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) a A B gRef x =
      metricDerivNorm (I := I) a B A gRef x := by
  have hneg :
      metricDiffCovDerivAt (I := I) a B A gRef x =
        -metricDiffCovDerivAt (I := I) a A B gRef x := by
    simp only [metricDiffCovDerivAt]
    abel
  rw [metricDerivNorm, metricDerivNorm, hneg, normSq0S_neg]




omit [Module.Finite ℝ E] in
omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem netCauchyAt
    [Module.Finite ℝ E]
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gNet : Nat -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hnet : forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps) :
    forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall m : Nat, k0 <= m -> forall l : Nat, k0 <= l ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi l) t) gRef x < eps := by
  intro t ht eps heps
  have hLpos : (0 : Real) < L + 1 := by linarith
  set delta : Real := eps / (4 * (L + 1)) with hdelta
  have hdelta_pos : 0 < delta := by rw [hdelta]; positivity
  obtain ⟨n, hn⟩ := hdense t ht delta hdelta_pos
  obtain ⟨k0, hk0⟩ := hnet n (eps / 4) (by positivity)
  refine ⟨k0, fun m hm l hl a ha x hxK => ?_⟩
  have h1 : metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi m) (e n)) gRef x
      <= L * |t - e n| :=
    hgLip (phi m) t ht (e n) (he n) a ha x hxK
  have h2 : metricDerivNorm (I := I) a (gSeq (phi m) (e n)) (gNet n) gRef x < eps / 4 :=
    hk0 m hm a ha x hxK
  have h3 : metricDerivNorm (I := I) a (gNet n) (gSeq (phi l) (e n)) gRef x < eps / 4 := by
    rw [metricDerivNorm_symm]
    exact hk0 l hl a ha x hxK
  have h4 : metricDerivNorm (I := I) a (gSeq (phi l) (e n)) (gSeq (phi l) t) gRef x
      <= L * |t - e n| := by
    have h := hgLip (phi l) (e n) (he n) t ht a ha x hxK
    rwa [abs_sub_comm] at h
  have htri : metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi l) t) gRef x <=
      metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi m) (e n)) gRef x
      + (metricDerivNorm (I := I) a (gSeq (phi m) (e n)) (gNet n) gRef x
        + (metricDerivNorm (I := I) a (gNet n) (gSeq (phi l) (e n)) gRef x
          + metricDerivNorm (I := I) a (gSeq (phi l) (e n)) (gSeq (phi l) t) gRef x)) := by
    refine le_trans
      (metricDerivNorm_triangle (I := I) a (gSeq (phi m) t) (gSeq (phi m) (e n))
        (gSeq (phi l) t) gRef x) ?_
    have htri2 := metricDerivNorm_triangle (I := I) a (gSeq (phi m) (e n)) (gNet n)
      (gSeq (phi l) t) gRef x
    have htri3 := metricDerivNorm_triangle (I := I) a (gNet n) (gSeq (phi l) (e n))
      (gSeq (phi l) t) gRef x
    linarith
  have hdbound : L * |t - e n| <= L * delta :=
    mul_le_mul_of_nonneg_left hn.le hL
  have hsmall : 2 * L * delta < eps / 2 := by
    have hstep : 2 * L * delta < 2 * (L + 1) * delta := by nlinarith
    have heq : 2 * (L + 1) * delta = eps / 2 := by
      rw [hdelta]
      field_simp
      ring
    linarith
  nlinarith [htri, h1, h2, h3, h4, hdbound, hsmall]



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem fullOfSubseq
    [Module.Finite ℝ E]
    (K : Set M) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gLim gRef : SmoothRiemannianMetric I M) (psi : Nat -> Nat) (hpsi : StrictMono psi)
    (hcauchy : forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall m : Nat, k0 <= m -> forall l : Nat, k0 <= l ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq m) (gSeq l) gRef x < eps)
    (hsub : forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (psi k)) gLim gRef x < eps) :
    forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k) gLim gRef x < eps := by
  intro eps heps
  obtain ⟨kC, hkC⟩ := hcauchy (eps / 2) (by positivity)
  obtain ⟨kS, hkS⟩ := hsub (eps / 2) (by positivity)
  let j : Nat := max kC kS
  refine ⟨kC, fun k hk a ha x hxK => ?_⟩
  have hjC : kC <= psi j := le_trans (Nat.le_max_left kC kS) (hpsi.id_le j)
  have hjS : kS <= j := Nat.le_max_right kC kS
  have h1 : metricDerivNorm (I := I) a (gSeq k) (gSeq (psi j)) gRef x < eps / 2 :=
    hkC k hk (psi j) hjC a ha x hxK
  have h2 : metricDerivNorm (I := I) a (gSeq (psi j)) gLim gRef x < eps / 2 :=
    hkS j hjS a ha x hxK
  have htri := metricDerivNorm_triangle (I := I) a (gSeq k) (gSeq (psi j)) gLim gRef x
  linarith



omit [Module.Finite ℝ E] in
omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem infLipOfConv
    [Module.Finite ℝ E]
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gInf : Real -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat)
    (L : Real)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hconv : forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps) :
    forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t| := by
  intro s hs t ht a ha x hxK
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨kS, hkS⟩ := hconv s hs (eps / 2) (by positivity)
  obtain ⟨kT, hkT⟩ := hconv t ht (eps / 2) (by positivity)
  let k0 : Nat := max kS kT
  have hkS0 : kS <= k0 := Nat.le_max_left kS kT
  have hkT0 : kT <= k0 := Nat.le_max_right kS kT
  have h1 : metricDerivNorm (I := I) a (gInf s) (gSeq (phi k0) s) gRef x < eps / 2 := by
    rw [metricDerivNorm_symm]
    exact hkS k0 hkS0 a ha x hxK
  have h2 : metricDerivNorm (I := I) a (gSeq (phi k0) s) (gSeq (phi k0) t) gRef x
      <= L * |s - t| :=
    hgLip (phi k0) s hs t ht a ha x hxK
  have h3 : metricDerivNorm (I := I) a (gSeq (phi k0) t) (gInf t) gRef x < eps / 2 :=
    hkT k0 hkT0 a ha x hxK
  have htri : metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <=
      metricDerivNorm (I := I) a (gInf s) (gSeq (phi k0) s) gRef x
      + (metricDerivNorm (I := I) a (gSeq (phi k0) s) (gSeq (phi k0) t) gRef x
        + metricDerivNorm (I := I) a (gSeq (phi k0) t) (gInf t) gRef x) := by
    refine le_trans
      (metricDerivNorm_triangle (I := I) a (gInf s) (gSeq (phi k0) s) (gInf t) gRef x) ?_
    have htri2 := metricDerivNorm_triangle (I := I) a (gSeq (phi k0) s)
      (gSeq (phi k0) t) (gInf t) gRef x
    linarith
  linarith




omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem windowOfNet
    [Module.Finite ℝ E]
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gInf : Real -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hInfLip : forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t|)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hnet : forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gInf (e n)) gRef x < eps) :
    exists phi' : Nat -> Nat, StrictMono phi' /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t, t ∈ Set.Icc beta psiT ->
          metricDerivNormSupOn (I := I) K p (gSeq (phi' k) t) (gInf t) gRef < eps := by
  refine ⟨phi, hphi, ?_⟩
  refine windowPreconv (I := I) K beta psiT p (fun k => gSeq (phi k)) gInf gRef L hL
    (fun k => hgLip (phi k)) hInfLip (Set.range e) ?_ ?_
  · intro t ht delta hdelta
    obtain ⟨n, hn⟩ := hdense t ht delta hdelta
    exact ⟨e n, ⟨n, rfl⟩, he n, hn⟩
  · rintro tau ⟨n, rfl⟩ _ eps heps
    exact hnet n eps heps




structure WindowGInfOut
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) : Prop where
  out :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gInf : Real -> SmoothRiemannianMetric I M,
        forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t, t ∈ Set.Icc beta psiT ->
            metricDerivNormSupOn (I := I) K p (gSeq (phi k) t) (gInf t) gRef < eps




omit [Module.Finite ℝ E] in
theorem windowGInf
    [Module.Finite ℝ E]
    (hne : Nonempty M)
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
        forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t, t ∈ Set.Icc beta psiT ->
            metricDerivNormSupOn (I := I) K p (gSeq (phi k) t) (gInf t) gRef < eps := by
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
  obtain ⟨phi', hphi', hwin⟩ :=
    windowOfNet (I := I) K beta psiT p gSeq gInf gRef phi hphi L hL hgLip hInfLip e he
      hdense (fun n eps heps => hfull (e n) (he n) eps heps)
  exact ⟨phi', hphi', gInf, hwin⟩


omit [Module.Finite ℝ E] in
theorem windowGInfOut
    [Module.Finite ℝ E]
    (hne : Nonempty M)
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
    WindowGInfOut (I := I) K beta psiT p gSeq gRef := by
  exact
    ⟨windowGInf (I := I) hne K hK beta psiT p gSeq gRef e he hdense L hL hgLip hbdd hlow⟩

end HCGCompactness
end DifferentialGeometry
