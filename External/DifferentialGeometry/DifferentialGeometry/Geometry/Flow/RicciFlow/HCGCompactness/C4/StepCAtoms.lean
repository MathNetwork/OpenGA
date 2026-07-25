import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCNormalBump
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCWeights
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]





noncomputable def stepCBump (lam : Real) (hlam : 0 < lam) : ContDiffBump (0 : Real) where
  rIn := (3 * lam) ^ 2
  rOut := (7 * lam / 2) ^ 2
  rIn_pos := sq_pos_of_pos (by positivity)
  rIn_lt_rOut := by nlinarith

@[simp] theorem stepCBump_rIn (lam : Real) (hlam : 0 < lam) :
    (stepCBump lam hlam).rIn = (3 * lam) ^ 2 := rfl

@[simp] theorem stepCBump_rOut (lam : Real) (hlam : 0 < lam) :
    (stepCBump lam hlam).rOut = (7 * lam / 2) ^ 2 := rfl

@[simp] theorem stepCBump_sqrt (lam : Real) (hlam : 0 < lam) :
    Real.sqrt (stepCBump lam hlam).rOut = 7 * lam / 2 := by
  rw [stepCBump_rOut, Real.sqrt_sq_eq_abs, abs_of_pos]
  positivity


theorem stepCBump_out_lt (lam : Real) (hlam : 0 < lam) :
    Real.sqrt (stepCBump lam hlam).rOut < 4 * lam := by
  rw [stepCBump_sqrt lam hlam]
  linarith




noncomputable def stepCAtom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) : Y.M → Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  quadNormal Y.metric p (stepCBump lam hlam)


omit [NeZero (Module.finrank ℝ E)] in
theorem stepCAtom_Icc
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) (q : Y.M) :
    stepCAtom Y p lam hlam q ∈ Set.Icc (0 : Real) 1 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact quadNormal_mem_Icc Y.metric p (stepCBump lam hlam) q


omit [NeZero (Module.finrank ℝ E)] in
theorem stepCAtom_nonneg
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) (q : Y.M) :
    0 ≤ stepCAtom Y p lam hlam q :=
  (stepCAtom_Icc Y p lam hlam q).1



variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}



noncomputable def seqAtom (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) : (X.obj (L.φ k)).M → Real :=
  match seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => 0
  | some c => stepCAtom (X.obj (L.φ k)) c (L.lamInf (gamma : Nat))
      (hd.lambda_pos hD (L.rInf (gamma : Nat)))


omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem seqAtom_subseq (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k : Nat) (gamma : Fin (pb.A r)) :
    seqAtom hd hD P (L.subseq hψ) pb r k gamma =
      seqAtom hd hD P L pb r (ψ k) gamma := by
  funext y
  unfold seqAtom
  simp only [NetLimitData.subseq_phi, NetLimitData.subseq_lamInf,
    Function.comp_apply]
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (gamma : Nat) with
  | none => rfl
  | some c => simp only

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem seqAtom_none (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r))
    (hc : seqCenter hd D P (L.φ k) (gamma : Nat) = none) :
    seqAtom hd hD P L pb r k gamma = 0 := by
  simp [seqAtom, hc]

omit [NeZero (Module.finrank ℝ E)] in
theorem seqAtom_some (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {c : (X.obj (L.φ k)).M}
    (hc : seqCenter hd D P (L.φ k) (gamma : Nat) = some c) :
    seqAtom hd hD P L pb r k gamma =
      stepCAtom (X.obj (L.φ k)) c (L.lamInf (gamma : Nat))
        (hd.lambda_pos hD (L.rInf (gamma : Nat))) := by
  simp [seqAtom, hc]




theorem seqAtom_contMDiff (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    ContMDiff I (modelWithCornersSelf Real Real) ∞
      (seqAtom hd hD P L pb r k gamma) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      rw [seqAtom_none hd hD P L pb r k gamma hc]
      exact contMDiff_const
  | some c =>
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      simpa only [stepCAtom] using
        quadNormal_contMDiff (X.obj (L.φ k)).metric c
          (stepCBump (L.lamInf (gamma : Nat))
            (hd.lambda_pos hD (L.rInf (gamma : Nat))))
          ((stepCBump_out_lt (L.lamInf (gamma : Nat))
              (hd.lambda_pos hD (L.rInf (gamma : Nat)))).trans
            (hgp gamma c hc))


omit [NeZero (Module.finrank ℝ E)] in
theorem seqAtom_Icc (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) (q : (X.obj (L.φ k)).M) :
    seqAtom hd hD P L pb r k gamma q ∈ Set.Icc (0 : Real) 1 := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [seqAtom, hc]
  | some c =>
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      exact stepCAtom_Icc (X.obj (L.φ k)) c _ _ q


omit [NeZero (Module.finrank ℝ E)] in
theorem seqAtom_nonneg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) (q : (X.obj (L.φ k)).M) :
    0 ≤ seqAtom hd hD P L pb r k gamma q :=
  (seqAtom_Icc hd hD P L pb r k gamma q).1


theorem seqAtom_one (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : q ∈ L.innerBall hd D P pb r k gamma) :
    seqAtom hd hD P L pb r k gamma q = 1 := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      simp [NetLimitData.innerBall, hc] at hq
  | some c =>
      let lam := L.lamInf (gamma : Nat)
      have hlam : 0 < lam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      have hR : 3 * lam < expRadiusGp (I := I) (X.obj (L.φ k)).metric c := by
        exact (by nlinarith : 3 * lam < 4 * lam).trans
          (hgp gamma c hc)
      have hdist_lt : dist c q < 3 * lam := by
        simpa only [NetLimitData.innerBall, hc, Metric.mem_ball, dist_comm] using hq
      obtain ⟨v, hvtgt, _hvdom, hvlen, hqexp⟩ :=
        properBallNormal (I := I) (X.obj (L.φ k)) (P (L.φ k))
          (c := c) (y := q) (R := 3 * lam) hR
          (by
            rw [Metric.mem_ball, dist_comm q c]
            exact hdist_lt)
      let ψ := normalChartAt (I := I) (X.obj (L.φ k)).metric c
      have hsymm : ψ.symm v = expMap (I := I) (X.obj (L.φ k)).metric c
          (show TangentSpace I c from v) := by
        simpa only [ψ] using
          normalChartAt_symm_apply (I := I) (X.obj (L.φ k)).metric c hvtgt
      have hsymmq : ψ.symm v = q := hsymm.trans hqexp.symm
      have hqsrc : q ∈ ψ.source := by
        rw [← hsymmq]
        exact ψ.symm.map_source hvtgt
      have hchart : ψ q = v := by
        rw [← hsymmq]
        exact ψ.toPartialEquiv.right_inv hvtgt
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      change quadNormal (X.obj (L.φ k)).metric c (stepCBump lam hlam) q = 1
      apply quadNormal_one (X.obj (L.φ k)).metric c (stepCBump lam hlam)
        (by simpa only [ψ] using hqsrc)
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      have hquad_nonneg : 0 ≤ (X.obj (L.φ k)).metric.inner c v v := by
        exact (mul_nonneg
          (gpCoerciveConst_pos (I := I) (X.obj (L.φ k)).metric c).le
          (sq_nonneg ‖v‖)).trans
            (gpCoerciveConst_le (I := I) (X.obj (L.φ k)).metric c v)
      rw [show normalChartAt (I := I) (X.obj (L.φ k)).metric c q = v by
        simpa only [ψ] using hchart, abs_of_nonneg hquad_nonneg, stepCBump_rIn]
      calc
        (X.obj (L.φ k)).metric.inner c v v =
            (Real.sqrt ((X.obj (L.φ k)).metric.inner c v v)) ^ 2 :=
          (Real.sq_sqrt hquad_nonneg).symm
        _ = (dist c q) ^ 2 := by
          rw [hvlen]
        _ ≤ (3 * lam) ^ 2 :=
          (sq_le_sq₀ dist_nonneg (by positivity)).2 hdist_lt.le


theorem seqAtom_mem_hat (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : seqAtom hd hD P L pb r k gamma q ≠ 0) :
    q ∈ L.hatBall hd D P pb r k gamma := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      exact False.elim (hq (by simp [seqAtom, hc]))
  | some c =>
      let lam := L.lamInf (gamma : Nat)
      have hlam : 0 < lam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      have hR := hgp gamma c hc
      have hsupp : q ∈ Function.support
          (quadNormal (X.obj (L.φ k)).metric c (stepCBump lam hlam)) := by
        rw [Function.mem_support]
        simpa [seqAtom, hc, stepCAtom, lam] using hq
      obtain ⟨v, hv, hqv⟩ := quadNormal_tsupport (X.obj (L.φ k)).metric c
        (stepCBump lam hlam) ((stepCBump_out_lt lam hlam).trans hR)
        (subset_tsupport _ hsupp)
      have hsqrt_lt : Real.sqrt ((X.obj (L.φ k)).metric.inner c v v) < 4 * lam :=
        (Real.sqrt_le_sqrt hv).trans_lt (stepCBump_out_lt lam hlam)
      have hsmall : Real.sqrt ((X.obj (L.φ k)).metric.inner c v v) <
          expRadiusGp (I := I) (X.obj (L.φ k)).metric c := hsqrt_lt.trans hR
      have hvnorm : ‖v‖ < expMapC2Radius (I := I) (X.obj (L.φ k)).metric c :=
        norm_lt_expMapC2Radius_of_sqrt_inner_lt
          (I := I) (X.obj (L.φ k)).metric c hsmall
      have hvtgt : v ∈ (normalChartAt (I := I) (X.obj (L.φ k)).metric c).target :=
        ball_subset_normalChartAt_target (I := I) (X.obj (L.φ k)).metric c hvnorm
      have hsymm : (normalChartAt (I := I) (X.obj (L.φ k)).metric c).symm v =
          expMap (I := I) (X.obj (L.φ k)).metric c
            (show TangentSpace I c from v) :=
        normalChartAt_symm_apply (I := I) (X.obj (L.φ k)).metric c hvtgt
      have hqexp : q = expMap (I := I) (X.obj (L.φ k)).metric c
          (show TangentSpace I c from v) := hqv.symm.trans hsymm
      have hdist_eq : dist c q =
          Real.sqrt ((X.obj (L.φ k)).metric.inner c v v) := by
        rw [hqexp]
        exact properExpDist (I := I) (X.obj (L.φ k)) (P (L.φ k)) c hsmall
      simp only [NetLimitData.hatBall, hc, Metric.mem_ball]
      rw [dist_comm, hdist_eq]
      exact hsqrt_lt






theorem seqWeights_data (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k) (i0 : Fin (pb.A r))
    {s : Set (X.obj (L.φ k)).M}
    (hcover : s ⊆ ⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) :
    centerAverage.WeightDataOn s
      (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
      (rawWeights
        (cutRaw (seqAtom hd hD P L pb r k i0)
          (seqAtom hd hD P L pb r k) i0)) := by
  apply cutWeights_data
  · intro x _hx
    exact seqAtom_Icc hd hD P L pb r k i0 x
  · intro x _hx gamma
    exact seqAtom_nonneg hd hD P L pb r k gamma x
  · intro x hx
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp (hcover hx)
    refine ⟨gamma, ?_⟩
    rw [seqAtom_one hd hD P L pb r k hgp gamma hgamma]
    exact zero_lt_one
  · intro x _hx hne
    exact lt_of_le_of_ne (seqAtom_nonneg hd hD P L pb r k i0 x) (Ne.symm hne)
  · intro x _hx gamma hne
    exact seqAtom_mem_hat hd hD P L pb r k hgp gamma hne



theorem seqWeights_ev (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (i0 : Fin (pb.A r)) :
    ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn (L.hatSourceBall hd P r k)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k i0)
            (seqAtom hd hD P L pb r k) i0)) := by
  filter_upwards [L.innerBall_cover hd hD P hre pb r, hgp] with k hcover hgpAt
  exact seqWeights_data hd hD P L pb r k hgpAt i0 hcover

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
private theorem packA_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    0 < pb.A r := by
  let O := (X.obj 0).basepoint
  have hself : hd.dist 0 O O = 0 := by
    have hz : ENNReal.ofReal (hd.dist 0 O O) = 0 := by
      letI : EMetricSpace (X.obj 0).M := (X.obj 0).emetricSpace
      rw [← hre.edist_eq 0 O O, edist_self]
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (hre.dist_nonneg 0 O O)
  have hcard := pb.card_le 0 r ({O} : Finset (X.obj 0).M) (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst x
    change hd.dist 0 O O ≤ r
    simpa only [hself] using hr) (by
      intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx hy
      exact False.elim (hxy (hx.trans hy.symm)))
  simpa only [Finset.card_singleton, Nat.succ_le_iff] using hcard



noncomputable def baseIndex (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    Fin (pb.A r) :=
  ⟨0, packA_pos hd hre pb hr⟩

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem baseIndex_val (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    (baseIndex hd hre pb hr : Nat) = 0 := rfl


theorem seqAtom_base (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k) :
    seqAtom hd hD P L pb r k (baseIndex hd hre pb hr)
        (X.obj (L.φ k)).basepoint = 1 := by
  apply seqAtom_one hd hD P L pb r k hgp
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  simp only [NetLimitData.innerBall, baseIndex_val, seqCenter_zero, Metric.mem_ball,
    dist_self]
  exact mul_pos (by norm_num) (hd.lambda_pos hD (L.rInf 0))



theorem seqWeights_base (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k) :
    let i0 := baseIndex hd hre pb hr
    let num := cutRaw (seqAtom hd hD P L pb r k i0)
      (seqAtom hd hD P L pb r k) i0
    rawWeights num (X.obj (L.φ k)).basepoint i0 = 1 ∧
      ∀ j, j ≠ i0 → rawWeights num (X.obj (L.φ k)).basepoint j = 0 := by
  dsimp only
  have hbase := seqAtom_base hd hD P L hre pb hr k hgp
  have hdelta := cutRaw_delta
    (cut := seqAtom hd hD P L pb r k (baseIndex hd hre pb hr))
    (a := seqAtom hd hD P L pb r k) (i0 := baseIndex hd hre pb hr)
    (x := (X.obj (L.φ k)).basepoint) hbase
  apply rawWeights_delta (baseIndex hd hre pb hr) hdelta.2
  rw [hdelta.1, hbase]
  exact one_ne_zero



theorem seqWeights_zero_ev (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (hgp : Item3GpScaleTail (I := I) hd D P L pb r) :
    ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn (L.hatSourceBall hd P r k)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k (baseIndex hd hre pb hr))
            (seqAtom hd hD P L pb r k) (baseIndex hd hre pb hr))) :=
  seqWeights_ev hd hD P L hre pb r hgp (baseIndex hd hre pb hr)

end HCGCompactness
end DifferentialGeometry
