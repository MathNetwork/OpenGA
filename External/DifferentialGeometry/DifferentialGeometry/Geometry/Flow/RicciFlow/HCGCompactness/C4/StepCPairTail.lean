import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransitionOverlap
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPairGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCTransitionRefine










noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}



def InterSlot
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (alpha : LiveSlot L pb r) :=
  { beta : LiveSlot L pb r // ∀ᶠ k in atTop,
    BInter hd D P L.lamInf
      (alpha.1 : Nat) (beta.1 : Nat) (L.φ k) }



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem inter_slot_of_binter
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {k : Nat} (alpha : LiveSlot L pb r) {gamma : Fin (pb.A r)}
    (hgammaStable :
      (seqCenter hd D P (L.φ k) (gamma : Nat)).isSome =
        L.alive (gamma : Nat))
    (hcurrent : BInter hd D P L.lamInf
      (alpha.1 : Nat) (gamma : Nat) (L.φ k))
    (htail : ∀ᶠ j in atTop,
      BInter hd D P L.lamInf
        (alpha.1 : Nat) (gamma : Nat) (L.φ j)) :
    ∃ target : InterSlot L pb r alpha, target.1.1 = gamma := by
  obtain ⟨_x, y, _hx, hy, _hinter⟩ := hcurrent
  have hgammaLive : L.alive (gamma : Nat) = true := by
    simpa only [hy, Option.isSome_some] using hgammaStable.symm
  exact ⟨⟨⟨gamma, hgammaLive⟩, htail⟩, rfl⟩



theorem MetricCompactnessInputs.atom_trans_small
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) inp.decay inp.D P L inp.pack r k)
    (x : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A r))
    (hC2 :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      8 * L.lamInf (gamma : Nat) ≤
      Geometry.Riemannian.expMapC2Radius
        (I := I) (X.obj (L.φ k)).metric
        (seqCenterD inp.decay P L k (gamma : Nat)))
    (z : E)
    (hne :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      seqAtom inp.decay inp.hD P L inp.pack r k gamma
      (Geometry.Riemannian.NormalCoordinates.expMapDiffeo
        (I := I) (X.obj (L.φ k)).metric x z) ≠ 0) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    normalTransition (I := I) (X.obj (L.φ k)) x
        (seqCenterD inp.decay P L k (gamma : Nat)) z ∈
      Metric.ball 0 (6 * L.lamInf (gamma : Nat)) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  cases hc : seqCenter inp.decay inp.D P (L.φ k) (gamma : Nat) with
  | none =>
      exact False.elim (hne (by simp [seqAtom, hc]))
  | some y =>
      have hyD : seqCenterD inp.decay P L k (gamma : Nat) = y := by
        simp [seqCenterD, hc]
      rw [hyD] at hC2 ⊢
      let q := Geometry.Riemannian.NormalCoordinates.expMapDiffeo
        (I := I) (X.obj (L.φ k)).metric x z
      have hqHat : q ∈ L.hatBall inp.decay inp.D P inp.pack r k gamma :=
        seqAtom_mem_hat inp.decay inp.hD P L inp.pack r k hgp gamma hne
      have hqBall : q ∈ Metric.ball y (4 * L.lamInf (gamma : Nat)) := by
        simpa only [NetLimitData.hatBall, hc] using hqHat
      have hhalf : (1 / 2 : Real) ≤ Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj (L.φ k)).metric y :=
        inp.normalBounds.half_le_gpConst (L.φ k) y
      have hsqrtPos : 0 < Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj (L.φ k)).metric y) :=
        Real.sqrt_pos.mpr ((by norm_num : (0 : Real) < 1 / 2).trans_le hhalf)
      have hsqrtHalf : (2 / 3 : Real) < Real.sqrt (1 / 2 : Real) := by
        have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
        have hn := Real.sqrt_nonneg (1 / 2 : Real)
        nlinarith
      have hsqrt : (2 / 3 : Real) < Real.sqrt
          (Geometry.Riemannian.gpCoerciveConst
            (I := I) (X.obj (L.φ k)).metric y) :=
        hsqrtHalf.trans_le (Real.sqrt_le_sqrt hhalf)
      have hlam : 0 < L.lamInf (gamma : Nat) :=
        inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))
      have hcoord :
          (4 * L.lamInf (gamma : Nat)) /
              Real.sqrt (Geometry.Riemannian.gpCoerciveConst
                (I := I) (X.obj (L.φ k)).metric y) <
            6 * L.lamInf (gamma : Nat) := by
        rw [div_lt_iff₀ hsqrtPos]
        nlinarith
      have htarget := properBall_to_exp (I := I) (X.obj (L.φ k))
        (P (L.φ k)).ms (P (L.φ k)).realizes
        (c := y) (R := 4 * L.lamInf (gamma : Nat))
        (σ := 6 * L.lamInf (gamma : Nat)) (hgp gamma y hc) hcoord
      have hVy : Metric.ball (0 : E) (6 * L.lamInf (gamma : Nat)) ⊆
          Metric.ball 0 (Geometry.Riemannian.expMapC2Radius
            (I := I) (X.obj (L.φ k)).metric y) :=
        Metric.ball_subset_ball ((by nlinarith :
          6 * L.lamInf (gamma : Nat) ≤ 8 * L.lamInf (gamma : Nat)).trans hC2)
      have hmaps : Set.MapsTo
          (fun w : E => Geometry.Riemannian.NormalCoordinates.expMapDiffeo
            (I := I) (X.obj (L.φ k)).metric x w)
          ({z} : Set E)
          ((fun v : E => Geometry.Riemannian.Exponential.expMap
            (I := I) (X.obj (L.φ k)).metric y
              (show TangentSpace I y from v)) ''
            Metric.ball 0 (6 * L.lamInf (gamma : Nat))) := by
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact htarget (Metric.ball_subset_closedBall hqBall)
      exact normalTrans_mapsTo (I := I) (X.obj (L.φ k)) x y hVy hmaps
        (Set.mem_singleton z)



theorem MetricCompactnessInputs.weight_trans_small
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) inp.decay inp.D P L inp.pack r k)
    (beta : ∀ j : Nat, (X.obj (L.φ j)).M)
    (i0 gamma : Fin (inp.pack.A r))
    (hC2 :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      8 * L.lamInf (gamma : Nat) ≤
        Geometry.Riemannian.expMapC2Radius
          (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (gamma : Nat)))
    (z : E)
    (hweight : rawWeights
      (cutRaw
        (seqAtomChart (I := I) inp.decay inp.hD P L inp.pack r beta i0 k)
        (fun target =>
          seqAtomChart (I := I) inp.decay inp.hD P L inp.pack r beta target k)
        i0) z gamma ≠ 0) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    normalTransition (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD inp.decay P L k (gamma : Nat)) z ∈
      Metric.ball 0 (6 * L.lamInf (gamma : Nat)) := by
  apply inp.atom_trans_small P L r k hgp (beta k) gamma hC2 z
  simpa only [seqAtomChart] using
    (num_ne_of_cut_ne (num_ne_of_raw_ne hweight))




theorem MetricCompactnessInputs.pair_exp_maps_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    (α β : LiveSlot L inp.pack r)
    (hinter : ∀ᶠ k in atTop,
      BInter inp.decay inp.D P L.lamInf (α.1 : Nat) (β.1 : Nat) (L.φ k)) :
    ∀ᶠ k in atTop,
      let x := seqCenterD inp.decay P L k (α.1 : Nat)
      let y := seqCenterD inp.decay P L k (β.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      Set.MapsTo
        (fun z : E => Geometry.Riemannian.NormalCoordinates.expMapDiffeo
          (I := I) (X.obj (L.φ k)).metric x z)
        (Metric.ball 0 (8 * L.lamInf (α.1 : Nat)))
        ((fun v : E => Geometry.Riemannian.Exponential.expMap
          (I := I) (X.obj (L.φ k)).metric y (show TangentSpace I y from v)) ''
            Metric.ball 0
              (item3RadiusFactor inp.decay inp.D * L.lamInf (β.1 : Nat))) := by
  have hrad : Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
      (item3RadiusFactor inp.decay inp.D) :=
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r
  have hgp := inp.normalRadius.halfGpScaleTail inp.hD
    (item3Factor_pos inp.decay inp.D) hradRatio
    P inp.realizes L inp.pack r
  have hα := seqCenterD_live inp.decay P L (α.1 : Nat) α.2
  have hβ := seqCenterD_live inp.decay P L (β.1 : Nat) β.2
  have hfreq : ∃ᶠ k in atTop,
      BInter inp.decay inp.D P L.lamInf
        (α.1 : Nat) (β.1 : Nat) (L.φ k) := hinter.frequently
  filter_upwards [hinter, hrad, hgp, hα, hβ] with k hk hradk hgpk hx hy
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hzero : (0 : E) ∈ Metric.ball 0
      (inp.normalBounds.radius (L.φ k)
        (seqCenterD inp.decay P L k (α.1 : Nat))) := by
    rw [Metric.mem_ball, dist_self]
    exact inp.normalBounds.radius_pos (L.φ k)
      (seqCenterD inp.decay P L k (α.1 : Nat))
  have hmetric : ∀ z : E,
      (X.obj (L.φ k)).metric.inner
          (seqCenterD inp.decay P L k (α.1 : Nat)) z z ≤ 2 * ‖z‖ ^ 2 := by
    intro z
    simpa only [normalMetric_zero (I := I) (X.obj (L.φ k))
      (seqCenterD inp.decay P L k (α.1 : Nat))] using
        (inp.normalBounds.metric_equiv (L.φ k)
          (seqCenterD inp.decay P L k (α.1 : Nat)) 0 hzero z).2
  exact L.pair_exp_maps inp.decay inp.hD P inp.pack r α.1 β.1
    hfreq k hk hx hy hradk hmetric
    (inp.normalBounds.half_le_gpConst
      (L.φ k) (seqCenterD inp.decay P L k (β.1 : Nat)))
    (hgpk β.1 (seqCenterD inp.decay P L k (β.1 : Nat)) hy)




theorem MetricCompactnessInputs.pair_overlap_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    (α β : LiveSlot L inp.pack r)
    (hinter : ∀ᶠ k in atTop,
      BInter inp.decay inp.D P L.lamInf (α.1 : Nat) (β.1 : Nat) (L.φ k)) :
    ∀ᶠ k in atTop,
      let x := seqCenterD inp.decay P L k (α.1 : Nat)
      let y := seqCenterD inp.decay P L k (β.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      let U := Metric.ball 0 (8 * L.lamInf (α.1 : Nat))
      let Va := Metric.ball 0
        (item3RadiusFactor inp.decay inp.D * L.lamInf (β.1 : Nat))
      U ⊆ Metric.ball 0 (inp.normalBounds.radius (L.φ k) x) ∧
        Va ⊆ Metric.ball 0 (inp.normalBounds.radius (L.φ k) y) ∧
        U ⊆ Metric.ball 0
          (Geometry.Riemannian.expMapC2Radius
            (I := I) (X.obj (L.φ k)).metric x) ∧
        Va ⊆ Metric.ball 0
          (Geometry.Riemannian.expMapC2Radius
            (I := I) (X.obj (L.φ k)).metric y) ∧
        ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) (X.obj (L.φ k)) x y) U ∧
        NormalOverlapOn (I := I) (X.obj (L.φ k)) x y U ∧
        Set.MapsTo (normalTransition (I := I) (X.obj (L.φ k)) x y) U Va := by
  have hmaps := inp.pair_exp_maps_tail hradD hradRatio P L r α β hinter
  have hrad : Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
      (item3RadiusFactor inp.decay inp.D) :=
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r
  have hmetric := inp.normalRadius.metricScaleTail inp.hD
    (item3Factor_pos inp.decay inp.D) hradRatio
    P inp.realizes L inp.pack r
  have hα := seqCenterD_live inp.decay P L (α.1 : Nat) α.2
  have hβ := seqCenterD_live inp.decay P L (β.1 : Nat) β.2
  filter_upwards [hmaps, hrad, hmetric, hα, hβ]
    with k hmapsk hradk hmetrick hx hy
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hExp : (1 : Real) ≤
      Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
    rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr
      (mul_nonneg inp.decay.C_nonneg
        (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
  have hfactor : (8 : Real) ≤ item3RadiusFactor inp.decay inp.D := by
    rw [item3RadiusFactor]
    nlinarith
  have hUmetric : Metric.ball (0 : E) (8 * L.lamInf (α.1 : Nat)) ⊆
      Metric.ball 0 (inp.normalBounds.radius (L.φ k)
        (seqCenterD inp.decay P L k (α.1 : Nat))) :=
    Metric.ball_subset_ball <| (mul_le_mul_of_nonneg_right hfactor
      (inp.decay.lambda_pos inp.hD (L.rInf (α.1 : Nat))).le).trans
        (hmetrick α.1 (seqCenterD inp.decay P L k (α.1 : Nat)) hx)
  have hVmetric : Metric.ball (0 : E)
        (item3RadiusFactor inp.decay inp.D * L.lamInf (β.1 : Nat)) ⊆
      Metric.ball 0 (inp.normalBounds.radius (L.φ k)
        (seqCenterD inp.decay P L k (β.1 : Nat))) :=
    Metric.ball_subset_ball <|
      hmetrick β.1 (seqCenterD inp.decay P L k (β.1 : Nat)) hy
  have hUx : Metric.ball (0 : E) (8 * L.lamInf (α.1 : Nat)) ⊆
      Metric.ball 0 (Geometry.Riemannian.expMapC2Radius
        (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (α.1 : Nat))) := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    exact hz.trans_le <| (mul_le_mul_of_nonneg_right hfactor
      (inp.decay.lambda_pos inp.hD (L.rInf (α.1 : Nat))).le).trans
        (hradk α.1 (seqCenterD inp.decay P L k (α.1 : Nat)) hx).2
  have hVy : Metric.ball (0 : E)
        (item3RadiusFactor inp.decay inp.D * L.lamInf (β.1 : Nat)) ⊆
      Metric.ball 0 (Geometry.Riemannian.expMapC2Radius
        (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (β.1 : Nat))) := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    exact hz.trans_le
      (hradk β.1 (seqCenterD inp.decay P L k (β.1 : Nat)) hy).2
  have hsmooth := contDiffOn_normalTransition (I := I) (X.obj (L.φ k))
    (seqCenterD inp.decay P L k (α.1 : Nat))
    (seqCenterD inp.decay P L k (β.1 : Nat)) hUx
    (hmapsk.mono_right (Set.image_mono hVy))
  exact ⟨hUmetric, hVmetric, hUx, hVy, hsmooth,
    normalOverlap_of_map (I := I) (X.obj (L.φ k))
      (seqCenterD inp.decay P L k (α.1 : Nat))
      (seqCenterD inp.decay P L k (β.1 : Nat)) hUx hVy hmapsk,
    normalTrans_mapsTo (I := I) (X.obj (L.φ k))
      (seqCenterD inp.decay P L k (α.1 : Nat))
      (seqCenterD inp.decay P L k (β.1 : Nat)) hVy hmapsk⟩




theorem MetricCompactnessInputs.exists_pair_trans
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    {ι : Type*} [Finite ι]
    (α β : ι → LiveSlot L inp.pack r)
    (hinter : ∀ i, ∀ᶠ k in atTop,
      BInter inp.decay inp.D P L.lamInf
        ((α i).1 : Nat) ((β i).1 : Nat) (L.φ k)) :
    let x : ι → ∀ k : Nat, (X.obj (L.φ k)).M :=
      fun i k => seqCenterD inp.decay P L k ((α i).1 : Nat)
    let y : ι → ∀ k : Nat, (X.obj (L.φ k)).M :=
      fun i k => seqCenterD inp.decay P L k ((β i).1 : Nat)
    let U : ι → Set E := fun i =>
      Metric.ball 0 (8 * L.lamInf ((α i).1 : Nat))
    let V : ι → Set E := fun i =>
      Metric.ball 0 (8 * L.lamInf ((β i).1 : Nat))
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∃ Jinf : ι → E → E, ∃ Jbarinf : ι → E → E,
        ∀ i,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf i) (U i) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf i) (V i) ∧
          ContinuousOn (Jinf i) (U i) ∧
          ContinuousOn (Jbarinf i) (V i) ∧
          MapCInfConvOnCompacts (U i)
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (x i (phi k)) (y i (phi k))) (Jinf i) ∧
          MapCInfConvOnCompacts (V i)
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (y i (phi k)) (x i (phi k))) (Jbarinf i) ∧
          (∀ z, z ∈ U i → Jinf i z ∈ V i → Jbarinf i (Jinf i z) = z) ∧
          (∀ w, w ∈ V i → Jbarinf i w ∈ U i → Jinf i (Jbarinf i w) = w) := by
  classical
  dsimp only
  refine existsTransTail (I := I) (X := X.subseq L.φ)
    (NormalCoordMetricBoundInput.subseq (I := I) inp.normalBounds L.φ)
    (fun i k => seqCenterD inp.decay P L k ((α i).1 : Nat))
    (fun i k => seqCenterD inp.decay P L k ((β i).1 : Nat))
    (fun i => Metric.ball 0 (8 * L.lamInf ((α i).1 : Nat)))
    (fun i => Metric.ball 0 (8 * L.lamInf ((β i).1 : Nat)))
    (fun i => Metric.ball 0
      (item3RadiusFactor inp.decay inp.D * L.lamInf ((α i).1 : Nat)))
    (fun i => Metric.ball 0
      (item3RadiusFactor inp.decay inp.D * L.lamInf ((β i).1 : Nat)))
    (fun _ => Metric.isOpen_ball) (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.isOpen_ball) (fun _ => Metric.isOpen_ball) ?_ ?_ ?_
  · intro i
    refine ⟨max (item3RadiusFactor inp.decay inp.D *
      L.lamInf ((α i).1 : Nat)) 0, ?_⟩
    intro z hz
    exact (le_of_lt (mem_ball_zero_iff.mp hz)).trans (le_max_left _ _)
  · intro i
    refine ⟨max (item3RadiusFactor inp.decay inp.D *
      L.lamInf ((β i).1 : Nat)) 0, ?_⟩
    intro z hz
    exact (le_of_lt (mem_ball_zero_iff.mp hz)).trans (le_max_left _ _)
  · intro i
    have hinterRev : ∀ᶠ k in atTop,
        BInter inp.decay inp.D P L.lamInf
          ((β i).1 : Nat) ((α i).1 : Nat) (L.φ k) :=
      (hinter i).mono fun _ hk =>
        BInter.symm inp.decay inp.D P L.lamInf hk
    have hforward := inp.pair_overlap_tail hradD hradRatio P L r
      (α i) (β i) (hinter i)
    have hreverse := inp.pair_overlap_tail hradD hradRatio P L r
      (β i) (α i) hinterRev
    filter_upwards [hforward, hreverse] with k hf hr
    exact
      { Umetric := hf.1
        Vmetric := hr.1
        Uametric := hr.2.1
        Vametric := hf.2.1
        Uexp := hf.2.2.1
        Vexp := hr.2.2.1
        Uaexp := hr.2.2.2.1
        Vaexp := hf.2.2.2.1
        J := hf.2.2.2.2.1
        Jbar := hr.2.2.2.2.1
        ovlJ := hf.2.2.2.2.2.1
        ovlJbar := hr.2.2.2.2.2.1
        mapJ := hf.2.2.2.2.2.2
        mapJbar := hr.2.2.2.2.2.2
        left := fun _ hz => (hf.2.2.2.2.2.1).cancel hz
        right := fun _ hw => (hr.2.2.2.2.2.1).cancel hw }

end HCGCompactness
end DifferentialGeometry
