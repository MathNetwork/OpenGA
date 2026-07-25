import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageComparison

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}




theorem liveCenters_radial
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (s : Real)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k l : Nat, N ≤ k → N ≤ l →
      ∀ alpha : LiveSlot L inp.pack s,
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
        dist (seqCenterD inp.decay P Lphi l (alpha.1 : Nat)) Yl.basepoint <
          dist (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) Yk.basepoint + eps := by
  let Lphi := L.subseq hphi
  have hrad : ∀ᶠ n in Filter.atTop, ∀ alpha : LiveSlot L inp.pack s,
      |seqRadius inp.decay inp.D P (Lphi.φ n) (alpha.1 : Nat) -
        L.rInf (alpha.1 : Nat)| < eps / 2 :=
    Filter.eventually_all.mpr fun alpha =>
      (Lphi.tendsto (alpha.1 : Nat)).eventually
        (Metric.ball_mem_nhds (L.rInf (alpha.1 : Nat)) (half_pos heps))
  rw [Filter.eventually_atTop] at hrad
  obtain ⟨N, hN⟩ := hrad
  refine ⟨N, ?_⟩
  intro k l hk hl alpha
  dsimp only
  letI : MetricSpace (X.obj (Lphi.φ k)).M := (P (Lphi.φ k)).ms
  letI : MetricSpace (X.obj (Lphi.φ l)).M := (P (Lphi.φ l)).ms
  rw [← seqCenterD_dist_eq inp.decay P Lphi l (alpha.1 : Nat),
    ← seqCenterD_dist_eq inp.decay P Lphi k (alpha.1 : Nat)]
  have hk' := abs_lt.mp (hN k hk alpha)
  have hl' := abs_lt.mp (hN l hl alpha)
  linarith




theorem HasStageJetData.mapsTo_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {s : Real} (hs : 0 ≤ s)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack s → Set E)
    (aInf : (alpha : LiveSlot L inp.pack s) →
      Fin (inp.pack.A s) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack s) →
      InterSlot L inp.pack s alpha → E → E)
    (gInf : LiveSlot L inp.pack s →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hs phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R0 R1 : Real)
    (hroom : R0 + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < R1)
    (hR1s : R1 < s) :
    ∃ N : Nat, ∀ k l : Nat, N ≤ k → N ≤ l →
      let Lphi := L.subseq hphi
      Set.MapsTo (stageComparisonMap inp P Lphi s hs hconn k l)
        (Lphi.hatSourceBall inp.decay P R0 k)
        (Lphi.hatSourceBall inp.decay P R1 l) := by
  classical
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  have hraw := hdata
  dsimp only [HasSuppConvData] at hraw
  rcases hraw with
    ⟨_hU, hU8, hC0, _hC1, hC01, hC1U, hconvex, hzero,
      hbuffer, _hcore, hgeom, _hlim, _hweight, _htrans, _hsmooth⟩
  let Lphi := L.subseq hphi
  let lam0 := inp.decay.lambda inp.D 0
  have hlam0 : 0 < lam0 := inp.decay.lambda_pos inp.hD 0
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hcoef : 0 < (4 + 8 * Real.sqrt 2) * lam0 := by positivity
  have hR0R1 : R0 < R1 := by linarith
  have hR0s : R0 < s := hR0R1.trans hR1s
  let gap := R1 - (R0 + (4 + 8 * Real.sqrt 2) * lam0)
  have hgap : 0 < gap := by
    dsimp only [gap, lam0]
    exact sub_pos.mpr hroom
  obtain ⟨eta, heta, hbuffer⟩ := hbuffer
  let epsA : LiveSlot L inp.pack s → Real := fun alpha =>
    min (eta alpha / 2) (gap / 8)
  have hepsA : ∀ alpha, 0 < epsA alpha := by
    intro alpha
    dsimp only [epsA]
    exact lt_min (div_pos (heta alpha) (by norm_num))
      (div_pos hgap (by norm_num))
  have hjetA : ∀ alpha : LiveSlot L inp.pack s,
      HasStageJetTail (I := I) inp P L hs phi hphi hconn C0 R0 0
        (epsA alpha) := fun alpha =>
    hjets R0 hR0s 0 (epsA alpha) (hepsA alpha)
  choose Njet hNjet using hjetA
  let Njets := Finset.univ.sup Njet
  obtain ⟨Nrad, hrad⟩ := liveCenters_radial inp P L s phi hphi
    (gap / 4) (div_pos hgap (by norm_num))
  refine ⟨max Nrad Njets, ?_⟩
  intro k l hk hl
  have hkRad : Nrad ≤ k := (le_max_left _ _).trans hk
  have hlRad : Nrad ≤ l := (le_max_left _ _).trans hl
  dsimp only
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let F := stageComparisonMap inp P Lphi s hs hconn k l
  intro x hx
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P s k :=
    cball_subset_of_le hR0s.le
      (by simpa only [NetLimitData.hatSourceBall, Yk] using hx)
  obtain ⟨alpha, z, hzx, hzbuffer⟩ := hbuffer k x hxLarge
  have hzSelf : z ∈ Metric.closedBall z (eta alpha) := by
    simpa only [Metric.mem_closedBall, dist_self] using (heta alpha).le
  have hzInt : z ∈ interior (C0 alpha) := hzbuffer hzSelf
  have hzC0 : z ∈ C0 alpha := interior_subset hzInt
  have hzU : z ∈ U alpha :=
    hC1U alpha (interior_subset (hC01 alpha hzC0))
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric cl
  have hxEq : chiK.symm z = x := by
    simpa only [chiK, ck, Yk, Lphi] using hzx
  have hxCoord : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R0 k := by
    rwa [hxEq]
  have hNjetMax : Njet alpha ≤ Njets :=
    Finset.le_sup (s := Finset.univ) (f := Njet) (Finset.mem_univ alpha)
  have hkJet : Njet alpha ≤ k := hNjetMax.trans ((le_max_right _ _).trans hk)
  have hlJet : Njet alpha ≤ l := hNjetMax.trans ((le_max_right _ _).trans hl)
  have hjet := hNjet alpha k hkJet l hlJet alpha z hzC0 hzInt hxCoord
  have hgeomK := (hgeom k).1 alpha
  have hgeomL := (hgeom l).1 alpha
  obtain ⟨_hRadK, _hExpK, hmapK⟩ := hgeomK
  obtain ⟨hRadL, hExpL, _hmapL⟩ := hgeomL
  have hxHat : x ∈
      Lphi.hatBall inp.decay inp.D P inp.pack s k alpha.1 := by
    simpa only [Lphi, hzx] using (hmapK hzU).1
  have hxCenter : dist x ck < 4 * L.lamInf (alpha.1 : Nat) := by
    simpa only [ck, Lphi, NetLimitData.subseq_lamInf] using
      hat_dist_centerD inp.decay P Lphi inp.pack s hxHat
  have hlam : L.lamInf (alpha.1 : Nat) ≤ lam0 := by
    dsimp only [lam0, NetLimitData.lamInf]
    exact inp.decay.lambda_antitone inp.hD (L.rInf_mem (alpha.1 : Nat)).1
  let w := chiL (F x)
  have hcoord : dist w z ≤ epsA alpha := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq, dist_eq_norm,
      w, F, chiK, chiL, ck, cl, Yk, Yl, Lphi, hxEq] using
        hjet.2.2 0 le_rfl
  have hepsEta : epsA alpha ≤ eta alpha := by
    have hhalf : eta alpha / 2 ≤ eta alpha := by linarith [heta alpha]
    exact (min_le_left _ _).trans hhalf
  have hwBall : w ∈ Metric.closedBall z (eta alpha) := by
    change dist w z ≤ eta alpha
    exact hcoord.trans hepsEta
  have hwInt : w ∈ interior (C0 alpha) := hzbuffer hwBall
  have hwC0 : w ∈ C0 alpha := interior_subset hwInt
  have hseg : segment Real w 0 ⊆ U alpha := by
    intro q hq
    have hqC0 := (hconvex alpha).segment_subset hwC0 (hzero alpha) hq
    exact hC1U alpha (interior_subset (hC01 alpha hqC0))
  have hEquiv : NormalCoordMetricEquivOn (I := I) Yl cl (U alpha) := by
    intro q hq v
    exact inp.normalBounds.metric_equiv (Lphi.φ l) cl q (hRadL hq) v
  have hUtgt : U alpha ⊆ chiL.target := by
    intro q hq
    have hqBall := hExpL hq
    have hqNorm : ‖q‖ < expMapC2Radius (I := I) Yl.metric cl := by
      simpa only [Metric.mem_ball, dist_zero_right] using hqBall
    simpa only [chiL] using
      Geometry.Riemannian.ball_subset_normalChartAt_target
        (I := I) Yl.metric cl hqNorm
  have hman := NormalCoordMetricEquivOn.symm_dist_le
    (I := I) Yl (P (Lphi.φ l)) hEquiv hUtgt hseg
  have hFw : chiL.symm w = F x := by
    have htarget : F x ∈ (normalExpPD (I := I) Yl cl).target := by
      simpa only [F, chiK, ck, cl, Yk, Yl, Lphi, hxEq] using hjet.1
    change (normalExpPD (I := I) Yl cl)
      ((normalExpPD (I := I) Yl cl).symm (F x)) = F x
    exact (normalExpPD (I := I) Yl cl).right_inv htarget
  have hzeroL : chiL.symm (0 : E) = cl := by
    simpa only [chiL] using
      NormalCoordinates.normalChartAt_symm_zero (I := I) Yl.metric cl
  rw [hFw, hzeroL] at hman
  have hzNorm : ‖z‖ < 8 * L.lamInf (alpha.1 : Nat) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hU8 alpha hzU
  have hw0 : dist w 0 < epsA alpha + 8 * L.lamInf (alpha.1 : Nat) := by
    calc
      dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ < epsA alpha + 8 * L.lamInf (alpha.1 : Nat) := by
        rw [dist_zero_right]
        exact add_lt_add_of_le_of_lt hcoord hzNorm
  have hepsGap : epsA alpha ≤ gap / 8 := min_le_right _ _
  have hfirst : Real.sqrt 2 * epsA alpha ≤ gap / 4 := by
    calc
      Real.sqrt 2 * epsA alpha ≤ 2 * epsA alpha :=
        mul_le_mul_of_nonneg_right hsqrt2 (hepsA alpha).le
      _ ≤ 2 * (gap / 8) :=
        mul_le_mul_of_nonneg_left hepsGap (by norm_num)
      _ = gap / 4 := by ring
  have hsecond : Real.sqrt 2 * (8 * L.lamInf (alpha.1 : Nat)) ≤
      8 * Real.sqrt 2 * lam0 := by
    calc
      Real.sqrt 2 * (8 * L.lamInf (alpha.1 : Nat)) ≤
          Real.sqrt 2 * (8 * lam0) := by
        gcongr
      _ = 8 * Real.sqrt 2 * lam0 := by ring
  have hFCenter : dist (F x) cl < gap / 4 + 8 * Real.sqrt 2 * lam0 := by
    calc
      dist (F x) cl ≤ Real.sqrt 2 * dist w 0 := hman
      _ < Real.sqrt 2 *
          (epsA alpha + 8 * L.lamInf (alpha.1 : Nat)) :=
        mul_lt_mul_of_pos_left hw0 hsqrt0
      _ = Real.sqrt 2 * epsA alpha +
          Real.sqrt 2 * (8 * L.lamInf (alpha.1 : Nat)) := by ring
      _ ≤ gap / 4 + 8 * Real.sqrt 2 * lam0 := add_le_add hfirst hsecond
  have hxRad : dist x Yk.basepoint ≤ R0 := by
    simpa only [NetLimitData.hatSourceBall, Metric.mem_closedBall, Yk] using hx
  have hkCenter : dist ck Yk.basepoint < R0 + 4 * lam0 := by
    calc
      dist ck Yk.basepoint ≤ dist ck x + dist x Yk.basepoint := dist_triangle _ _ _
      _ < 4 * L.lamInf (alpha.1 : Nat) + R0 := by
        rw [dist_comm ck x]
        exact add_lt_add_of_lt_of_le hxCenter hxRad
      _ ≤ 4 * lam0 + R0 := by gcongr
      _ = R0 + 4 * lam0 := by ring
  have hradPair := hrad k l hkRad hlRad alpha
  have hlCenter : dist cl Yl.basepoint < R0 + 4 * lam0 + gap / 4 := by
    dsimp only [Lphi, Yk, Yl, ck, cl] at hradPair
    linarith
  have hfinal : dist (F x) Yl.basepoint < R1 := by
    calc
      dist (F x) Yl.basepoint ≤
          dist (F x) cl + dist cl Yl.basepoint := dist_triangle _ _ _
      _ < (gap / 4 + 8 * Real.sqrt 2 * lam0) +
          (R0 + 4 * lam0 + gap / 4) := add_lt_add hFCenter hlCenter
      _ < R1 := by
        dsimp only [gap, lam0]
        linarith
  change dist (F x) Yl.basepoint ≤ R1
  exact hfinal.le




theorem HasStageJetData.return_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {s : Real} (hs : 0 ≤ s)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack s → Set E)
    (aInf : (alpha : LiveSlot L inp.pack s) →
      Fin (inp.pack.A s) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack s) →
      InterSlot L inp.pack s alpha → E → E)
    (gInf : LiveSlot L inp.pack s →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hs phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R0 R1 : Real)
    (hroom : R0 + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < R1)
    (hR1s : R1 < s) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k l : Nat, N ≤ k → N ≤ l →
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
      ∀ x ∈ Lphi.hatSourceBall inp.decay P R0 k,
        dist
          (stageComparisonMap inp P Lphi s hs hconn l k
            (stageComparisonMap inp P Lphi s hs hconn k l x))
          x < eps := by
  classical
  obtain ⟨Nmap, hmap⟩ := HasStageJetData.mapsTo_tail inp P L hs phi hphi
    hconn U C0 C1 aInf Jinf Jbarinf gInf hstage R0 R1 hroom hR1s
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  have hraw := hdata
  dsimp only [HasSuppConvData] at hraw
  rcases hraw with
    ⟨_hU, _hU8, _hC0, _hC1, hC01, hC1U, hconvex, hzero,
      hbuffer, _hcore, hgeom, _hlim, _hweight, _htrans, _hsmooth⟩
  let Lphi := L.subseq hphi
  have hlam0 : 0 < inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_pos inp.hD 0
  have hcoef : 0 <
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 := by positivity
  have hR0R1 : R0 < R1 := by linarith
  have hR0s : R0 < s := hR0R1.trans hR1s
  obtain ⟨eta, heta, hbuffer⟩ := hbuffer
  let delta : LiveSlot L inp.pack s → Real := fun alpha =>
    min (eta alpha / 4) (eps / 8)
  have hdelta : ∀ alpha, 0 < delta alpha := by
    intro alpha
    dsimp only [delta]
    exact lt_min (div_pos (heta alpha) (by norm_num))
      (div_pos heps (by norm_num))
  have hfwd : ∀ alpha : LiveSlot L inp.pack s,
      HasStageJetTail (I := I) inp P L hs phi hphi hconn C0 R0 0
        (delta alpha) := fun alpha =>
    hjets R0 hR0s 0 (delta alpha) (hdelta alpha)
  have hrev : ∀ alpha : LiveSlot L inp.pack s,
      HasStageJetTail (I := I) inp P L hs phi hphi hconn C0 R1 0
        (delta alpha) := fun alpha =>
    hjets R1 hR1s 0 (delta alpha) (hdelta alpha)
  choose Nfwd hNfwd using hfwd
  choose Nrev hNrev using hrev
  let Nf := Finset.univ.sup Nfwd
  let Nr := Finset.univ.sup Nrev
  refine ⟨max Nmap (max Nf Nr), ?_⟩
  intro k l hk hl
  have hkMap : Nmap ≤ k := (le_max_left _ _).trans hk
  have hlMap : Nmap ≤ l := (le_max_left _ _).trans hl
  dsimp only
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let Fkl := stageComparisonMap inp P Lphi s hs hconn k l
  let Flk := stageComparisonMap inp P Lphi s hs hconn l k
  intro x hx
  have hy := hmap k l hkMap hlMap hx
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P s k :=
    cball_subset_of_le hR0s.le
      (by simpa only [NetLimitData.hatSourceBall, Yk] using hx)
  obtain ⟨alpha, z, hzx, hzbuffer⟩ := hbuffer k x hxLarge
  have hzSelf : z ∈ Metric.closedBall z (eta alpha) := by
    simpa only [Metric.mem_closedBall, dist_self] using (heta alpha).le
  have hzInt : z ∈ interior (C0 alpha) := hzbuffer hzSelf
  have hzC0 : z ∈ C0 alpha := interior_subset hzInt
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric cl
  have hxEq : chiK.symm z = x := by
    simpa only [chiK, ck, Yk, Lphi] using hzx
  have hxCoord : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R0 k := by
    rwa [hxEq]
  have hNf : Nfwd alpha ≤ Nf :=
    Finset.le_sup (s := Finset.univ) (f := Nfwd) (Finset.mem_univ alpha)
  have hNr : Nrev alpha ≤ Nr :=
    Finset.le_sup (s := Finset.univ) (f := Nrev) (Finset.mem_univ alpha)
  have hkF : Nfwd alpha ≤ k :=
    hNf.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hk))
  have hlF : Nfwd alpha ≤ l :=
    hNf.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hl))
  have hkR : Nrev alpha ≤ k :=
    hNr.trans ((le_max_right _ _).trans ((le_max_right _ _).trans hk))
  have hlR : Nrev alpha ≤ l :=
    hNr.trans ((le_max_right _ _).trans ((le_max_right _ _).trans hl))
  have hforward := hNfwd alpha k hkF l hlF alpha z hzC0 hzInt hxCoord
  let w := chiL (Fkl x)
  have hwz : dist w z ≤ delta alpha := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq, dist_eq_norm,
      w, Fkl, chiK, chiL, ck, cl, Yk, Yl, Lphi, hxEq] using
        hforward.2.2 0 le_rfl
  have hdeltaEta : delta alpha ≤ eta alpha / 4 := min_le_left _ _
  have hquarterEta : eta alpha / 4 ≤ eta alpha := by
    linarith [heta alpha]
  have hwBall : w ∈ Metric.closedBall z (eta alpha) := by
    change dist w z ≤ eta alpha
    exact hwz.trans (hdeltaEta.trans hquarterEta)
  have hwInt : w ∈ interior (C0 alpha) := hzbuffer hwBall
  have hwC0 : w ∈ C0 alpha := interior_subset hwInt
  have hFw : chiL.symm w = Fkl x := by
    have htarget : Fkl x ∈ (normalExpPD (I := I) Yl cl).target := by
      simpa only [Fkl, chiK, ck, cl, Yk, Yl, Lphi, hxEq] using hforward.1
    change (normalExpPD (I := I) Yl cl)
      ((normalExpPD (I := I) Yl cl).symm (Fkl x)) = Fkl x
    exact (normalExpPD (I := I) Yl cl).right_inv htarget
  have hyCoord : chiL.symm w ∈ Lphi.hatSourceBall inp.decay P R1 l := by
    rwa [hFw]
  have hreverse := hNrev alpha l hlR k hkR alpha w hwC0 hwInt hyCoord
  let u := chiK (Flk (Fkl x))
  have huw : dist u w ≤ delta alpha := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq, dist_eq_norm,
      u, w, Fkl, Flk, chiK, chiL, ck, cl, Yk, Yl, Lphi, hFw] using
        hreverse.2.2 0 le_rfl
  have huz : dist u z ≤ 2 * delta alpha := by
    calc
      dist u z ≤ dist u w + dist w z := dist_triangle _ _ _
      _ ≤ delta alpha + delta alpha := add_le_add huw hwz
      _ = 2 * delta alpha := by ring
  have htwoDeltaEta : 2 * delta alpha ≤ eta alpha := by
    calc
      2 * delta alpha ≤ 2 * (eta alpha / 4) :=
        mul_le_mul_of_nonneg_left hdeltaEta (by norm_num)
      _ ≤ eta alpha := by linarith [heta alpha]
  have huBall : u ∈ Metric.closedBall z (eta alpha) := by
    change dist u z ≤ eta alpha
    exact huz.trans htwoDeltaEta
  have huInt : u ∈ interior (C0 alpha) := hzbuffer huBall
  have huC0 : u ∈ C0 alpha := interior_subset huInt
  have hseg : segment Real u z ⊆ U alpha := by
    intro q hq
    have hqC0 := (hconvex alpha).segment_subset huC0 hzC0 hq
    exact hC1U alpha (interior_subset (hC01 alpha hqC0))
  have hgeomK := (hgeom k).1 alpha
  obtain ⟨hRadK, hExpK, _hmapK⟩ := hgeomK
  have hEquiv : NormalCoordMetricEquivOn (I := I) Yk ck (U alpha) := by
    intro q hq v
    exact inp.normalBounds.metric_equiv (Lphi.φ k) ck q (hRadK hq) v
  have hUtgt : U alpha ⊆ chiK.target := by
    intro q hq
    have hqBall := hExpK hq
    have hqNorm : ‖q‖ < expMapC2Radius (I := I) Yk.metric ck := by
      simpa only [Metric.mem_ball, dist_zero_right] using hqBall
    simpa only [chiK] using
      Geometry.Riemannian.ball_subset_normalChartAt_target
        (I := I) Yk.metric ck hqNorm
  have hman := NormalCoordMetricEquivOn.symm_dist_le
    (I := I) Yk (P (Lphi.φ k)) hEquiv hUtgt hseg
  have hHu : chiK.symm u = Flk (Fkl x) := by
    have htarget : Flk (Fkl x) ∈ (normalExpPD (I := I) Yk ck).target := by
      simpa only [Flk, chiL, ck, cl, Yk, Yl, Lphi, hFw] using hreverse.1
    change (normalExpPD (I := I) Yk ck)
      ((normalExpPD (I := I) Yk ck).symm (Flk (Fkl x))) = Flk (Fkl x)
    exact (normalExpPD (I := I) Yk ck).right_inv htarget
  rw [hHu, hxEq] at hman
  have hdeltaEps : delta alpha ≤ eps / 8 := min_le_right _ _
  have hcoordEps : dist u z ≤ eps / 4 := by
    calc
      dist u z ≤ 2 * delta alpha := huz
      _ ≤ 2 * (eps / 8) :=
        mul_le_mul_of_nonneg_left hdeltaEps (by norm_num)
      _ = eps / 4 := by ring
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  calc
    dist (Flk (Fkl x)) x ≤ Real.sqrt 2 * dist u z := hman
    _ ≤ 2 * dist u z :=
      mul_le_mul_of_nonneg_right hsqrt2 dist_nonneg
    _ ≤ 2 * (eps / 4) :=
      mul_le_mul_of_nonneg_left hcoordEps (by norm_num)
    _ < eps := by linarith

end HCGCompactness
end DifferentialGeometry
