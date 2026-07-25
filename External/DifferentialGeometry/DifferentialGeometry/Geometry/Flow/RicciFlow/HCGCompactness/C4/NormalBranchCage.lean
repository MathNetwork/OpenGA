import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchHessian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCCmDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSmoothness

set_option autoImplicit false








noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem aliveSlots_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : Fin (pb.A r),
      (seqCenter hd D P (L.φ k) (gamma : Nat)).isSome =
        L.alive (gamma : Nat) :=
  Filter.eventually_all.mpr fun gamma => L.alive_eventually (gamma : Nat)


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hat_mem_live
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {k : Nat} {gamma : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hstable : (seqCenter hd D P (L.φ k) (gamma : Nat)).isSome =
      L.alive (gamma : Nat))
    (hx : x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k gamma) :
    L.alive (gamma : Nat) = true := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [NetLimitData.hatBall, hc] at hx
  | some c => simpa [hc] using hstable.symm



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hat_dist_centerD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {k : Nat} {gamma : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hx : x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k gamma) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    dist x (seqCenterD hd P L k (gamma : Nat)) <
      4 * L.lamInf (gamma : Nat) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [NetLimitData.hatBall, hc] at hx
  | some c => simpa [NetLimitData.hatBall, seqCenterD, hc] using hx



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqCenterD_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (gamma : Nat) (hgamma : L.alive gamma = true) :
    ∀ᶠ k in Filter.atTop,
      hd.dist (L.φ k) (seqCenterD hd P L k gamma)
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (gamma : Real) := by
  filter_upwards [seqCenterD_live hd P L gamma hgamma] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  rw [← ProperMetricOn.dist_eq hd hre P (L.φ k)]
  have hr : seqRadius hd D P (L.φ k) gamma =
      dist (seqCenterD hd P L k gamma) (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ gamma hk
  rw [← hr]
  exact (seqRadius_mem hd hD P (L.φ k) gamma).2



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqCenterD_rInf_lt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P) (gamma : Nat) :
    ∀ᶠ k in Filter.atTop,
      hd.dist (L.φ k) (seqCenterD hd P L k gamma)
          (X.obj (L.φ k)).basepoint < L.rInf gamma + 1 := by
  have hrad : ∀ᶠ k in Filter.atTop,
      seqRadius hd D P (L.φ k) gamma < L.rInf gamma + 1 :=
    (L.tendsto gamma).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hrad] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  rw [← ProperMetricOn.dist_eq hd hre P (L.φ k),
    ← seqCenterD_dist_eq hd P L k gamma]
  exact hk



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem liveCenters_rInf
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      hd.dist (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint < L.rInf (gamma.1 : Nat) + 1 :=
  Filter.eventually_all.mpr fun gamma =>
    seqCenterD_rInf_lt hd P hre L (gamma.1 : Nat)



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem lamInf_lt_halfMin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real} (hD : 0 < D)
    (hphys : 8 * Real.exp hd.C < aMin * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) :
    4 * L.lamInf gamma <
      (aMin * hd.mu (L.rInf gamma + 1)) / 2 := by
  have hratio : hd.lambda D (L.rInf gamma) ≤
      Real.exp hd.C * hd.lambda D (L.rInf gamma + 1) := by
    simpa only [mul_one] using hd.lambda_exp_le hD
      (s := L.rInf gamma + 1) (t := L.rInf gamma) (d := 1) (by linarith)
  have hhat : (8 * Real.exp hd.C) * hd.lambda D (L.rInf gamma + 1) <
      aMin * hd.mu (L.rInf gamma + 1) :=
    normalBrHat (hd := hd) hD hphys
  calc
    4 * L.lamInf gamma = 4 * hd.lambda D (L.rInf gamma) := rfl
    _ ≤ 4 * (Real.exp hd.C * hd.lambda D (L.rInf gamma + 1)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = ((8 * Real.exp hd.C) * hd.lambda D (L.rInf gamma + 1)) / 2 := by ring
    _ < (aMin * hd.mu (L.rInf gamma + 1)) / 2 :=
      div_lt_div_of_pos_right hhat (by norm_num)



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_cage_rad
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real} (hD : 0 < D)
    (haMin : 0 < aMin)
    (hphys : 8 * Real.exp hd.C < aMin * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat)
    (eps : Real) (heps : 0 < eps) :
    ∃ rad : Real, 0 < rad ∧ rad < eps ∧
      ENNReal.ofReal (4 * L.lamInf gamma + 6 * rad) <
        ENNReal.ofReal ((aMin * hd.mu (L.rInf gamma + 1)) / 2) := by
  let rho := aMin * hd.mu (L.rInf gamma + 1)
  let gap := rho / 2 - 4 * L.lamInf gamma
  have hgap : 0 < gap := by
    dsimp only [gap, rho]
    linarith [lamInf_lt_halfMin hd hD hphys P L gamma]
  let rad := min (gap / 12) (eps / 2)
  have hrad : 0 < rad := by
    dsimp only [rad]
    exact lt_min (div_pos hgap (by norm_num)) (div_pos heps (by norm_num))
  have hradGap : rad ≤ gap / 12 := min_le_left _ _
  have hradEps : rad ≤ eps / 2 := min_le_right _ _
  have hreal : 4 * L.lamInf gamma + 6 * rad < rho / 2 := by
    dsimp only [gap] at hradGap
    nlinarith
  refine ⟨rad, hrad, by linarith, ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff
    (div_pos (mul_pos haMin (hd.mu_pos _)) (by norm_num))).2 (by
      simpa only [rho] using hreal)



def HasLiveBrFull
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (aMin : Real) (q : LiveSlot L pb r → NNReal)
    (δ : LiveSlot L pb r → Real) : Prop :=
  ∀ gamma : LiveSlot L pb r,
    HasNormalBrFull (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n)) (hconn (L.φ n))
      (seqCenterD hd P L n (gamma.1 : Nat)) (q gamma) (δ gamma)
      (aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1))




theorem exists_slot_min
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L : NetLimitData hd D P)
        (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
                2 * rho < (q gamma : Real)) ∧
            (∀ gamma : LiveSlot L pb r,
              6 * (q gamma : Real) <
                h.phaseRadius (L.rInf (gamma.1 : Nat) + 1)) ∧
            (∀ gamma : LiveSlot L pb r,
              3 * hb.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
                (2 / 3 : Real) * (q gamma : Real)) ∧
            (∀ gamma : LiveSlot L pb r,
              PhaseFlow.phaseErr (normalPhaseK hb (2 * q gamma)) < T) ∧
            (∀ gamma : LiveSlot L pb r,
              N * (T - PhaseFlow.phaseErr
                    (normalPhaseK hb (2 * q gamma)))⁻¹ *
                  PhaseFlow.phaseErr (normalPhaseK hb (2 * q gamma)) < 1 / 24) ∧
            (∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              let x := seqCenterD hd P L k (gamma.1 : Nat)
              letI : TopologicalSpace (X.obj (L.φ k)).M :=
                (X.obj (L.φ k)).topology
              letI : ChartedSpace H (X.obj (L.φ k)).M :=
                (X.obj (L.φ k)).charted
              letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
                (X.obj (L.φ k)).smooth
              letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
                (X.obj (L.φ k)).t2TangentBundle
              Metric.ball (0 : E) rho ⊆
                normalQuarter (I := I) (X.obj (L.φ k)) x) ∧
            ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              let x := seqCenterD hd P L k (gamma.1 : Nat)
              letI : TopologicalSpace (X.obj (L.φ k)).M :=
                (X.obj (L.φ k)).topology
              letI : ChartedSpace H (X.obj (L.φ k)).M :=
                (X.obj (L.φ k)).charted
              letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
                (X.obj (L.φ k)).smooth
              letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
                (X.obj (L.φ k)).t2TangentBundle
              HasNormalBrFull (I := I) (X.obj (L.φ k))
                  (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x
                  (q gamma) (δ gamma) rho ∧
                rho ≤ hb.radius (L.φ k) x ∧
                rho / 2 ≤ Geometry.Riemannian.expRadiusGp
                  (I := I) (X.obj (L.φ k)).metric x := by
  classical
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  obtain ⟨aq, aδ, aMin, haq, haδ, haMin, hscale⟩ :=
    normalMinScale (I := I) h hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D P L pb r
  have hslot : ∀ gamma : LiveSlot L pb r,
      ∃ (q : NNReal) (δ : Real),
        0 < q ∧ 0 < δ ∧
        (q : Real) = aq * hd.mu (L.rInf (gamma.1 : Nat) + 1) ∧
        aδ * hd.mu (L.rInf (gamma.1 : Nat) + 1) ≤ δ ∧
        6 * (q : Real) < h.phaseRadius (L.rInf (gamma.1 : Nat) + 1) ∧
        3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q : Real) ∧
        PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T ∧
        N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
            PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 ∧
        2 * (aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) < (q : Real) ∧
        ∀ k (x : (X.obj k).M),
          hd.dist k x (X.obj k).basepoint ≤ L.rInf (gamma.1 : Nat) + 1 →
          letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
          letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
          letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
          letI : T2Space (TangentBundle I (X.obj k).M) :=
            (X.obj k).t2TangentBundle
          HasNormalBrFull (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x q δ (aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) ∧
            aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1) ≤ hb.radius k x ∧
            (aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2 ≤
              Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
    intro gamma
    apply hscale
    nlinarith [(L.rInf_mem (gamma.1 : Nat)).1]
  choose q δ hdata using hslot
  refine ⟨q, δ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro gamma
    rcases hdata gamma with
      ⟨hq, hδ, _hqeq, _hδlower, _hqWide, _hqAcc, _herr, _hinvErr, hqMin,
        _hcentres⟩
    dsimp only
    exact ⟨hq, hδ, mul_pos haMin (hd.mu_pos _), hqMin⟩
  · intro gamma
    rcases hdata gamma with
      ⟨_hq, _hδ, _hqeq, _hδlower, hqWide, _hqAcc, _herr, _hinvErr, _hqMin,
        _hcentres⟩
    exact hqWide
  · intro gamma
    rcases hdata gamma with
      ⟨_hq, _hδ, _hqeq, _hδlower, _hqWide, hqAcc, _herr, _hinvErr, _hqMin,
        _hcentres⟩
    exact hqAcc
  · intro gamma
    rcases hdata gamma with
      ⟨_hq, _hδ, _hqeq, _hδlower, _hqWide, _hqAcc, herr, _hinvErr, _hqMin,
        _hcentres⟩
    exact herr
  · intro gamma
    rcases hdata gamma with
      ⟨_hq, _hδ, _hqeq, _hδlower, _hqWide, _hqAcc, _herr, hinvErr, _hqMin,
        _hcentres⟩
    exact hinvErr
  · filter_upwards [liveCenters_rInf hd P hre L pb r] with k hk
    intro gamma
    rcases hdata gamma with
      ⟨_hq, _hδ, _hqeq, _hδlower, hqWide, _hqAcc, _herr, _hinvErr, hqMin,
        _hcentres⟩
    letI : TopologicalSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    dsimp only
    have hρphase : aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1) <
        h.phaseRadius (L.rInf (gamma.1 : Nat) + 1) := by
      nlinarith
    apply (Metric.ball_subset_ball hρphase.le).trans
    change Metric.ball (0 : E)
        (h.phaseRadius (L.rInf (gamma.1 : Nat) + 1)) ⊆
      Metric.ball (0 : E)
        (Geometry.Riemannian.expMapC2Radius (I := I)
          (X.obj (L.φ k)).metric
          (seqCenterD hd P L k (gamma.1 : Nat)) / 4)
    exact h.phaseRadius_exp (hk gamma).le
  · filter_upwards [liveCenters_rInf hd P hre L pb r] with k hk
    intro gamma
    rcases hdata gamma with
      ⟨_hq, _hδ, _hqeq, _hδlower, _hqWide, _hqAcc, _herr, _hinvErr, _hqMin,
        hcentres⟩
    letI : TopologicalSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    exact hcentres (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat)) (hk gamma).le



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_rad_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real} (hD : 0 < D)
    (haMin : 0 < aMin) (hphys : 8 * Real.exp hd.C < aMin * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (s : Set (X.obj (L.φ n)).M)
    (radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real)
    (htail : ∀ epsilon > 0, ∃ N : Nat,
      ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s, radSeq a b x < epsilon) :
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s,
      ∀ gamma : LiveSlot L pb r,
        ENNReal.ofReal
            (4 * L.lamInf (gamma.1 : Nat) + 2 * radSeq a b x) <
          ENNReal.ofReal
            ((aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2) := by
  classical
  let epsilon : LiveSlot L pb r → Real := fun gamma =>
    ((aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2 -
      4 * L.lamInf (gamma.1 : Nat)) / 2
  have hepsilon : ∀ gamma : LiveSlot L pb r, 0 < epsilon gamma := by
    intro gamma
    dsimp only [epsilon]
    nlinarith [lamInf_lt_halfMin hd hD hphys P L (gamma.1 : Nat)]
  choose N hN using fun gamma : LiveSlot L pb r =>
    htail (epsilon gamma) (hepsilon gamma)
  let Nmax : Nat := Finset.univ.sup N
  refine ⟨Nmax, ?_⟩
  intro a ha b hb x hx gamma
  have hgamma : N gamma ≤ Nmax :=
    Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ gamma)
  have hrad := hN gamma a (hgamma.trans ha) b (hgamma.trans hb) x hx
  have hreal : 4 * L.lamInf (gamma.1 : Nat) + 2 * radSeq a b x <
      (aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2 := by
    dsimp only [epsilon] at hrad
    linarith
  exact (ENNReal.ofReal_lt_ofReal_iff
    (div_pos (mul_pos haMin (hd.mu_pos _)) (by norm_num))).2 hreal



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem liveCenters_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      hd.dist (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (gamma.1 : Real) :=
  Filter.eventually_all.mpr fun gamma =>
    seqCenterD_dist_le hd hD P hre L (gamma.1 : Nat) gamma.2



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem liveCenters_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      hd.dist (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (pb.A r : Real) := by
  filter_upwards [liveCenters_dist_le hd hD P hre L pb r] with k hk
  intro gamma
  refine (hk gamma).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast Nat.le_of_lt gamma.1.isLt
  · exact (mul_pos (by norm_num) (hd.lambda_pos hD 0)).le



theorem exists_live_dom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aρ : Real, 0 < aρ ∧ ∃ (q : NNReal) (δ : Real),
      ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
        HasNormalBranchDom (I := I) (X.obj (L.φ k))
          (hcomplete.complete (L.φ k)) (hconn (L.φ k))
          (seqCenterD hd P L k (gamma.1 : Nat)) q δ
          (aρ * hd.mu (2 * hd.lambda D 0 * (pb.A r : Real))) := by
  obtain ⟨aq, aδ, aρ, haq, haδ, haρ, hscale⟩ :=
    normalBrScale (I := I) h hcomplete hconn
  have hR : 0 ≤ 2 * hd.lambda D 0 * (pb.A r : Real) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (hd.lambda_pos hD 0).le) (by positivity)
  obtain ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, hdom⟩ :=
    hscale (2 * hd.lambda D 0 * (pb.A r : Real)) hR
  refine ⟨aρ, haρ, q, δ, ?_⟩
  filter_upwards [liveCenters_cage hd hD P hre L pb r] with k hk
  exact fun gamma => hdom (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat)) (hk gamma)




theorem exists_live_min
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aMin : Real, 0 < aMin ∧ ∃ (q : NNReal) (δ : Real),
      let Rlive := 2 * hd.lambda D 0 * (pb.A r : Real)
      let ρ := aMin * hd.mu Rlive
      0 < q ∧ 0 < δ ∧ 0 < ρ ∧ 2 * ρ < (q : Real) ∧
      ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
        letI : TopologicalSpace (X.obj (L.φ k)).M :=
          (X.obj (L.φ k)).topology
        letI : ChartedSpace H (X.obj (L.φ k)).M :=
          (X.obj (L.φ k)).charted
        letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
          (X.obj (L.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
          (X.obj (L.φ k)).t2TangentBundle
        let x := seqCenterD hd P L k (gamma.1 : Nat)
        HasNormalBrFull (I := I) (X.obj (L.φ k))
            (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x q δ ρ ∧
          ρ ≤ hb.radius (L.φ k) x ∧
          ρ / 2 ≤ Geometry.Riemannian.expRadiusGp
            (I := I) (X.obj (L.φ k)).metric x := by
  obtain ⟨aq, aδ, aMin, haq, haδ, haMin, hscale⟩ :=
    normalMinScale (I := I) h hcomplete hconn
  let Rlive : Real := 2 * hd.lambda D 0 * (pb.A r : Real)
  have hRlive : 0 ≤ Rlive := by
    dsimp only [Rlive]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (hd.lambda_pos hD 0).le) (by positivity)
  obtain ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, _hqAcc, _herr, _hinvErr,
      hqMin, hcentres⟩ := hscale Rlive hRlive
  let ρ : Real := aMin * hd.mu Rlive
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact mul_pos haMin (hd.mu_pos Rlive)
  have h2ρ : 2 * ρ < (q : Real) := by
    simpa only [ρ] using hqMin
  refine ⟨aMin, haMin, q, δ, ?_⟩
  dsimp only
  refine ⟨hq, hδ, hρ, h2ρ, ?_⟩
  filter_upwards [liveCenters_cage hd hD P hre L pb r] with k hk
  intro gamma
  letI : TopologicalSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).smooth
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  simpa only [Rlive, ρ] using
    hcentres (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat)) (hk gamma)



theorem HasNormalBrFull.exists_cm_eqn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hfull : HasNormalBrFull (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type} [Fintype ι] (mu : ι → Real) (pts : ι → (X.obj k).M)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r R : Real) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    ∀ h : CenterInput (I := I) (X.obj k).metric mu pts join p r,
      dist p x ≤ R →
      ENNReal.ofReal (R + 2 * r) < ENNReal.ofReal (ρ / 2) →
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ hb.radius k x →
      ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
      ∃ (hq : 0 < q) (e : OpenPartialHomeomorph (E × E) (E × E))
          (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e),
        NormalDiagFence (I := I) (X.obj k) x q e ∧
          let B := IsNormalDiag.toBranch
            (I := I) (X.obj k) hcomplete hconn x hq he
          let c := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
          let xi : ι → E := fun i =>
            NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (pts i)
          chartCmEqnB (I := I) (X.obj k).metric
            (normal_enorm (I := I) (X.obj k)) x B
            (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c)
            (mu, xi) = 0 := by
  classical
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  letI : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  letI : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro h hpq hscale hρ hρq hρmetric hρexp
  have hpairs₀ := centerPairs_lt_le (I := I) (X.obj k).metric
    mu pts join p r h x R hpq hscale
  let c := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
  have hpairs : ∀ i,
      max (riemannianEDist I x c) (riemannianEDist I x (pts i)) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [c, riemannianEDist_comm] using hpairs₀
  have hsrc (i : ι) :
      pts i ∈ (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).source := by
    have hiLt := (le_max_right (riemannianEDist I x c)
      (riemannianEDist I x (pts i))).trans_lt (hpairs i)
    have hiFin : riemannianEDist I x (pts i) ≠ ⊤ :=
      ne_of_lt (hiLt.trans ENNReal.ofReal_lt_top)
    have hiReal : (riemannianEDist I x (pts i)).toReal < ρ / 2 :=
      (ENNReal.lt_ofReal_iff_toReal_lt hiFin).mp hiLt
    exact (hb.chart_mem_norm_le k x (pts i)
      ⟨hiFin, hiReal.trans_le hρexp⟩).1
  let xi : ι → E := fun i =>
    NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (pts i)
  have hdecode :
      (fun i => (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).symm (xi i)) = pts := by
    funext i
    exact (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).left_inv (hsrc i)
  have h' : CenterInput (I := I) (X.obj k).metric mu
      (fun i => (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).symm (xi i)) join p r := by
    rw [hdecode]
    exact h
  dsimp only [HasNormalBrFull] at hfull
  rcases hfull with ⟨hq, e, he, hf, _hclosed, _hδdom, _htransport⟩
  refine ⟨hq, e, he, hf, ?_⟩
  have hpairs' := centerPairs_lt_le (I := I) (X.obj k).metric mu
    (fun i => (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).symm (xi i))
    join p r h' x R hpq hscale
  have hpairs'' : ∀ i,
      max (riemannianEDist I x
          (centerOfMass (I := I) (X.obj k).metric mu
            (fun j => (NormalCoordinates.normalChartAt
              (I := I) (X.obj k).metric x).symm (xi j)) join p r h'))
        (riemannianEDist I x
          ((NormalCoordinates.normalChartAt
            (I := I) (X.obj k).metric x).symm (xi i))) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [riemannianEDist_comm] using hpairs'
  have hz := centerReadoutB_min (I := I) hb k hcomplete hconn x hq he hf
    mu xi join p r h' hρ hρq hρmetric hρexp hpairs''
  simpa only [xi, hdecode] using hz




theorem HasNormalBrFull.exists_cm_deriv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hfull : HasNormalBrFull (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type} [Fintype ι] (mu : ι → Real) (pts : ι → (X.obj k).M)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r R : Real) (hsum : ∑ i, mu i = 1) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    ∀ h : CenterInput (I := I) (X.obj k).metric mu pts join p r,
      dist p x ≤ R →
      ENNReal.ofReal (R + 2 * r) < ENNReal.ofReal (ρ / 2) →
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ hb.radius k x →
      ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
      ∃ (hq : 0 < q) (e : OpenPartialHomeomorph (E × E) (E × E))
          (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e),
        NormalDiagFence (I := I) (X.obj k) x q e ∧
          let B := IsNormalDiag.toBranch
            (I := I) (X.obj k) hcomplete hconn x hq he
          let c := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
          let z := NormalCoordinates.normalChartAt
            (I := I) (X.obj k).metric x c
          let xi : ι → E := fun i =>
            NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (pts i)
          c ∈ (NormalCoordinates.normalChartAt
              (I := I) (X.obj k).metric x).source ∧
            (∀ i, (z, xi i) ∈ e.target) ∧
              z ∈ normalBall (I := I) (X.obj k) x ∧
              chartCmEqnB (I := I) (X.obj k).metric
                  (normal_enorm (I := I) (X.obj k)) x B z (mu, xi) = 0 ∧
                ∃ L : E ≃L[Real] E,
                  HasFDerivAt
                    (fun u : E => chartCmEqnB (I := I) (X.obj k).metric
                      (normal_enorm (I := I) (X.obj k)) x B u (mu, xi))
                    (L : E →L[Real] E) z ∧
                    ∃ (f : ((ι → Real) × (ι → E)) → E)
                        (Df : ((ι → Real) × (ι → E)) →L[Real] E),
                      f (mu, xi) = z ∧ HasStrictFDerivAt f Df (mu, xi) ∧
                        (∀ᶠ params in nhds (mu, xi),
                          chartCmEqnB (I := I) (X.obj k).metric
                            (normal_enorm (I := I) (X.obj k)) x B
                            (f params) params = 0) ∧
                        (∀ᶠ zp in nhds (z, (mu, xi)),
                          chartCmEqnB (I := I) (X.obj k).metric
                              (normal_enorm (I := I) (X.obj k)) x B
                              zp.1 zp.2 = 0 →
                            zp.1 = f zp.2) := by
  classical
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  letI : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  letI : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro h hpq hscale hρ hρq hρmetric hρexp
  have hpairs₀ := centerPairs_lt_le (I := I) (X.obj k).metric
    mu pts join p r h x R hpq hscale
  let c := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
  have hpairs : ∀ i,
      max (riemannianEDist I x c) (riemannianEDist I x (pts i)) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [c, riemannianEDist_comm] using hpairs₀
  have hsrc (i : ι) :
      pts i ∈ (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).source := by
    have hiLt := (le_max_right (riemannianEDist I x c)
      (riemannianEDist I x (pts i))).trans_lt (hpairs i)
    have hiFin : riemannianEDist I x (pts i) ≠ ⊤ :=
      ne_of_lt (hiLt.trans ENNReal.ofReal_lt_top)
    have hiReal : (riemannianEDist I x (pts i)).toReal < ρ / 2 :=
      (ENNReal.lt_ofReal_iff_toReal_lt hiFin).mp hiLt
    exact (hb.chart_mem_norm_le k x (pts i)
      ⟨hiFin, hiReal.trans_le hρexp⟩).1
  let xi : ι → E := fun i =>
    NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (pts i)
  have hdecode :
      (fun i => (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).symm (xi i)) = pts := by
    funext i
    exact (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).left_inv (hsrc i)
  have h' : CenterInput (I := I) (X.obj k).metric mu
      (fun i => (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).symm (xi i)) join p r := by
    rw [hdecode]
    exact h
  dsimp only [HasNormalBrFull] at hfull
  rcases hfull with
    ⟨hq, e, he, hf, _hclosed, _hδdom, _hhom, _hpair, _hinv,
      _hδinv, eta, heta, happrox⟩
  refine ⟨hq, e, he, hf, ?_⟩
  have hpairs' := centerPairs_lt_le (I := I) (X.obj k).metric mu
    (fun i => (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).symm (xi i))
    join p r h' x R hpq hscale
  have hpairs'' : ∀ i,
      max (riemannianEDist I x
          (centerOfMass (I := I) (X.obj k).metric mu
            (fun j => (NormalCoordinates.normalChartAt
              (I := I) (X.obj k).metric x).symm (xi j)) join p r h'))
        (riemannianEDist I x
          ((NormalCoordinates.normalChartAt
            (I := I) (X.obj k).metric x).symm (xi i))) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [riemannianEDist_comm] using hpairs'
  have hzero' := centerReadoutB_min (I := I) hb k hcomplete hconn x hq he hf
    mu xi join p r h' hρ hρq hρmetric hρexp hpairs''
  have hzero : chartCmEqnB (I := I) (X.obj k).metric
      (normal_enorm (I := I) (X.obj k)) x
      (IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he)
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c)
      (mu, xi) = 0 := by
    simpa only [c, xi, hdecode] using hzero'
  obtain ⟨i0, _hi0⟩ := h.μ_pos
  have hcLt : riemannianEDist I x c < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i0)
  have hcFin : riemannianEDist I x c ≠ ⊤ :=
    ne_of_lt (hcLt.trans ENNReal.ofReal_lt_top)
  have hcReal : (riemannianEDist I x c).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hcFin).mp hcLt
  have hcSource : c ∈ (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).source :=
    (hb.chart_mem_norm_le k x c ⟨hcFin, hcReal.trans_le hρexp⟩).1
  have htgt (i : ι) :
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c,
        xi i) ∈ e.target := by
    have hdom := (IsNormalDiag.inv_is_min (I := I) hb k hcomplete hconn x
      hq he hf hρ hρq hρmetric hρexp (hpairs i)).choose_spec.1
    simpa only [xi] using
      IsNormalDiag.target_of_chart_dom (I := I) (X.obj k) hcomplete hconn x
        hq he hf hcSource (hsrc i) hdom
  have hzNormal :
      NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c ∈
        normalBall (I := I) (X.obj k) x := by
    have hpre : e.symm
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c,
          xi i0) ∈ Metric.ball (0 : E × E) q := by
      rw [← he.1]
      exact e.map_target (htgt i0)
    have hout := (hf (e.symm
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c,
        xi i0)) (Metric.ball_subset_closedBall hpre)).2.1
    simpa only [e.right_inv (htgt i0)] using hout
  have heta_one : eta < 1 := heta.trans (by norm_num)
  have hsol := IsNormalDiag.cm_sol_strict (I := I) (X.obj k) hcomplete hconn x
    hq he hf happrox heta_one
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x c)
    mu xi htgt h.μ_nonneg hsum hzero
  simpa only [c, xi] using ⟨hcSource, htgt, hzNormal, hzero, hsol⟩



theorem exists_hat_cm_eqn_at
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat)
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (hqdata : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hbranch : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      let x0 := seqCenterD hd P L k (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      HasNormalBrFull (I := I) (X.obj (L.φ k))
          (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0
          (q gamma) (δ gamma) rho ∧
        rho ≤ hb.radius (L.φ k) x0 ∧
        rho / 2 ≤ expRadiusGp (I := I) (X.obj (L.φ k)).metric x0)
    (alpha : LiveSlot L pb r)
    :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
      (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ k)).M
    letI : T3Space (X.obj (L.φ k)).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle (I := I)
    letI : (z : (X.obj (L.φ k)).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj (L.φ k)).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).emetricSpace (I := I)
    letI : CompleteSpace (X.obj (L.φ k)).M :=
      MetricComplete.complete (I := I) (X.obj (L.φ k))
        (hcomplete.complete (L.φ k))
    letI : MetricSpace (X.obj (L.φ k)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
    ∀ (mu : Fin (pb.A r) → Real)
        (pts : Fin (pb.A r) → (X.obj (L.φ k)).M)
        (join : (X.obj (L.φ k)).M → (X.obj (L.φ k)).M → Real →
          (X.obj (L.φ k)).M)
        (x : (X.obj (L.φ k)).M) (rad : Real),
      ∀ h : CenterInput (I := I) (X.obj (L.φ k)).metric mu pts join x rad,
        x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k alpha.1 →
        ENNReal.ofReal
            (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
          ENNReal.ofReal
            ((aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)) / 2) →
          ∃ (hq : 0 < q alpha)
              (e : OpenPartialHomeomorph (E × E) (E × E))
              (he : IsNormalDiag (I := I) (X.obj (L.φ k))
                (hcomplete.complete (L.φ k)) (hconn (L.φ k))
                (seqCenterD hd P L k (alpha.1 : Nat))
                (q alpha) (δ alpha) e),
            NormalDiagFence (I := I) (X.obj (L.φ k))
                (seqCenterD hd P L k (alpha.1 : Nat)) (q alpha) e ∧
              let x0 := seqCenterD hd P L k (alpha.1 : Nat)
              let B := IsNormalDiag.toBranch (I := I) (X.obj (L.φ k))
                (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0 hq he
              let c := centerOfMass (I := I) (X.obj (L.φ k)).metric
                mu pts join x rad h
              let xi : Fin (pb.A r) → E := fun i =>
                NormalCoordinates.normalChartAt
                  (I := I) (X.obj (L.φ k)).metric x0 (pts i)
              chartCmEqnB (I := I) (X.obj (L.φ k)).metric
                (normal_enorm (I := I) (X.obj (L.φ k))) x0 B
                (NormalCoordinates.normalChartAt
                  (I := I) (X.obj (L.φ k)).metric x0 c)
                (mu, xi) = 0 := by
  classical
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ k)).M
  letI : T3Space (X.obj (L.φ k)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ k)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ k)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ k)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ k))
      (hcomplete.complete (L.φ k))
  letI : MetricSpace (X.obj (L.φ k)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
  intro mu pts join x rad h hxhat hradCage
  let x0 := seqCenterD hd P L k (alpha.1 : Nat)
  let rho0 := aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)
  rcases hqdata alpha with ⟨hq, _hδ, hρ, hρq⟩
  rcases hbranch alpha with ⟨hfull, hρmetric, hρexp⟩
  have hproper :
      (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
       dist x x0) < 4 * L.lamInf (alpha.1 : Nat) := by
    simpa only [x0] using hat_dist_centerD hd P L pb r hxhat
  have hhd : hd.dist (L.φ k) x x0 < 4 * L.lamInf (alpha.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ k) x x0]
    exact hproper
  have hed : riemannianEDist I x x0 =
      ENNReal.ofReal (hd.dist (L.φ k) x x0) := by
    have hrealize := hre.edist_eq (L.φ k) x x0
    simpa [PointedRiemannianManifold.emetricSpace] using hrealize
  have hpq : dist x x0 ≤ 4 * L.lamInf (alpha.1 : Nat) := by
    rw [HopfRinow.riemMetric_dist_eq, hed,
      ENNReal.toReal_ofReal (hre.dist_nonneg (L.φ k) x x0)]
    exact hhd.le
  have hresult := HasNormalBrFull.exists_cm_eqn (I := I) hb (L.φ k)
    (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0 hfull
    mu pts join x rad (4 * L.lamInf (alpha.1 : Nat)) h hpq
    hradCage hρ hρq hρmetric hρexp
  simpa only [x0, rho0] using hresult



theorem exists_hat_cm_sol_at
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat)
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (hqdata : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hbranch : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      let x0 := seqCenterD hd P L k (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      HasNormalBrFull (I := I) (X.obj (L.φ k))
          (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0
          (q gamma) (δ gamma) rho ∧
        rho ≤ hb.radius (L.φ k) x0 ∧
        rho / 2 ≤ expRadiusGp (I := I) (X.obj (L.φ k)).metric x0)
    (alpha : LiveSlot L pb r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
      (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ k)).M
    letI : T3Space (X.obj (L.φ k)).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle (I := I)
    letI : (z : (X.obj (L.φ k)).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj (L.φ k)).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).emetricSpace (I := I)
    letI : CompleteSpace (X.obj (L.φ k)).M :=
      MetricComplete.complete (I := I) (X.obj (L.φ k))
        (hcomplete.complete (L.φ k))
    letI : MetricSpace (X.obj (L.φ k)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
    ∀ (mu : Fin (pb.A r) → Real)
        (pts : Fin (pb.A r) → (X.obj (L.φ k)).M)
        (join : (X.obj (L.φ k)).M → (X.obj (L.φ k)).M → Real →
          (X.obj (L.φ k)).M)
        (x : (X.obj (L.φ k)).M) (rad : Real),
      ∀ h : CenterInput (I := I) (X.obj (L.φ k)).metric mu pts join x rad,
        ∑ i, mu i = 1 →
        x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k alpha.1 →
        ENNReal.ofReal
            (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
          ENNReal.ofReal
            ((aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)) / 2) →
          ∃ (hq : 0 < q alpha)
              (e : OpenPartialHomeomorph (E × E) (E × E))
              (he : IsNormalDiag (I := I) (X.obj (L.φ k))
                (hcomplete.complete (L.φ k)) (hconn (L.φ k))
                (seqCenterD hd P L k (alpha.1 : Nat))
                (q alpha) (δ alpha) e),
            NormalDiagFence (I := I) (X.obj (L.φ k))
                (seqCenterD hd P L k (alpha.1 : Nat)) (q alpha) e ∧
              let x0 := seqCenterD hd P L k (alpha.1 : Nat)
              let B := IsNormalDiag.toBranch (I := I) (X.obj (L.φ k))
                (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0 hq he
              let c := centerOfMass (I := I) (X.obj (L.φ k)).metric
                mu pts join x rad h
              let z := NormalCoordinates.normalChartAt
                (I := I) (X.obj (L.φ k)).metric x0 c
              let xi : Fin (pb.A r) → E := fun i =>
                NormalCoordinates.normalChartAt
                  (I := I) (X.obj (L.φ k)).metric x0 (pts i)
              c ∈ (NormalCoordinates.normalChartAt
                  (I := I) (X.obj (L.φ k)).metric x0).source ∧
                (∀ i, (z, xi i) ∈ e.target) ∧
                  z ∈ normalBall (I := I) (X.obj (L.φ k)) x0 ∧
                  chartCmEqnB (I := I) (X.obj (L.φ k)).metric
                      (normal_enorm (I := I) (X.obj (L.φ k))) x0 B
                      z (mu, xi) = 0 ∧
                    ∃ Lcm : E ≃L[Real] E,
                      HasFDerivAt
                          (fun u : E => chartCmEqnB (I := I)
                            (X.obj (L.φ k)).metric
                            (normal_enorm (I := I) (X.obj (L.φ k))) x0 B
                            u (mu, xi))
                          (Lcm : E →L[Real] E) z ∧
                        ∃ (f : ((Fin (pb.A r) → Real) ×
                              (Fin (pb.A r) → E)) → E)
                            (Df : ((Fin (pb.A r) → Real) ×
                              (Fin (pb.A r) → E)) →L[Real] E),
                          f (mu, xi) = z ∧ HasStrictFDerivAt f Df (mu, xi) ∧
                            (∀ᶠ params in nhds (mu, xi),
                              chartCmEqnB (I := I) (X.obj (L.φ k)).metric
                                (normal_enorm (I := I) (X.obj (L.φ k))) x0 B
                                (f params) params = 0) ∧
                            (∀ᶠ zp in nhds (z, (mu, xi)),
                              chartCmEqnB (I := I) (X.obj (L.φ k)).metric
                                  (normal_enorm (I := I) (X.obj (L.φ k))) x0 B
                                  zp.1 zp.2 = 0 →
                                zp.1 = f zp.2) := by
  classical
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ k)).M
  letI : T3Space (X.obj (L.φ k)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ k)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ k)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ k)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ k))
      (hcomplete.complete (L.φ k))
  letI : MetricSpace (X.obj (L.φ k)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
  intro mu pts join x rad h hsum hxhat hradCage
  let x0 := seqCenterD hd P L k (alpha.1 : Nat)
  let rho0 := aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)
  rcases hqdata alpha with ⟨hq, _hδ, hρ, hρq⟩
  rcases hbranch alpha with ⟨hfull, hρmetric, hρexp⟩
  have hproper :
      (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
       dist x x0) < 4 * L.lamInf (alpha.1 : Nat) := by
    simpa only [x0] using hat_dist_centerD hd P L pb r hxhat
  have hhd : hd.dist (L.φ k) x x0 < 4 * L.lamInf (alpha.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ k) x x0]
    exact hproper
  have hed : riemannianEDist I x x0 =
      ENNReal.ofReal (hd.dist (L.φ k) x x0) := by
    have hrealize := hre.edist_eq (L.φ k) x x0
    simpa [PointedRiemannianManifold.emetricSpace] using hrealize
  have hpq : dist x x0 ≤ 4 * L.lamInf (alpha.1 : Nat) := by
    rw [HopfRinow.riemMetric_dist_eq, hed,
      ENNReal.toReal_ofReal (hre.dist_nonneg (L.φ k) x x0)]
    exact hhd.le
  have hresult := HasNormalBrFull.exists_cm_deriv (I := I) hb (L.φ k)
    (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0 hfull
    mu pts join x rad (4 * L.lamInf (alpha.1 : Nat)) hsum h hpq
    hradCage hρ hρq hρmetric hρexp
  simpa only [x0, rho0] using hresult



theorem exists_hat_cm_eqn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat)
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (hstable : ∀ gamma : Fin (pb.A r),
      (seqCenter hd D P (L.φ k) (gamma : Nat)).isSome =
        L.alive (gamma : Nat))
    (hqdata : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hbranch : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      let x0 := seqCenterD hd P L k (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      HasNormalBrFull (I := I) (X.obj (L.φ k))
          (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0
          (q gamma) (δ gamma) rho ∧
        rho ≤ hb.radius (L.φ k) x0 ∧
        rho / 2 ≤ expRadiusGp (I := I) (X.obj (L.φ k)).metric x0)
    :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
      (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ k)).M
    letI : T3Space (X.obj (L.φ k)).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle (I := I)
    letI : (z : (X.obj (L.φ k)).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj (L.φ k)).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).emetricSpace (I := I)
    letI : CompleteSpace (X.obj (L.φ k)).M :=
      MetricComplete.complete (I := I) (X.obj (L.φ k))
        (hcomplete.complete (L.φ k))
    letI : MetricSpace (X.obj (L.φ k)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
    ∀ (mu : Fin (pb.A r) → Real)
        (pts : Fin (pb.A r) → (X.obj (L.φ k)).M)
        (join : (X.obj (L.φ k)).M → (X.obj (L.φ k)).M → Real →
          (X.obj (L.φ k)).M)
        (x : (X.obj (L.φ k)).M) (rad : Real),
      ∀ h : CenterInput (I := I) (X.obj (L.φ k)).metric mu pts join x rad,
        (∀ gamma, mu gamma ≠ 0 →
          x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k gamma) →
        (∀ gamma : LiveSlot L pb r,
          ENNReal.ofReal
              (4 * L.lamInf (gamma.1 : Nat) + 2 * rad) <
            ENNReal.ofReal
              ((aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2)) →
        ∃ gamma : LiveSlot L pb r,
          ∃ (hq : 0 < q gamma)
              (e : OpenPartialHomeomorph (E × E) (E × E))
              (he : IsNormalDiag (I := I) (X.obj (L.φ k))
                (hcomplete.complete (L.φ k)) (hconn (L.φ k))
                (seqCenterD hd P L k (gamma.1 : Nat))
                (q gamma) (δ gamma) e),
            NormalDiagFence (I := I) (X.obj (L.φ k))
                (seqCenterD hd P L k (gamma.1 : Nat)) (q gamma) e ∧
              let x0 := seqCenterD hd P L k (gamma.1 : Nat)
              let B := IsNormalDiag.toBranch (I := I) (X.obj (L.φ k))
                (hcomplete.complete (L.φ k)) (hconn (L.φ k)) x0 hq he
              let c := centerOfMass (I := I) (X.obj (L.φ k)).metric
                mu pts join x rad h
              let xi : Fin (pb.A r) → E := fun i ↦
                NormalCoordinates.normalChartAt
                  (I := I) (X.obj (L.φ k)).metric x0 (pts i)
              chartCmEqnB (I := I) (X.obj (L.φ k)).metric
                (normal_enorm (I := I) (X.obj (L.φ k))) x0 B
                (NormalCoordinates.normalChartAt
                  (I := I) (X.obj (L.φ k)).metric x0 c)
                (mu, xi) = 0 := by
  classical
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ k)).M
  letI : T3Space (X.obj (L.φ k)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ k)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ k)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ k)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ k))
      (hcomplete.complete (L.φ k))
  letI : MetricSpace (X.obj (L.φ k)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
  intro mu pts join x rad h hhat hradCage
  obtain ⟨gamma, hgamma⟩ := h.μ_pos
  have hxhat := hhat gamma (ne_of_gt hgamma)
  have halive : L.alive (gamma : Nat) = true :=
    hat_mem_live hd P L pb r (hstable gamma) hxhat
  let gammaLive : LiveSlot L pb r := ⟨gamma, halive⟩
  refine ⟨gammaLive, ?_⟩
  exact exists_hat_cm_eqn_at (I := I) hd P hre L pb r k hcomplete hconn
    q δ hqdata hbranch gammaLive mu pts join x rad h hxhat (hradCage gammaLive)



theorem exists_cm_branch
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type} [Fintype ι] (μ : ι → Real) (pts : ι → (X.obj k).M)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r R : Real) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ∀ h : CenterInput (I := I) (X.obj k).metric μ pts join p r,
      (letI : MetricSpace (X.obj k).M :=
          HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M);
        dist p x ≤ R) →
      ENNReal.ofReal (R + 2 * r) < ENNReal.ofReal (ρ / 2) →
      0 < ρ →
      ρ / 2 < expRadiusGp (I := I) (X.obj k).metric x →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (centerOfMass (I := I) (ι := ι) (X.obj k).metric μ pts join p r h,
          pts i) ∈ B.readDom := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro h hpq hscale hρ hρExp
  have hpairs : ∀ i,
      max
        (riemannianEDist I
          (centerOfMass (I := I) (ι := ι) (X.obj k).metric μ pts join p r h) x)
        (riemannianEDist I (pts i) x) < ENNReal.ofReal (ρ / 2) :=
    centerPairs_lt_le (I := I) (X.obj k).metric μ pts join p r h x R hpq hscale
  exact HasNormalBranchDom.exists_pair_readout (I := I) hb k hcomplete hconn x hdom
    (fun _ ↦ centerOfMass (I := I) (ι := ι) (X.obj k).metric μ pts join p r h) pts
    hρ hρExp (by simpa [riemannianEDist_comm] using hpairs)

end HCGCompactness
end DifferentialGeometry
