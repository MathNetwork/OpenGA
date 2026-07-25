import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv

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




noncomputable def stageTarget
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (x : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) :
    (X.obj (L.φ l)).M :=
  let Yk := X.obj (L.φ k)
  let Yl := X.obj (L.φ l)
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
  (NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P L l (gamma : Nat))).symm
    (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P L k (gamma : Nat)) x)





@[simp] theorem stageTarget_chart
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (alpha gamma : Fin (inp.pack.A s)) (z : E) :
    let Yk := X.obj (L.φ k)
    let Yl := X.obj (L.φ l)
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
    NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P L l (alpha : Nat))
        (stageTarget inp P L s k l
          ((NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma) =
      normalTransition (I := I) Yl
        (seqCenterD inp.decay P L l (gamma : Nat))
        (seqCenterD inp.decay P L l (alpha : Nat))
        (normalTransition (I := I) Yk
          (seqCenterD inp.decay P L k (alpha : Nat))
          (seqCenterD inp.decay P L k (gamma : Nat)) z) := by
  rfl



theorem stageTarget_local
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (alpha gamma : Fin (inp.pack.A s)) (z : E)
    (hsrc :
      let Yk := X.obj (L.φ k)
      let Yl := X.obj (L.φ l)
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
      stageTarget inp P L s k l
          ((NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma ∈
        (NormalCoordinates.normalChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P L l (alpha : Nat))).source) :
    let Yk := X.obj (L.φ k)
    let Yl := X.obj (L.φ l)
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
    (NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P L l (alpha : Nat))).symm
      (normalTransition (I := I) Yl
        (seqCenterD inp.decay P L l (gamma : Nat))
        (seqCenterD inp.decay P L l (alpha : Nat))
        (normalTransition (I := I) Yk
          (seqCenterD inp.decay P L k (alpha : Nat))
          (seqCenterD inp.decay P L k (gamma : Nat)) z)) =
      stageTarget inp P L s k l
        ((NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : TopologicalSpace (X.obj (L.φ l)).M := (X.obj (L.φ l)).topology
  letI : ChartedSpace H (X.obj (L.φ l)).M := (X.obj (L.φ l)).charted
  letI : IsManifold I ∞ (X.obj (L.φ l)).M := (X.obj (L.φ l)).smooth
  letI : T2Space (X.obj (L.φ l)).M := (X.obj (L.φ l)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ l)).M) :=
    (X.obj (L.φ l)).t2TangentBundle
  dsimp only
  rw [← stageTarget_chart (I := I) inp P L s k l alpha gamma z]
  exact NormalCoordinates.normalChartAt_left_inv (I := I)
    (X.obj (L.φ l)).metric
    (seqCenterD inp.decay P L l (alpha : Nat)) hsrc



@[simp] theorem stageTarget_subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat) :
    stageTarget inp P (L.subseq hψ) s k l =
      stageTarget inp P L s (ψ k) (ψ l) := by
  rfl


def HasUniqueStageCenter
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) (x : (X.obj (L.φ k)).M) : Prop :=
  let Y := X.obj (L.φ l)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : ConnectedSpace Y.M := hconn (L.φ l)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  ∃! y : Y.M, ∀ z : Y.M,
    CenterOfMass.centerEnergy (I := I) Y.metric
        (fun gamma => rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          x gamma)
        (stageTarget inp P L s k l x) y ≤
      CenterOfMass.centerEnergy (I := I) Y.metric
        (fun gamma => rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          x gamma)
        (stageTarget inp P L s k l x) z



theorem uniqueCenter_subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat)
    (x : (X.obj ((L.subseq hψ).φ k)).M) :
    HasUniqueStageCenter inp P (L.subseq hψ) s hs hconn k l x ↔
      HasUniqueStageCenter inp P L s hs hconn (ψ k) (ψ l) x := by
  have hseq :
      seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k =
        seqAtom inp.decay inp.hD P L inp.pack s (ψ k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack s hψ k gamma
  simp only [HasUniqueStageCenter, stageTarget_subseq, hseq,
    NetLimitData.subseq_phi, Function.comp_apply]
  rfl





noncomputable def stageComparisonMap
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M := by
  classical
  exact fun x =>
    if hx : x ∈ L.hatSourceBall inp.decay P s k then
      if huniq : HasUniqueStageCenter inp P L s hs hconn k l x then
        Classical.choose huniq.exists
      else
        (X.obj (L.φ l)).basepoint
    else
      (X.obj (L.φ l)).basepoint



theorem stageCompare_choose
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    (hx : x ∈ L.hatSourceBall inp.decay P s k)
    (huniq : HasUniqueStageCenter inp P L s hs hconn k l x) :
    stageComparisonMap inp P L s hs hconn k l x =
      Classical.choose huniq.exists := by
  simp only [stageComparisonMap, hx, huniq, dite_true]



theorem stageCompare_default
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    (hdefault : x ∉ L.hatSourceBall inp.decay P s k ∨
      ¬ HasUniqueStageCenter inp P L s hs hconn k l x) :
    stageComparisonMap inp P L s hs hconn k l x =
      (X.obj (L.φ l)).basepoint := by
  rcases hdefault with hx | huniq
  · simp only [stageComparisonMap, hx, dite_false]
  · by_cases hx : x ∈ L.hatSourceBall inp.decay P s k
    · simp only [stageComparisonMap, hx, huniq, dite_true, dite_false]
    · simp only [stageComparisonMap, hx, dite_false]



@[simp] theorem stageCompare_subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat) :
    stageComparisonMap inp P (L.subseq hψ) s hs hconn k l =
      stageComparisonMap inp P L s hs hconn (ψ k) (ψ l) := by
  classical
  funext x
  have hcenter := uniqueCenter_subseq (I := I) inp P L s hs hconn hψ k l x
  have hseq :
      seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k =
        seqAtom inp.decay inp.hD P L inp.pack s (ψ k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack s hψ k gamma
  by_cases hx : x ∈ L.hatSourceBall inp.decay P s (ψ k)
  · have hx' : x ∈ (L.subseq hψ).hatSourceBall inp.decay P s k := by
      simpa only [NetLimitData.hatSourceBall_subseq] using hx
    by_cases hu : HasUniqueStageCenter inp P L s hs hconn (ψ k) (ψ l) x
    · have hu' : HasUniqueStageCenter inp P (L.subseq hψ) s hs hconn k l x :=
        hcenter.mpr hu
      rw [stageCompare_choose (I := I) inp P (L.subseq hψ) s hs hconn k l x hx' hu',
        stageCompare_choose (I := I) inp P L s hs hconn (ψ k) (ψ l) x hx hu]
      apply hu.unique
      · simpa only [stageTarget_subseq, hseq, NetLimitData.subseq_phi,
          Function.comp_apply] using Classical.choose_spec hu'.exists
      · exact Classical.choose_spec hu.exists
    · have hu' : ¬ HasUniqueStageCenter inp P (L.subseq hψ) s hs hconn k l x :=
        fun h => hu (hcenter.mp h)
      rw [stageCompare_default (I := I) inp P (L.subseq hψ) s hs hconn k l x
          (Or.inr hu'),
        stageCompare_default (I := I) inp P L s hs hconn (ψ k) (ψ l) x
          (Or.inr hu)]
      simp only [NetLimitData.subseq_phi, Function.comp_apply]
  · have hx' : x ∉ (L.subseq hψ).hatSourceBall inp.decay P s k := by
      simpa only [NetLimitData.hatSourceBall_subseq] using hx
    rw [stageCompare_default (I := I) inp P (L.subseq hψ) s hs hconn k l x
        (Or.inl hx'),
      stageCompare_default (I := I) inp P L s hs hconn (ψ k) (ψ l) x
        (Or.inl hx)]
    simp only [NetLimitData.subseq_phi, Function.comp_apply]




theorem stageCompare_base
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat)
    (hgp : Item3GpScaleAt (I := I) inp.decay inp.D P L inp.pack s k) :
    stageComparisonMap inp P L s hs hconn k l
        (X.obj (L.φ k)).basepoint =
      (X.obj (L.φ l)).basepoint := by
  classical
  let Yk := X.obj (L.φ k)
  let Yl := X.obj (L.φ l)
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
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : ConnectedSpace Yl.M := hconn (L.φ l)
  letI : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  letI : T3Space Yl.M := inferInstance
  letI : MetricSpace Yk.M := (P (L.φ k)).ms
  letI : RiemannianBundle (fun x : Yl.M => TangentSpace I x) :=
    ⟨Yl.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : Yl.M => TangentSpace I x) :=
    ⟨Yl.metric.inner, Yl.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace Yl.M := HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  have hx : (X.obj (L.φ k)).basepoint ∈
      L.hatSourceBall inp.decay P s k := by
    change Yk.basepoint ∈ Metric.closedBall Yk.basepoint s
    simpa only [Metric.mem_closedBall, dist_self] using hs
  by_cases huniq : HasUniqueStageCenter inp P L s hs hconn k l
      (X.obj (L.φ k)).basepoint
  · rw [stageCompare_choose (I := I) inp P L s hs hconn k l
      Yk.basepoint hx huniq]
    let i0 := baseIndex inp.decay inp.realizes inp.pack hs
    let mu := fun gamma : Fin (inp.pack.A s) =>
      rawWeights
        (cutRaw
          (seqAtom inp.decay inp.hD P L inp.pack s k i0)
          (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
        Yk.basepoint gamma
    have hdelta : mu i0 = 1 ∧ ∀ j, j ≠ i0 → mu j = 0 := by
      simpa only [mu, i0] using
        seqWeights_base inp.decay inp.hD P L inp.realizes inp.pack hs k hgp
    have hcenterK :
        seqCenterD inp.decay P L k (i0 : Nat) = Yk.basepoint := by
      simp only [i0, baseIndex_val, seqCenterD, seqCenter_zero,
        Option.getD_some, Yk]
    have hcenterL :
        seqCenterD inp.decay P L l (i0 : Nat) = Yl.basepoint := by
      simp only [i0, baseIndex_val, seqCenterD, seqCenter_zero,
        Option.getD_some, Yl]
    have htarget :
        stageTarget inp P L s k l Yk.basepoint i0 = Yl.basepoint := by
      change
        (NormalCoordinates.normalChartAt (I := I) Yl.metric
            (seqCenterD inp.decay P L l (i0 : Nat))).symm
          (NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (i0 : Nat)) Yk.basepoint) =
          Yl.basepoint
      rw [hcenterK, hcenterL,
        NormalCoordinates.normalChartAt_centre,
        NormalCoordinates.normalChartAt_symm_zero]
    have hzero :
        CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint) Yl.basepoint = 0 := by
      simp only [CenterOfMass.centerEnergy]
      rw [Finset.sum_eq_zero, mul_zero]
      intro i _hi
      rcases eq_or_ne i i0 with rfl | hne
      · rw [htarget, Manifold.riemannianEDist_self]
        simp
      · rw [hdelta.2 i hne, zero_mul]
    have hmin : ∀ z : Yl.M,
        CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint) Yl.basepoint ≤
          CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint) z := by
      intro z
      rw [hzero]
      simp only [CenterOfMass.centerEnergy]
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
      rcases eq_or_ne i i0 with rfl | hne
      · rw [hdelta.1]
        positivity
      · rw [hdelta.2 i hne, zero_mul]
    apply huniq.unique
    · exact Classical.choose_spec huniq.exists
    · exact hmin
  · simp only [stageComparisonMap, hx, huniq, dite_true, dite_false]

end HCGCompactness
end DifferentialGeometry
