import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffPair
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffH0
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




theorem lapDiffA2_cont
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {S : Set Real}
    (hreg : ∀ s ∈ S, (T : Real) - s ∈ D.regular)
    (hsmall : ∀ s ∈ S,
      (Module.finrank Real E : Real) *
          HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
            (G.metric ((T : Real) - s))
            (G.metric (T : Real)) (G.metric (T : Real)) ≤
        (1 / 2 : Real)) :
    ContinuousOn
      (fun s : Real => lapDiffA2 (I := I) (M := M) G T s) S := by
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
        TensorL2 0 0 (G.metric (T : Real))) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  intro s0 hs0
  let q : SmoothRiemannianMetric I M := G.metric (T : Real)
  let K : D.RegularTime := ⟨(T : Real) - s0, hreg s0 hs0⟩
  let k : SmoothRiemannianMetric I M := G.metric (K : Real)
  let rhoK : Real → Real := fun s =>
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (G.metric ((T : Real) - s)) k k
  have hshiftK :
      Tendsto (fun s : Real => (T : Real) - s)
        (nhds s0) (nhds (K : Real)) := by
    dsimp only [K]
    simpa only using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (nhds s0) (nhds s0)))
  have hrhoK : Tendsto rhoK (nhds s0) (nhds 0) := by
    simpa only [rhoK, k] using
      (HCGCompactness.metric_c1_tendsto (I := I) G hG K).comp hshiftK
  obtain ⟨C, hC, hpair⟩ :=
    lapDiff_pair_norm (I := I) (M := M) q k
  change Tendsto
    (fun s : Real => lapDiffA2 (I := I) (M := M) G T s)
    (nhdsWithin s0 S)
    (nhds (lapDiffA2 (I := I) (M := M) G T s0))
  rw [Metric.tendsto_nhds]
  intro eta heta
  have hKsmall :
      ∀ᶠ s in nhds s0,
        (Module.finrank Real E : Real) * rhoK s < (1 / 2 : Real) :=
    (hrhoK.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  have hupperLim :
      Tendsto (fun s => Real.sqrt C * |rhoK s|)
        (nhds s0) (nhds 0) := by
    simpa only [abs_zero, mul_zero] using
      hrhoK.abs.const_mul (Real.sqrt C)
  have hupper :
      ∀ᶠ s in nhds s0, Real.sqrt C * |rhoK s| < eta :=
    hupperLim.eventually_lt_const heta
  filter_upwards [hKsmall.filter_mono inf_le_left,
    hupper.filter_mono inf_le_left, self_mem_nhdsWithin]
      with s hks hu hs
  have hqh := hsmall s hs
  have hqk := hsmall s0 hs0
  have hkh :
      (Module.finrank Real E : Real) *
          HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
            (G.metric ((T : Real) - s)) k k ≤
        (1 / 2 : Real) := by
    simpa only [rhoK] using hks.le
  rw [dist_eq_norm]
  simpa only [lapDiffA2, q, k, K, rhoK] using
    lt_of_le_of_lt
      (hpair (G.metric ((T : Real) - s)) hqh hqk hkh) hu




theorem lapDiffA20_short
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ContinuousOn
        (fun s : Real => lapDiffA20 (I := I) (M := M) G T s)
        (Set.Icc 0 tau) ∧
      AEStronglyMeasurable
        (fun s : Real => lapDiffA20 (I := I) (M := M) G T s)
        (timeMeasure tau) ∧
      (∀ s ∈ Set.Icc 0 tau,
        ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ epsilon) ∧
      ∀ᵐ s ∂timeMeasure tau,
        ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ epsilon := by
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
        tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let q : SmoothRiemannianMetric I M := G.metric (T : Real)
  let rhoQ : Real → Real := fun s =>
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (G.metric ((T : Real) - s)) q q
  have hshift :
      Tendsto (fun s : Real => (T : Real) - s)
        (nhds 0) (nhds (T : Real)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (nhds 0) (nhds 0)))
  have hrhoQ : Tendsto rhoQ (nhds 0) (nhds 0) := by
    simpa only [rhoQ, q] using
      (HCGCompactness.metric_c1_tendsto (I := I) G hG T).comp hshift
  have hreg :
      ∀ᶠ s in nhds (0 : Real), (T : Real) - s ∈ D.regular :=
    hshift.eventually (D.regular_isOpen.mem_nhds T.2)
  have hqsmall :
      ∀ᶠ s in nhds (0 : Real),
        (Module.finrank Real E : Real) * rhoQ s < (1 / 2 : Real) :=
    (hrhoQ.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  have heps :
      ∀ᶠ s in nhds (0 : Real),
        ‖lapDiffA2 (I := I) (M := M) G T s‖ < epsilon :=
    (lapDiffA2_zero (I := I) (M := M) G hG T).eventually_lt_const
      hepsilon
  let U : Set Real := {s |
    (T : Real) - s ∈ D.regular ∧
      (Module.finrank Real E : Real) * rhoQ s ≤ (1 / 2 : Real) ∧
      ‖lapDiffA2 (I := I) (M := M) G T s‖ ≤ epsilon}
  have hU : U ∈ nhds (0 : Real) := by
    change ∀ᶠ s in nhds (0 : Real),
      (T : Real) - s ∈ D.regular ∧
        (Module.finrank Real E : Real) * rhoQ s ≤ (1 / 2 : Real) ∧
        ‖lapDiffA2 (I := I) (M := M) G T s‖ ≤ epsilon
    filter_upwards [hreg, hqsmall, heps] with s hs hr he
    exact ⟨hs, hr.le, he.le⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := min 1 (delta / 2)
  have htaupos : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htauone : tau ≤ 1 := by
    exact min_le_left _ _
  have htaudelta : tau < delta := by
    exact (min_le_right (1 : Real) (delta / 2)).trans_lt
      (half_lt_self hdelta)
  have hIccU : Set.Icc (0 : Real) tau ⊆ U := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htaudelta
  have hgood (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) :
      (T : Real) - s ∈ D.regular ∧
        (Module.finrank Real E : Real) * rhoQ s ≤ (1 / 2 : Real) ∧
        ‖lapDiffA2 (I := I) (M := M) G T s‖ ≤ epsilon := by
    simpa only [U] using hIccU hs
  have hA2cont :
      ContinuousOn
        (fun s : Real => lapDiffA2 (I := I) (M := M) G T s)
        (Set.Icc 0 tau) := by
    apply lapDiffA2_cont (I := I) (M := M) G hG T
    · intro s hs
      exact (hgood s hs).1
    · intro s hs
      simpa only [rhoQ, q] using (hgood s hs).2.1
  have hA20cont :
      ContinuousOn
        (fun s : Real => lapDiffA20 (I := I) (M := M) G T s)
        (Set.Icc 0 tau) :=
    lapDiffA20_cont_of (I := I) (M := M) G T hA2cont
  have hA20meas :
      AEStronglyMeasurable
        (fun s : Real => lapDiffA20 (I := I) (M := M) G T s)
        (timeMeasure tau) := by
    unfold timeMeasure
    exact hA20cont.aestronglyMeasurable measurableSet_Icc
  have hboundOn :
      ∀ s ∈ Set.Icc (0 : Real) tau,
        ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ epsilon := by
    intro s hs
    rw [lapDiffA20_norm]
    exact (hgood s hs).2.2
  have hboundAE :
      ∀ᵐ s ∂timeMeasure tau,
        ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ epsilon := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall hboundOn)
  exact ⟨tau, htaupos, htauone, hA20cont, hA20meas, hboundOn,
    hboundAE⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
