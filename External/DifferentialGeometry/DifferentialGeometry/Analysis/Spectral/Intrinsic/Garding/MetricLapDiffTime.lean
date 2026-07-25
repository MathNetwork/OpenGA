import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBoundsFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricC1Continuity








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



noncomputable def lapDiffA2
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real) :
    tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
      TensorL2 0 0 (G.metric (T : Real)) :=
  lapDiffOp (I := I) (M := M) (G.metric (T : Real))
    (G.metric ((T : Real) - s))

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem lapDiff_rho
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    Tendsto
      (fun s : Real =>
        HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
          (G.metric ((T : Real) - s))
          (G.metric (T : Real)) (G.metric (T : Real)))
      (𝓝 0) (𝓝 0) := by
  have hshift :
      Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  exact (HCGCompactness.metric_c1_tendsto
    (I := I) G hG T).comp hshift

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lapDiff_fibreSmall
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∀ᶠ s in 𝓝 (0 : Real),
      MetricRealization.metricCauchySchwarzBound (I := I) (G.metric (T : Real))
        (fun x : M =>
          (G.metric ((T : Real) - s)).inner x - (G.metric (T : Real)).inner x)
        (1 / 4 : Real) := by
  let q : SmoothRiemannianMetric I M := G.metric (T : Real)
  let rho : Real → Real := fun s =>
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (G.metric ((T : Real) - s)) q q
  have hrho : Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho, q] using lapDiff_rho (I := I) G hG T
  have hsmall : ∀ᶠ s in 𝓝 (0 : Real), rho s < (1 / 4 : Real) :=
    hrho.eventually_lt_const (by norm_num)
  filter_upwards [hsmall] with s hs
  intro x v w
  have hnorm :
      HCGCompactness.metricDerivNorm (I := I) 0
          (G.metric ((T : Real) - s)) q q x ≤ rho s := by
    simpa only [rho] using
      (HCGCompactness.derivNorm_le_sup (I := I) (K := Set.univ)
        isCompact_univ (a := 0) (p := 1) (by omega)
        (G.metric ((T : Real) - s)) q q (Set.mem_univ x))
  have heval := HCGCompactness.metricDiff_abs_le (I := I)
    (G.metric ((T : Real) - s)) q q x v w
  have hfinal :
      |(G.metric ((T : Real) - s)).inner x v w - q.inner x v w| ≤
        (1 / 4 : Real) * Real.sqrt (q.inner x v v) * Real.sqrt (q.inner x w w) :=
    heval.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hnorm.trans hs.le) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  simpa only [q, ContinuousLinearMap.sub_apply] using hfinal

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lapDiff_short
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∀ s ∈ Set.Icc (0 : Real) tau,
        (T : Real) - s ∈ D.regular ∧
          MetricRealization.metricCauchySchwarzBound (I := I) (G.metric (T : Real))
            (fun x : M =>
              (G.metric ((T : Real) - s)).inner x -
                (G.metric (T : Real)).inner x)
            (1 / 4 : Real) := by
  have hshift :
      Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  have hreg :
      ∀ᶠ s in 𝓝 (0 : Real), (T : Real) - s ∈ D.regular :=
    hshift.eventually (D.regular_isOpen.mem_nhds T.2)
  have hsmall := lapDiff_fibreSmall (I := I) (M := M) G hG T
  let U : Set Real := {s |
    (T : Real) - s ∈ D.regular ∧
      MetricRealization.metricCauchySchwarzBound (I := I) (G.metric (T : Real))
        (fun x : M =>
          (G.metric ((T : Real) - s)).inner x -
            (G.metric (T : Real)).inner x)
        (1 / 4 : Real)}
  have hU : U ∈ 𝓝 (0 : Real) := by
    change ∀ᶠ s in 𝓝 (0 : Real),
      (T : Real) - s ∈ D.regular ∧
        MetricRealization.metricCauchySchwarzBound (I := I) (G.metric (T : Real))
          (fun x : M =>
            (G.metric ((T : Real) - s)).inner x -
              (G.metric (T : Real)).inner x)
          (1 / 4 : Real)
    filter_upwards [hreg, hsmall] with s hs hr
    exact ⟨hs, hr⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := min 1 (delta / 2)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htau_one : tau ≤ 1 := min_le_left _ _
  have htau_delta : tau < delta :=
    (min_le_right (1 : Real) (delta / 2)).trans_lt (half_lt_self hdelta)
  refine ⟨tau, htau, htau_one, ?_⟩
  intro s hs
  have hsball : s ∈ Metric.ball (0 : Real) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htau_delta
  simpa only [U] using hball hsball



theorem lapDiffA2_core
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∀ᶠ s in 𝓝 (0 : Real),
      ∀ v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)),
        lapDiffA2 (I := I) (M := M) G T s v.1 =
          lapDiffCore (I := I) (M := M) (G.metric (T : Real))
            (G.metric ((T : Real) - s)) v := by
  let rho : Real → Real := fun s =>
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (G.metric ((T : Real) - s))
      (G.metric (T : Real)) (G.metric (T : Real))
  have hrho : Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho] using lapDiff_rho (I := I) G hG T
  have hsmall :
      ∀ᶠ s in 𝓝 (0 : Real),
        (Module.finrank Real E : Real) * rho s < (1 / 2 : Real) :=
    (hrho.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  filter_upwards [hsmall] with s hs
  intro v
  exact lapDiffOp_core (I := I) (M := M)
    (G.metric (T : Real)) (G.metric ((T : Real) - s)) v hs.le



theorem lapDiffA2_bound
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ omega : Real → Real,
      Tendsto omega (𝓝 0) (𝓝 0) ∧
      ∀ᶠ s in 𝓝 (0 : Real),
        ∀ v : tensorHs (I := I) (M := M)
            (G.metric (T : Real)) 0 0 2,
          (Function.support v.coeff).Finite →
            ‖lapDiffA2 (I := I) (M := M) G T s v‖ <=
              omega s * ‖v‖ := by
  obtain ⟨C, hC, hop⟩ :=
    lapDiffOp_norm (I := I) (M := M) (G.metric (T : Real))
  let rho : Real → Real := fun s =>
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (G.metric ((T : Real) - s))
      (G.metric (T : Real)) (G.metric (T : Real))
  let omega : Real → Real := fun s => Real.sqrt C * |rho s|
  have hrho : Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho] using lapDiff_rho (I := I) G hG T
  have homega : Tendsto omega (𝓝 0) (𝓝 0) := by
    simpa only [omega, abs_zero, mul_zero] using
      hrho.abs.const_mul (Real.sqrt C)
  have hsmall :
      ∀ᶠ s in 𝓝 (0 : Real),
        (Module.finrank Real E : Real) * rho s < (1 / 2 : Real) :=
    (hrho.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  refine ⟨omega, homega, ?_⟩
  filter_upwards [hsmall] with s hs
  intro v hv
  calc
    ‖lapDiffA2 (I := I) (M := M) G T s v‖ <=
        ‖lapDiffA2 (I := I) (M := M) G T s‖ * ‖v‖ :=
      (lapDiffA2 (I := I) (M := M) G T s).le_opNorm v
    _ <= omega s * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      simpa only [lapDiffA2, omega, rho] using
        hop (G.metric ((T : Real) - s)) hs.le



theorem lapDiffA2_zero
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    Tendsto (fun s : Real => ‖lapDiffA2 (I := I) (M := M) G T s‖)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC, hop⟩ :=
    lapDiffOp_norm (I := I) (M := M) (G.metric (T : Real))
  let rho : Real → Real := fun s =>
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (G.metric ((T : Real) - s))
      (G.metric (T : Real)) (G.metric (T : Real))
  have hrho : Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho] using lapDiff_rho (I := I) G hG T
  have hupper :
      Tendsto (fun s => Real.sqrt C * |rho s|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using
      hrho.abs.const_mul (Real.sqrt C)
  have hsmall :
      ∀ᶠ s in 𝓝 (0 : Real),
        (Module.finrank Real E : Real) * rho s < (1 / 2 : Real) :=
    (hrho.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun s => norm_nonneg
      (lapDiffA2 (I := I) (M := M) G T s))
    _ hupper
  filter_upwards [hsmall] with s hs
  simpa only [lapDiffA2, rho] using
    hop (G.metric ((T : Real) - s)) hs.le

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
