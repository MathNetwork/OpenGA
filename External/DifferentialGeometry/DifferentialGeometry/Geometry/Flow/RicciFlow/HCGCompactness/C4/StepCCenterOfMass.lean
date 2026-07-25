import DifferentialGeometry.Geometry.Comparison.HalfSqDistGradMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCInputs

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Connection

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]



structure CenterInput (g : SmoothRiemannianMetric I M)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (pts : ι → M)
    (join : M → M → ℝ → M) (p : M) (r : ℝ) : Prop where
  complete :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M
  enorm :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))
  r_pos : 0 < r
  pts_mem :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ i : ι, dist p (pts i) < r
  μ_nonneg : ∀ i : ι, 0 ≤ μ i
  μ_pos : ∃ i : ι, 0 < μ i
  strict : StrictDistInput (I := I) g pts join p r

namespace CenterInput

variable {g : SmoothRiemannianMetric I M} {ι : Type} [Fintype ι]
  {μ : ι → ℝ} {pts : ι → M} {join : M → M → ℝ → M} {p : M} {r : ℝ}


theorem exists_cm (h : CenterInput (I := I) g μ pts join p r) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ q ∈ Metric.closedBall p (2 * r),
      (∀ y : M, CenterOfMass.centerEnergy (I := I) g μ pts q ≤
        CenterOfMass.centerEnergy (I := I) g μ pts y) ∧
      ∀ y : M,
        (∀ z : M, CenterOfMass.centerEnergy (I := I) g μ pts y ≤
          CenterOfMass.centerEnergy (I := I) g μ pts z) → y = q := by
  exact CenterOfMass.exists_unique_curve (I := I) g h.complete h.enorm μ pts join
    h.r_pos h.pts_mem h.μ_nonneg h.μ_pos h.strict.mid h.strict.zero h.strict.one
    h.strict.strict

end CenterInput


noncomputable def centerOfMass (g : SmoothRiemannianMetric I M)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (pts : ι → M)
    (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) : M :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  Classical.choose h.exists_cm

namespace centerOfMass

variable {g : SmoothRiemannianMetric I M} {ι : Type} [Fintype ι]
  {μ : ι → ℝ} {pts : ι → M} {join : M → M → ℝ → M} {p : M} {r : ℝ}
  (h : CenterInput (I := I) g μ pts join p r)


omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem grad_half_self (q : M)
    (hdiff :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist q) q) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    gradientFun (I := I) g (CenterOfMass.halfSqDist q) q =
      - (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q q) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hlocal : IsLocalMin (CenterOfMass.halfSqDist q) q := by
    unfold IsLocalMin IsMinFilter
    refine Filter.Eventually.of_forall ?_
    intro y
    unfold CenterOfMass.halfSqDist
    have hsq : 0 ≤ dist y q ^ 2 := sq_nonneg (dist y q)
    rw [dist_self]
    nlinarith
  have hgrad0 :
      gradientFun (I := I) g (CenterOfMass.halfSqDist q) q = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g hlocal hdiff
  have hchart0 :
      (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q q) = 0 := by
    change NormalCoordinates.normalChartAt (I := I) g q q = (0 : E)
    exact NormalCoordinates.normalChartAt_centre (I := I) g q
  rw [hgrad0, hchart0, neg_zero]


theorem mem :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerOfMass (I := I) g μ pts join p r h ∈ Metric.closedBall p (2 * r) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec h.exists_cm).1


theorem min :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ y : M,
      CenterOfMass.centerEnergy (I := I) g μ pts
          (centerOfMass (I := I) g μ pts join p r h) ≤
        CenterOfMass.centerEnergy (I := I) g μ pts y := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec h.exists_cm).2.1


theorem unique :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ y : M,
      (∀ z : M, CenterOfMass.centerEnergy (I := I) g μ pts y ≤
        CenterOfMass.centerEnergy (I := I) g μ pts z) →
      y = centerOfMass (I := I) g μ pts join p r h := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec h.exists_cm).2.2



theorem dist_le {qstar : M} {ε : ℝ} (hε : 0 ≤ ε)
    (hnear :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, dist qstar (pts i) ≤ ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (centerOfMass (I := I) g μ pts join p r h) qstar ≤ 2 * ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨q, _hqmem, hqmin, hqdist, _hquniq⟩ :=
    CenterOfMass.exists_unique_curve_dist_le (I := I) g h.complete h.enorm μ pts join
      h.r_pos h.pts_mem hε hnear h.μ_nonneg h.μ_pos h.strict.mid h.strict.zero
      h.strict.one h.strict.strict
  have hq_eq : q = centerOfMass (I := I) g μ pts join p r h := unique h q hqmin
  simpa [hq_eq] using hqdist



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_diff {x : M}
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts i)) x) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.centerEnergy (I := I) g μ pts) x := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hfun :
      CenterOfMass.centerEnergy (I := I) g μ pts =
        (∑ i : ι, μ i • CenterOfMass.halfSqDist (pts i)) := by
    funext q
    rw [CenterOfMass.centerEnergy_eq_dist (I := I) (ι := ι) g μ pts q,
      CenterOfMass.metricEnergy_half (ι := ι)]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact MDifferentiableAt.sum (𝕜 := ℝ) (I := I) (E' := ℝ)
    (t := Finset.univ)
    (f := fun i : ι => μ i • CenterOfMass.halfSqDist (pts i)) (z := x)
    (by
      intro i _hi
      exact (hdiffSummands i).const_smul (μ i))







theorem expInv_eqn
    (hdiffEnergy :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.centerEnergy (I := I) g μ pts)
        (centerOfMass (I := I) g μ pts join p r h))
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts i))
        (centerOfMass (I := I) g μ pts join p r h))
    (hgrad :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        gradientFun (I := I) g (CenterOfMass.halfSqDist (pts i))
            (centerOfMass (I := I) g μ pts join p r h) =
          - (show TangentSpace I (centerOfMass (I := I) g μ pts join p r h) from
              NormalCoordinates.normalChartAt (I := I) g
                (centerOfMass (I := I) g μ pts join p r h) (pts i))) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∑ i : ι, μ i •
      (show TangentSpace I (centerOfMass (I := I) g μ pts join p r h) from
        NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ pts join p r h) (pts i)) = 0 := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact CenterOfMass.sum_expInv_eq_zero (I := I) (κ := ι) g μ pts
    (centerOfMass (I := I) g μ pts join p r h) (min h) hdiffEnergy hdiffSummands hgrad



theorem invB_eqn
    (invB : ι → TangentSpace I (centerOfMass (I := I) g μ pts join p r h))
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts i))
        (centerOfMass (I := I) g μ pts join p r h))
    (hgrad :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        gradientFun (I := I) g (CenterOfMass.halfSqDist (pts i))
            (centerOfMass (I := I) g μ pts join p r h) = -invB i) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∑ i : ι, μ i • invB i = 0 := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hsum := CenterOfMass.sum_grad_eq_zero (I := I) (κ := ι) g μ pts
    (centerOfMass (I := I) g μ pts join p r h) (min h)
    (centerEnergy_diff (I := I) (g := g) hdiffSummands) hdiffSummands
  have hneg : ∑ i : ι, μ i • (-invB i) = 0 := by
    calc
      ∑ i : ι, μ i • (-invB i) =
          ∑ i : ι, μ i • gradientFun (I := I) g
            (CenterOfMass.halfSqDist (pts i))
            (centerOfMass (I := I) g μ pts join p r h) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hgrad i]
      _ = 0 := hsum
  have hsum_neg : -(∑ i : ι, μ i • invB i) = 0 := by
    simpa only [Finset.sum_neg_distrib, smul_neg] using hneg
  exact neg_eq_zero.mp hsum_neg




theorem expInv_eqn_local
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts i))
        (centerOfMass (I := I) g μ pts join p r h))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, pts i ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ pts join p r h)).source) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧
      ((∀ i : ι, pts i ≠ centerOfMass (I := I) g μ pts join p r h →
        Real.sqrt
          (g.inner (centerOfMass (I := I) g μ pts join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ pts join p r h) (pts i) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ pts join p r h) (pts i) : E)) < ρ) →
        ∑ i : ι, μ i •
          (show TangentSpace I (centerOfMass (I := I) g μ pts join p r h) from
            NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ pts join p r h) (pts i)) = 0) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  haveI : CompleteSpace M := h.complete
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  set q := centerOfMass (I := I) g μ pts join p r h
  obtain ⟨ρ, hρ, hgradρ⟩ := grad_halfSqDist (I := I) g h.enorm q
  refine ⟨ρ, hρ, ?_⟩
  intro hsmall
  refine expInv_eqn h (centerEnergy_diff (I := I) (g := g) hdiffSummands)
    hdiffSummands ?_
  intro i
  by_cases hself : pts i = q
  · rw [hself]
    have hdiffSelf :
        MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist q) q := by
      simpa [hself] using hdiffSummands i
    exact grad_half_self (I := I) (g := g) q hdiffSelf
  · exact hgradρ (hsrc i) hself (hsmall i hself) (hdiffSummands i)





noncomputable def eqnRadius : ℝ :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := h.complete
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  Classical.choose (grad_halfSqDist (I := I) g h.enorm
    (centerOfMass (I := I) g μ pts join p r h))


theorem eqnRadius_pos : 0 < eqnRadius (I := I) h := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  haveI : CompleteSpace M := h.complete
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec (grad_halfSqDist (I := I) g h.enorm
    (centerOfMass (I := I) g μ pts join p r h))).1



theorem grad_eq_of_lt {pt : M}
    (hsrc : pt ∈ (NormalCoordinates.normalChartAt (I := I) g
      (centerOfMass (I := I) g μ pts join p r h)).source)
    (hne : pt ≠ centerOfMass (I := I) g μ pts join p r h)
    (hsmall : Real.sqrt
      (g.inner (centerOfMass (I := I) g μ pts join p r h)
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ pts join p r h) pt : E)
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ pts join p r h) pt : E)) <
      eqnRadius (I := I) h)
    (hdiff :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt)
        (centerOfMass (I := I) g μ pts join p r h)) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    gradientFun (I := I) g (CenterOfMass.halfSqDist pt)
      (centerOfMass (I := I) g μ pts join p r h) =
      -(show TangentSpace I (centerOfMass (I := I) g μ pts join p r h) from
        NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ pts join p r h) pt) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  haveI : CompleteSpace M := h.complete
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec (grad_halfSqDist (I := I) g h.enorm
    (centerOfMass (I := I) g μ pts join p r h))).2 hsrc hne hsmall hdiff



theorem expInv_eqn_of_lt
    (hdiffSummands :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (pts i))
        (centerOfMass (I := I) g μ pts join p r h))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, pts i ∈ (NormalCoordinates.normalChartAt (I := I) g
        (centerOfMass (I := I) g μ pts join p r h)).source)
    (hsmall :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, pts i ≠ centerOfMass (I := I) g μ pts join p r h →
        Real.sqrt
          (g.inner (centerOfMass (I := I) g μ pts join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ pts join p r h) (pts i) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ pts join p r h) (pts i) : E)) <
          eqnRadius (I := I) h) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∑ i : ι, μ i •
      (show TangentSpace I (centerOfMass (I := I) g μ pts join p r h) from
        NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ pts join p r h) (pts i)) = 0 := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine expInv_eqn h (centerEnergy_diff (I := I) (g := g) hdiffSummands)
    hdiffSummands ?_
  intro i
  by_cases hself : pts i = centerOfMass (I := I) g μ pts join p r h
  · rw [hself]
    have hdiffSelf :
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (CenterOfMass.halfSqDist (centerOfMass (I := I) g μ pts join p r h))
          (centerOfMass (I := I) g μ pts join p r h) := by
      simpa [hself] using hdiffSummands i
    exact grad_half_self (I := I) (g := g) _ hdiffSelf
  · exact grad_eq_of_lt h (hsrc i) hself (hsmall i hself) (hdiffSummands i)

end centerOfMass








theorem centerOfMass_cont {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : P → ι → ℝ) (pts : P → ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ) (p₀ : P)
    (H : ∀ a : P, CenterInput (I := I) g (μ a) (pts a) join p r)
    (hμ : Continuous μ) (hpts : Continuous pts) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    Filter.Tendsto (fun a : P => centerOfMass (I := I) g (μ a) (pts a) join p r (H a)) (nhds p₀)
      (nhds (centerOfMass (I := I) g (μ p₀) (pts p₀) join p r (H p₀))) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  haveI : ProperSpace M :=
    HopfRinow.properSpace_riemMetric (I := I) (M := M) (H p₀).complete g (H p₀).enorm
  refine CenterOfMass.metricEnergy_argmin_stable (isCompact_closedBall p (2 * r))
    μ pts (fun a => centerOfMass (I := I) g (μ a) (pts a) join p r (H a)) p₀ hμ hpts ?_ ?_ ?_
  · intro a y
    simp only [← CenterOfMass.centerEnergy_eq_dist (I := I) g (μ a) (pts a)]
    exact centerOfMass.min (H a) y
  · intro a
    exact centerOfMass.mem (H a)
  · intro y hy
    refine centerOfMass.unique (H p₀) y (fun z => ?_)
    simp only [CenterOfMass.centerEnergy_eq_dist (I := I) g (μ p₀) (pts p₀)]
    exact hy z

end HCGCompactness
end DifferentialGeometry
