import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchHessian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCInputs

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace HasNormalBrFull




theorem strict_dist
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hfull : HasNormalBrFull (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    (hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    {ι : Type} [Fintype ι] (pts : ι → (X.obj k).M)
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
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
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
    Metric.ball (0 : E) ρ ⊆ normalQuarter (I := I) (X.obj k) x →
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ hb.radius k x →
      ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
      0 < r →
      dist x p ≤ R →
      (∀ i, dist p (pts i) < r) →
      ENNReal.ofReal (R + 6 * r) < ENNReal.ofReal (ρ / 2) →
      StrictDistInput (I := I) (X.obj k).metric pts
        (minJoin (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))) p r := by
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
  letI : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
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
  intro hquarter hρ hρq hρmetric hρexp hr hxp hpts hcage
  let hEnorm := normal_enorm (I := I) (X.obj k)
  let join := minJoin (I := I) (X.obj k).metric hEnorm
  have hfullData := hfull
  dsimp only [HasNormalBrFull] at hfullData
  rcases hfullData with
    ⟨hq, e, he, hf, _hclosed, _hδdom, _hhom, _hpair, _hinv,
      _hδinv, _eta, _heta, _happrox⟩
  have hR6pos : 0 < R + 6 * r := by
    nlinarith [show 0 ≤ dist x p from dist_nonneg]
  have hjoin_dist (a b : (X.obj k).M) {t : Real} (ht : 0 ≤ t) :
      dist a (join a b t) ≤ dist a b * t := by
    have hed := minJoin_edist_le (I := I) (X.obj k).metric hEnorm a b ht
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hmul : 0 ≤ (riemannianEDist I a b).toReal * t :=
      mul_nonneg ENNReal.toReal_nonneg ht
    rw [ENNReal.toReal_ofReal hmul] at hmono
    simpa only [join, ← HopfRinow.riemMetric_dist_eq] using hmono
  have hjoin_cage (a : (X.obj k).M)
      (ha : a ∈ Metric.closedBall p (2 * r)) (b : (X.obj k).M)
      (hbmem : b ∈ Metric.closedBall p (2 * r)) {t : Real}
      (ht : t ∈ unitInterval) :
      dist x (join a b t) ≤ R + 6 * r := by
    have ha' : dist p a ≤ 2 * r := by
      simpa only [dist_comm] using Metric.mem_closedBall.mp ha
    have hb' : dist p b ≤ 2 * r := by
      simpa only [dist_comm] using Metric.mem_closedBall.mp hbmem
    have hab : dist a b ≤ 4 * r := by
      calc
        dist a b ≤ dist a p + dist p b := dist_triangle _ _ _
        _ ≤ 4 * r := by
          have hap : dist a p ≤ 2 * r := Metric.mem_closedBall.mp ha
          linarith
    have hajoin : dist a (join a b t) ≤ 4 * r := by
      have hraw := hjoin_dist a b ht.1
      have habt : dist a b * t ≤ 4 * r := by
        calc
          dist a b * t ≤ dist a b * 1 :=
            mul_le_mul_of_nonneg_left ht.2 dist_nonneg
          _ ≤ 4 * r := by simpa only [mul_one] using hab
      exact hraw.trans habt
    calc
      dist x (join a b t) ≤ dist x p + dist p a + dist a (join a b t) :=
        dist_triangle4 _ _ _ _
      _ ≤ R + 6 * r := by linarith
  have hriem_eq (a b : (X.obj k).M) :
      riemannianEDist I a b = ENNReal.ofReal (dist a b) := by
    rw [HopfRinow.riemMetric_dist_eq]
    exact (ENNReal.ofReal_toReal
      (riemannianEDist_ne_top (I := I) a b)).symm
  have hpair_cage (pt : (X.obj k).M) (hpt : dist x pt < R + 6 * r)
      (a : (X.obj k).M) (ha : a ∈ Metric.closedBall p (2 * r))
      (b : (X.obj k).M) (hbmem : b ∈ Metric.closedBall p (2 * r))
      {t : Real} (ht : t ∈ unitInterval) :
      max (riemannianEDist I x (join a b t)) (riemannianEDist I x pt) <
        ENNReal.ofReal (ρ / 2) := by
    rw [max_lt_iff]
    constructor
    · have hjoinEd : riemannianEDist I x (join a b t) ≤
          ENNReal.ofReal (R + 6 * r) := by
        rw [hriem_eq]
        exact ENNReal.ofReal_le_ofReal (hjoin_cage a ha b hbmem ht)
      exact hjoinEd.trans_lt hcage
    · have hptEd : riemannianEDist I x pt <
          ENNReal.ofReal (R + 6 * r) := by
        rw [hriem_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff hR6pos).2 hpt
      exact hptEd.trans hcage
  have hpCage : dist x p < R + 6 * r := by linarith
  have hptsCage (i : ι) : dist x (pts i) < R + 6 * r := by
    calc
      dist x (pts i) ≤ dist x p + dist p (pts i) := dist_triangle _ _ _
      _ < R + r := add_lt_add_of_le_of_lt hxp (hpts i)
      _ < R + 6 * r := by nlinarith
  have hstrict_pt (pt : (X.obj k).M) (hpt : dist x pt < R + 6 * r)
      (a : (X.obj k).M) (ha : a ∈ Metric.closedBall p (2 * r))
      (b : (X.obj k).M) (hbmem : b ∈ Metric.closedBall p (2 * r))
      (hab : a ≠ b) :
      StrictConvexOn Real unitInterval
        (fun t : Real => CenterOfMass.halfSqDist pt (join a b t)) := by
    let S : Set (X.obj k).M :=
      {y | max (riemannianEDist I x y) (riemannianEDist I x pt) <
        ENNReal.ofReal (ρ / 2)}
    let γ : Real → (X.obj k).M := join a b
    let v₀ : TangentSpace I a := minimizingVec
      (I := I) (X.obj k).metric hEnorm a b
    have hSopen : IsOpen S := by
      dsimp only [S]
      exact isOpen_lt
        ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
          continuous_const) continuous_const
    have hsmooth : ContMDiffOn I 𝓘(Real) ∞
        (CenterOfMass.halfSqDist pt) S := by
      simpa only [S] using IsNormalDiag.halfSq_inf (I := I) hb k hcomplete
        hconn x hq he hf hρ hρq hρmetric hρexp
    have hmap : MapsTo γ unitInterval S := by
      intro t ht
      simpa only [γ, S] using hpair_cage pt hpt a ha b hbmem ht
    have hgeo : IsGeodesic (I := I) (X.obj k).metric γ := by
      simpa only [γ, join, minJoin, v₀] using
        intrinsicGeodesic_isGeodesic (I := I) (X.obj k).metric hEnorm a v₀
    have hγcont : Continuous γ := by
      simpa only [γ, join] using
        minJoin_cont (I := I) (X.obj k).metric hEnorm a b
    have hγsmooth : ContMDiff 𝓘(Real) I ∞ γ :=
      isGeodesic_contMDiff (I := I) (X.obj k).metric hgeo hγcont
    have hv₀ : v₀ ≠ 0 := by
      intro hvzero
      apply hab
      calc
        a = expMapIntrinsic (I := I) (X.obj k).metric hEnorm a 0 :=
          (expMapIntrinsic_zero (I := I) (X.obj k).metric hEnorm a).symm
        _ = expMapIntrinsic (I := I) (X.obj k).metric hEnorm a v₀ := by
          rw [hvzero]
        _ = b := by
          simpa only [v₀] using
            minimizingVec_exp (I := I) (X.obj k).metric hEnorm a b
    have hvel (t : Real) :
        mfderiv 𝓘(Real) I γ t 1 ≠ 0 := by
      intro hzero
      have hspeed := intrinsicGeodesic_speedSq_eq
        (I := I) (X.obj k).metric hEnorm a v₀ t
      have hspeed' : (X.obj k).metric.inner (γ t)
          (mfderiv 𝓘(Real) I γ t 1) (mfderiv 𝓘(Real) I γ t 1) =
          (X.obj k).metric.inner a v₀ v₀ := by
        simpa only [γ, join, minJoin, v₀] using hspeed
      have hlaunch : 0 < (X.obj k).metric.inner a v₀ v₀ :=
        (X.obj k).metric.pos a v₀ hv₀
      apply (ne_of_gt hlaunch)
      rw [← hspeed', hzero]
      simp
    have hcont : ContinuousOn
        ((CenterOfMass.halfSqDist pt) ∘ γ) unitInterval :=
      hsmooth.continuousOn.comp hγsmooth.continuous.continuousOn hmap
    have hmem : MapsTo γ (interior unitInterval) S :=
      fun t ht => hmap (interior_subset ht)
    have hpos : ∀ t ∈ interior unitInterval,
        0 < hessFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) (γ t)
          (mfderiv 𝓘(Real) I γ t 1) (mfderiv 𝓘(Real) I γ t 1) := by
      intro t ht
      exact HasNormalBrFull.hess_pos (I := I) hb k hcomplete hconn x hfull
        hqAcc hquarter hρ hρq hρmetric hρexp
          (by simpa only [γ, S] using hmem ht) (hvel t)
    simpa only [Function.comp_apply, γ] using
      strictConvex_geo (I := I) (X.obj k).metric hSopen hsmooth hγsmooth hgeo
        (convex_Icc (0 : Real) 1) hcont hmem hpos
  change StrictDistInput (I := I) (X.obj k).metric pts join p r
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hbmem hab
    have hstrictP := hstrict_pt p hpCage a ha b hbmem hab
    have hlt := hstrictP.2 unitInterval.zero_mem unitInterval.one_mem
      (by norm_num : (0 : Real) ≠ 1)
      (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (1 / 2 : Real) + 1 / 2 = 1)
    norm_num at hlt
    have hltMid :
        CenterOfMass.halfSqDist p (join a b (1 / 2 : Real)) <
          (1 / 2 : Real) * CenterOfMass.halfSqDist p a +
            (1 / 2 : Real) * CenterOfMass.halfSqDist p b := by
      simpa only [join, minJoin_zero, minJoin_one, one_smul, Function.comp_apply,
        smul_eq_mul] using hlt
    have hRnonneg : 0 ≤ 2 * r := by positivity
    have haDist : dist a p ≤ 2 * r := Metric.mem_closedBall.mp ha
    have hbDist : dist b p ≤ 2 * r := Metric.mem_closedBall.mp hbmem
    have haSq : dist a p ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ dist_nonneg hRnonneg).2 haDist
    have hbSq : dist b p ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ dist_nonneg hRnonneg).2 hbDist
    have hsq : dist (join a b (1 / 2 : Real)) p ^ 2 ≤ (2 * r) ^ 2 := by
      simp only [CenterOfMass.halfSqDist] at hltMid
      nlinarith
    exact Metric.mem_closedBall.2 ((sq_le_sq₀ dist_nonneg hRnonneg).1 hsq)
  · intro a _ha b _hb
    exact minJoin_zero (I := I) (X.obj k).metric hEnorm a b
  · intro a _ha b _hb
    exact minJoin_one (I := I) (X.obj k).metric hEnorm a b
  · intro i a ha b hbmem hab
    exact hstrict_pt (pts i) (hptsCage i) a ha b hbmem hab

end HasNormalBrFull

end HCGCompactness
end DifferentialGeometry
