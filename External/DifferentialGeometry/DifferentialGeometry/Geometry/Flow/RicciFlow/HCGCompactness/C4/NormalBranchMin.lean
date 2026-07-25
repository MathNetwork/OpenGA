import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagBranch
import DifferentialGeometry.Geometry.Comparison.CenterOfMass
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGradMain
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



omit [NeZero (Module.finrank ℝ E)] in
theorem normalTan_metric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y x z.1 z.2 z.2 =
      Y.metric.inner (normalTangent (I := I) Y x z).proj
        (normalTangent (I := I) Y x z).snd
        (normalTangent (I := I) Y x z).snd := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [normalCoordMetric_apply]
  rfl



theorem normalTanHome_target
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalTanHome (I := I) Y x).target =
      Bundle.TotalSpace.proj ⁻¹' (normalExpPD (I := I) Y x).target := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [normalTanHome, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,
    PartialDiffeomorph.tangentHome, preimage_univ, inter_univ]

namespace IsNormalDiag



theorem tan_mem_of_small
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {y : (X.obj k).M} :
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
    ∀ {v : TangentSpace I y},
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
    riemannianEDist I x y < ENNReal.ofReal (ρ / 2) →
    Real.sqrt ((X.obj k).metric.inner y v v) < ρ →
    (⟨y, v⟩ : TangentBundle I (X.obj k).M) ∈
      (IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn
        x hq he).hom.source := by
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
  intro v hρ hρq hρmetric hρexp hy hv
  have hyFin : riemannianEDist I x y ≠ ⊤ :=
    ne_of_lt (hy.trans ENNReal.ofReal_lt_top)
  have hyReal : (riemannianEDist I x y).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hyFin).mp hy
  have hyControl := hb.chart_mem_norm_le k x y
    ⟨hyFin, hyReal.trans_le hρexp⟩
  let a : E := NormalCoordinates.normalChartAt
    (I := I) (X.obj k).metric x y
  have haρ : ‖a‖ < ρ := by
    calc
      ‖a‖ ≤ 2 * (riemannianEDist I x y).toReal := hyControl.2
      _ < 2 * (ρ / 2) := mul_lt_mul_of_pos_left hyReal (by norm_num)
      _ = ρ := by ring
  have hρq' : ρ < (q : Real) := by nlinarith
  have haClosed : (a, (0 : E)) ∈ Metric.closedBall (0 : E × E) q := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le (haρ.trans hρq').le (by simp)
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) (X.obj k) x ∧
    (e z).1 ∈ normalBall (I := I) (X.obj k) x ∧
    (e z).2 ∈ normalBall (I := I) (X.obj k) x at hfence
  have haNormal : a ∈ normalBall (I := I) (X.obj k) x :=
    (hfence (a, 0) haClosed).1
  have haSource : a ∈ (normalExpPD (I := I) (X.obj k) x).source := by
    simpa only [normalExpPD_source] using haNormal
  have haNorm : ‖a‖ < expMapC2Radius (I := I) (X.obj k).metric x := by
    have haNormal' := haNormal
    change a ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric x) at haNormal'
    rwa [Metric.mem_ball, dist_zero_right] at haNormal'
  have haExpSource : a ∈
      (NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius
      (I := I) (X.obj k).metric x haNorm
  have haTarget : a ∈
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).target :=
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).map_source
      hyControl.1
  have hyDecode : NormalCoordinates.expMapDiffeo
      (I := I) (X.obj k).metric x a = y := by
    calc
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x a =
          expMap (I := I) (X.obj k).metric x a :=
        NormalCoordinates.expMapDiffeo_apply_eq
          (I := I) (X.obj k).metric x haExpSource
      _ = (NormalCoordinates.normalChartAt
          (I := I) (X.obj k).metric x).symm a :=
        (NormalCoordinates.normalChartAt_symm_apply
          (I := I) (X.obj k).metric x haTarget).symm
      _ = y :=
        (NormalCoordinates.normalChartAt
          (I := I) (X.obj k).metric x).left_inv hyControl.1
  have hyTarget : y ∈ (normalExpPD (I := I) (X.obj k) x).target := by
    have hmap := (normalExpPD (I := I) (X.obj k) x).map_source haSource
    change NormalCoordinates.expMapDiffeo
      (I := I) (X.obj k).metric x a ∈
        (normalExpPD (I := I) (X.obj k) x).target at hmap
    rwa [hyDecode] at hmap
  let A := normalTanHome (I := I) (X.obj k) x
  let u : TangentBundle I (X.obj k).M := ⟨y, v⟩
  have huTarget : u ∈ A.target := by
    change u ∈ (normalTanHome (I := I) (X.obj k) x).target
    rw [normalTanHome_target]
    exact hyTarget
  let z : E × E := A.symm u
  have hzSource : z ∈ A.source := A.map_target huTarget
  have hAz : A z = u := A.right_inv huTarget
  have hzNormal : z.1 ∈ normalBall (I := I) (X.obj k) x := by
    have hzSource' : z ∈ (normalTanHome (I := I) (X.obj k) x).source := hzSource
    rw [normalTanHome_source] at hzSource'
    exact hzSource'
  have hnt : normalTangent (I := I) (X.obj k) x z = u := by
    calc
      normalTangent (I := I) (X.obj k) x z = A z :=
        (normalTanHome_apply (I := I) (X.obj k) x z hzNormal).symm
      _ = u := hAz
  have hbase : NormalCoordinates.expMapDiffeo
      (I := I) (X.obj k).metric x z.1 = y := by
    simpa only [normalTangent, u] using
      congrArg (Bundle.TotalSpace.proj :
        TangentBundle I (X.obj k).M → (X.obj k).M) hnt
  have hzLeft := (normalExpPD (I := I) (X.obj k) x).left_inv (by
    simpa only [normalExpPD_source] using hzNormal)
  have hz1 : z.1 = a := by
    calc
      z.1 = NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x
          (NormalCoordinates.expMapDiffeo
            (I := I) (X.obj k).metric x z.1) := hzLeft.symm
      _ = NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x y :=
        congrArg (NormalCoordinates.normalChartAt
          (I := I) (X.obj k).metric x) hbase
      _ = a := rfl
  have hzMetric : z.1 ∈ Metric.ball (0 : E) (hb.radius k x) := by
    rw [Metric.mem_ball, dist_zero_right, hz1]
    exact haρ.trans_le hρmetric
  have hcoerc := (hb.metric_equiv k x z.1 hzMetric z.2).1
  have hmetric : normalCoordMetric (I := I) (X.obj k) x z.1 z.2 z.2 =
      (X.obj k).metric.inner y v v := by
    calc
      normalCoordMetric (I := I) (X.obj k) x z.1 z.2 z.2 =
          (X.obj k).metric.inner
            (normalTangent (I := I) (X.obj k) x z).proj
            (normalTangent (I := I) (X.obj k) x z).snd
            (normalTangent (I := I) (X.obj k) x z).snd :=
        normalTan_metric (I := I) (X.obj k) x z
      _ = (X.obj k).metric.inner u.proj u.snd u.snd :=
        congrArg (fun w : TangentBundle I (X.obj k).M ↦
          (X.obj k).metric.inner w.proj w.snd w.snd) hnt
      _ = (X.obj k).metric.inner y v v := rfl
  rw [hmetric] at hcoerc
  have hinnerNonneg : 0 ≤ (X.obj k).metric.inner y v v := by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · exact ((X.obj k).metric.pos y v hv0).le
  have hinnerLt : (X.obj k).metric.inner y v v < ρ ^ 2 := by
    nlinarith [Real.sq_sqrt hinnerNonneg,
      Real.sqrt_nonneg ((X.obj k).metric.inner y v v)]
  have hz2 : ‖z.2‖ < 2 * ρ := by
    by_contra hnot
    have hge : 2 * ρ ≤ ‖z.2‖ := le_of_not_gt hnot
    have hsq : (2 * ρ) ^ 2 ≤ ‖z.2‖ ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (by norm_num) hρ.le) (norm_nonneg z.2)).2 hge
    nlinarith
  have hzBall : z ∈ Metric.ball (0 : E × E) q := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    constructor
    · rw [hz1]
      exact haρ.trans (by nlinarith)
    · exact hz2.trans hρq
  have htransport := IsNormalDiag.full_transport (I := I) (X.obj k)
    hcomplete hconn x hq he hf
  rw [← htransport.1]
  exact ⟨z, hzBall, hAz⟩



theorem inv_is_min
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {y pt : (X.obj k).M} :
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
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn
      x hq he
    ∃ v : TangentSpace I y,
      (y, pt) ∈ B.dom ∧
      B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I (X.obj k).M) ∧
      expMapIntrinsic (I := I) (X.obj k).metric
        (normal_enorm (I := I) (X.obj k)) y v = pt ∧
      Real.sqrt ((X.obj k).metric.inner y v v) =
        (riemannianEDist I y pt).toReal := by
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
  intro hρ hρq hρmetric hρexp hpairs
  have hy : riemannianEDist I x y < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt hpairs
  have hpt : riemannianEDist I x pt < ENNReal.ofReal (ρ / 2) :=
    (le_max_right _ _).trans_lt hpairs
  have hyx : riemannianEDist I y x < ENNReal.ofReal (ρ / 2) := by
    simpa only [riemannianEDist_comm] using hy
  have hsum : ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) =
      ENNReal.ofReal ρ := by
    calc
      ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) =
          ENNReal.ofReal (ρ / 2 + ρ / 2) :=
        (ENNReal.ofReal_add (by linarith) (by linarith)).symm
      _ = ENNReal.ofReal ρ := by ring_nf
  have hyp : riemannianEDist I y pt < ENNReal.ofReal ρ := by
    calc
      riemannianEDist I y pt ≤
      riemannianEDist I y x + riemannianEDist I x pt :=
        Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) :=
        ENNReal.add_lt_add hyx hpt
      _ = ENNReal.ofReal ρ := hsum
  have hypReal : (riemannianEDist I y pt).toReal < ρ :=
    (ENNReal.lt_ofReal_iff_toReal_lt
      (riemannianEDist_ne_top (I := I) y pt)).mp hyp
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) (X.obj k).metric (normal_enorm (I := I) (X.obj k)) y pt
  have hvSmall : Real.sqrt ((X.obj k).metric.inner y v v) < ρ := by
    rw [hlen]
    exact hypReal
  have hvsrc := tan_mem_of_small (I := I) hb k hcomplete hconn x hq he hf
    hρ hρq hρmetric hρexp hy hvSmall
  let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  have hinv : B.inv (y, pt) =
      (⟨y, v⟩ : TangentBundle I (X.obj k).M) :=
    B.inv_eq_of_exp hvsrc hexp
  have hdom : (y, pt) ∈ B.dom := by
    have hmap := B.hom.map_source hvsrc
    have hhom : B.hom (⟨y, v⟩ : TangentBundle I (X.obj k).M) = (y, pt) := by
      calc
        B.hom (⟨y, v⟩ : TangentBundle I (X.obj k).M) =
            diagExp (I := I) (X.obj k).metric
              (normal_enorm (I := I) (X.obj k))
              (⟨y, v⟩ : TangentBundle I (X.obj k).M) := B.hom_eq hvsrc
        _ = (y, pt) := by simp only [diagExp_apply, hexp]
    rw [hhom] at hmap
    exact hmap
  exact ⟨v, hdom, hinv, hexp, hlen⟩



theorem halfSq_eq_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {y pt : (X.obj k).M} :
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
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn
      x hq he
    CenterOfMass.halfSqDist pt y =
      (1 / 2 : Real) * (X.obj k).metric.inner
        (B.inv (y, pt)).proj (B.inv (y, pt)).snd (B.inv (y, pt)).snd := by
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
  intro hρ hρq hρmetric hρexp hpairs
  obtain ⟨v, _hdom, hinv, _hexp, hlen⟩ :=
    inv_is_min (I := I) hb k hcomplete hconn x hq he hf
      hρ hρq hρmetric hρexp hpairs
  have hinnerNonneg : 0 ≤ (X.obj k).metric.inner y v v := by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · exact ((X.obj k).metric.pos y v hv0).le
  unfold CenterOfMass.halfSqDist
  rw [HopfRinow.riemMetric_dist_eq (I := I) (M := (X.obj k).M) y pt]
  dsimp only
  rw [hinv, ← hlen, Real.sq_sqrt hinnerNonneg]



theorem halfSq_inf
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {pt : (X.obj k).M} :
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
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
    ContMDiffOn I 𝓘(Real) ∞ (CenterOfMass.halfSqDist pt)
      {y : (X.obj k).M |
        max (riemannianEDist I x y) (riemannianEDist I x pt) <
          ENNReal.ofReal (ρ / 2)} := by
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
  intro hρ hρq hρmetric hρexp
  let S : Set (X.obj k).M :=
    {y | max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  have hdom : ∀ y ∈ S, (y, pt) ∈ B.dom := by
    intro y hy
    exact (inv_is_min (I := I) hb k hcomplete hconn x hq he hf
      hρ hρq hρmetric hρexp hy).choose_spec.1
  have hpair : ContMDiffOn I (I.prod I) ∞ (fun y : (X.obj k).M ↦ (y, pt)) S :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  have hu : ContMDiffOn I I.tangent ∞ (fun y : (X.obj k).M ↦ B.inv (y, pt)) S := by
    simpa only [DiagInvBranch.inv, DiagInvBranch.dom, Function.comp_apply] using
      B.inv_inf.comp hpair hdom
  have hbase : ContMDiffOn I I ∞
      (fun y : (X.obj k).M ↦ (B.inv (y, pt)).proj) S := by
    intro y hy
    have h_at := hu y hy
    rw [contMDiffWithinAt_totalSpace] at h_at
    exact h_at.1
  have hg : ContMDiffOn I
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun y : (X.obj k).M ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun z : (X.obj k).M ↦
            TangentSpace I z →L[Real] TangentSpace I z →L[Real] Real)
          (B.inv (y, pt)).proj ((X.obj k).metric.inner (B.inv (y, pt)).proj))
      S :=
    (X.obj k).metric.contMDiff.comp_contMDiffOn hbase
  have htotal : ContMDiffOn I (I.prod 𝓘(Real, Real)) ∞
      (fun y : (X.obj k).M ↦
        TotalSpace.mk' Real (E := Bundle.Trivial (X.obj k).M Real)
          (B.inv (y, pt)).proj
          ((X.obj k).metric.inner (B.inv (y, pt)).proj
            (B.inv (y, pt)).snd (B.inv (y, pt)).snd)) S :=
    ContMDiffOn.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) (F₃ := Real)
      (E₁ := fun z : (X.obj k).M ↦ TangentSpace I z)
      (E₂ := fun z : (X.obj k).M ↦ TangentSpace I z)
      (E₃ := Bundle.Trivial (X.obj k).M Real)
      (b := fun y ↦ (B.inv (y, pt)).proj)
      (ψ := fun y ↦ (X.obj k).metric.inner (B.inv (y, pt)).proj)
      (v := fun y ↦ (B.inv (y, pt)).snd)
      (w := fun y ↦ (B.inv (y, pt)).snd)
      hg hu hu
  have hinner : ContMDiffOn I 𝓘(Real) ∞
      (fun y : (X.obj k).M ↦
        (X.obj k).metric.inner (B.inv (y, pt)).proj
          (B.inv (y, pt)).snd (B.inv (y, pt)).snd) S := by
    intro y hy
    have h_at := htotal y hy
    rw [contMDiffWithinAt_totalSpace] at h_at
    exact h_at.2
  have henergy : ContMDiffOn I 𝓘(Real) ∞
      (fun y : (X.obj k).M ↦ (1 / 2 : Real) *
        (X.obj k).metric.inner (B.inv (y, pt)).proj
          (B.inv (y, pt)).snd (B.inv (y, pt)).snd) S :=
    (contMDiffOn_const (c := (1 / 2 : Real))).mul hinner
  refine henergy.congr ?_
  intro y hy
  exact halfSq_eq_inv (I := I) hb k hcomplete hconn x hq he hf
    hρ hρq hρmetric hρexp hy



theorem grad_half_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {y pt : (X.obj k).M} :
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
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn
      x hq he
    gradientFun (I := I) (X.obj k).metric
      (CenterOfMass.halfSqDist pt) y =
        -(show TangentSpace I y from (B.inv (y, pt)).snd) := by
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
  intro hρ hρq hρmetric hρexp hpairs
  dsimp only
  let S : Set (X.obj k).M :=
    {z | max (riemannianEDist I x z) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  have hSopen : IsOpen S := by
    dsimp only [S]
    exact isOpen_lt
      ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
        continuous_const) continuous_const
  have hsmooth : ContMDiffOn I 𝓘(Real) ∞
      (CenterOfMass.halfSqDist pt) S := by
    simpa only [S] using
      halfSq_inf (I := I) hb k hcomplete hconn x hq he hf
        hρ hρq hρmetric hρexp
  have hyS : y ∈ S := by
    simpa only [S] using hpairs
  have hdiff : MDifferentiableAt I 𝓘(Real, Real)
      (CenterOfMass.halfSqDist pt) y :=
    (hsmooth.contMDiffAt (hSopen.mem_nhds hyS)).mdifferentiableAt (by simp)
  obtain ⟨v, _hdom, hinv, hexp, hlen⟩ :=
    inv_is_min (I := I) hb k hcomplete hconn x hq he hf
      hρ hρq hρmetric hρexp hpairs
  have hgrad := grad_halfSqDist_min (I := I) (X.obj k).metric
    (normal_enorm (I := I) (X.obj k)) y pt v hexp hlen hdiff
  change gradientFun (I := I) (X.obj k).metric
    (CenterOfMass.halfSqDist pt) y =
      -(show TangentSpace I y from (B.inv (y, pt)).snd)
  rw [hinv]
  exact hgrad




theorem hess_half_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {y pt : (X.obj k).M} :
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
    ∀ v w : TangentSpace I y,
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ expRadiusGp (I := I) (X.obj k).metric x →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn
      x hq he
    hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y v w =
      (X.obj k).metric.inner y
        ((LeviCivita (I := I) (X.obj k).metric).toFun
          (fun z => -(show TangentSpace I z from (B.inv (z, pt)).snd))
          y v) w := by
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
  intro v w hρ hρq hρmetric hρexp hpairs
  dsimp only
  let S : Set (X.obj k).M :=
    {z | max (riemannianEDist I x z) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  let B := IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  have hSopen : IsOpen S := by
    dsimp only [S]
    exact isOpen_lt
      ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
        continuous_const) continuous_const
  have hyS : y ∈ S := by
    simpa only [S] using hpairs
  have hsmooth : ContMDiffOn I 𝓘(Real) ∞
      (CenterOfMass.halfSqDist pt) S := by
    simpa only [S] using
      halfSq_inf (I := I) hb k hcomplete hconn x hq he hf
        hρ hρq hρmetric hρexp
  have hdom : ∀ z ∈ S, (z, pt) ∈ B.dom := by
    intro z hz
    exact (inv_is_min (I := I) hb k hcomplete hconn x hq he hf
      hρ hρq hρmetric hρexp hz).choose_spec.1
  have hinv_at :=
    ((B.inv_snd_inf hdom).contMDiffAt (hSopen.mem_nhds hyS)).mdifferentiableAt
      (by simp)
  have hneg_at := mdifferentiableAt_neg_section hinv_at
  have hgrad :
      (fun z => gradientFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) z) =ᶠ[𝓝 y]
        (fun z => -(show TangentSpace I z from (B.inv (z, pt)).snd)) := by
    filter_upwards [hSopen.mem_nhds hyS] with z hz
    simpa only [B, S] using
      grad_half_inv (I := I) hb k hcomplete hconn x hq he hf
        hρ hρq hρmetric hρexp hz
  have hgrad_total :
      (T% (fun z => gradientFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) z)) =ᶠ[𝓝 y]
        (T% (fun z => -(show TangentSpace I z from (B.inv (z, pt)).snd))) := by
    filter_upwards [hgrad] with z hz
    change TotalSpace.mk' E z
        (gradientFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) z) =
      TotalSpace.mk' E z
        (-(show TangentSpace I z from (B.inv (z, pt)).snd))
    rw [hz]
  have hgrad_at := hneg_at.congr_of_eventuallyEq hgrad_total
  have hcov :
      (LeviCivita (I := I) (X.obj k).metric).toFun
          (fun z => gradientFun (I := I) (X.obj k).metric
            (CenterOfMass.halfSqDist pt) z) y =
        (LeviCivita (I := I) (X.obj k).metric).toFun
          (fun z => -(show TangentSpace I z from (B.inv (z, pt)).snd)) y :=
    (LeviCivita (I := I) (X.obj k).metric).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_at hneg_at Filter.univ_mem hgrad
  have hgradient_eq :
      (fun z => gradFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) z) =
        fun z => gradientFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) z := by
    funext z
    exact (gradient_eq_gradFun (I := I) (X.obj k).metric
      (CenterOfMass.halfSqDist pt) z).symm
  rw [hessFun_eq_cov_local (I := I) (X.obj k).metric hSopen hsmooth hyS v w,
    hgradient_eq, hcov]

end IsNormalDiag

end HCGCompactness
end DifferentialGeometry
