import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalMetricExtend
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype
import DifferentialGeometry.Geometry.Geodesic.PullbackCross

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



def normalQuarter
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Opens E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨Metric.ball (0 : E)
    (expMapC2Radius (I := I) Y.metric x / 4), Metric.isOpen_ball⟩



theorem normalQuarter_sub
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalQuarter (I := I) Y x : Set E) ⊆
      (normalExpPD (I := I) Y x).source := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [normalExpPD_source]
  exact normalInner_sub (I := I) Y x


def normalQuarterImage
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Opens Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨(normalExpPD (I := I) Y x : E → Y.M) ''
      (normalQuarter (I := I) Y x : Set E),
    image_opens_isOpen (normalExpPD (I := I) Y x)
      (normalQuarter_sub (I := I) Y x)⟩



noncomputable def normalQuarterDiffeo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Diffeomorph 𝓘(Real, E) I (normalQuarter (I := I) Y x)
      (normalQuarterImage (I := I) Y x) (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simpa only [normalQuarterImage] using
    PartialDiffeomorph.toOpensDiffeoCross (normalExpPD (I := I) Y x)
      (normalQuarter_sub (I := I) Y x)



@[implicit_reducible] noncomputable def normalQuarterSigma
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SigmaCompactSpace (normalQuarter (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : LocallyCompactSpace (normalQuarter (I := I) Y x) :=
    (normalQuarter (I := I) Y x).2.locallyCompactSpace
  infer_instance


@[implicit_reducible] noncomputable def normalQuarterImageSigma
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SigmaCompactSpace (normalQuarterImage (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (normalQuarterDiffeo (I := I) Y x :
      normalQuarter (I := I) Y x → normalQuarterImage (I := I) Y x) =
      Set.univ := Set.range_eq_univ.mpr
        (normalQuarterDiffeo (I := I) Y x).surjective
  rw [← hrange]
  exact isSigmaCompact_range (normalQuarterDiffeo (I := I) Y x).continuous



theorem quarterDiffeo_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalQuarter (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ((normalQuarterDiffeo (I := I) Y x z :
      normalQuarterImage (I := I) Y x) : Y.M) =
      expMapDiffeo (I := I) Y.metric x (z : E) := by
  rfl



theorem quarterDiffeo_mfd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalQuarter (I := I) Y x) (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    mfderiv 𝓘(Real, E) I
        (normalQuarterDiffeo (I := I) Y x :
          normalQuarter (I := I) Y x → normalQuarterImage (I := I) Y x) z v =
      mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (z : E) v := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have h := PartialDiffeomorph.opensDiffeo_mfd
    (normalExpPD (I := I) Y x) (normalQuarter_sub (I := I) Y x) z v
  simpa only [normalQuarterDiffeo, normalExpPD] using h

omit [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)] in
private theorem metric_ext
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(Real, E) ∞ M]
    {g g' : SmoothRiemannianMetric 𝓘(Real, E) M}
    (h : ∀ (z : M) (v w : TangentSpace 𝓘(Real, E) z),
      g.inner z v w = g'.inner z v w) : g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun z => ContinuousLinearMap.ext fun v =>
      ContinuousLinearMap.ext fun w => h z v w
  subst hi
  rfl



theorem normalTotal_quarter
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
      normalQuarterSigma (I := I) Y x
    letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
      normalQuarterImageSigma (I := I) Y x
    (normalTotal (I := I) Y x).restrictOpen (I := 𝓘(Real, E))
        (normalQuarter (I := I) Y x) =
      Diffeomorph.pullbackMetricCross
        (Y.metric.restrictOpen (I := I) (normalQuarterImage (I := I) Y x))
        (normalQuarterDiffeo (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
    normalQuarterImageSigma (I := I) Y x
  apply metric_ext (M := normalQuarter (I := I) Y x)
  intro z v w
  rw [SmoothRiemannianMetric.restrictOpen_inner,
    Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [quarterDiffeo_apply, quarterDiffeo_mfd, quarterDiffeo_mfd]
  rw [normalTotal_inner (I := I) Y x (z : E) z.2 v w]
  exact normalCoordMetric_apply (I := I) Y x (z : E) v w




theorem normal_cov_map
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
      normalQuarterSigma (I := I) Y x
    letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
      normalQuarterImageSigma (I := I) Y x
    ∀ (V : ContMDiffSection 𝓘(Real, E) E (∞ : WithTop ℕ∞)
          (TangentSpace 𝓘(Real, E) : E → Type _))
      (Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : Y.M → Type _))
      (z : normalQuarter (I := I) Y x) (v : E),
    (fun y : normalQuarterImage (I := I) Y x =>
        Integral.Connection.restrictOpenTangentSection (I := I)
          (normalQuarterImage (I := I) Y x) Z y) =ᶠ[
      nhds (normalQuarterDiffeo (I := I) Y x z)]
      (fun y : normalQuarterImage (I := I) Y x =>
        Integral.Connection.pushFwdSectionCross
          (I := 𝓘(Real, E)) (J := I)
          (normalQuarterDiffeo (I := I) Y x)
          (Integral.Connection.restrictOpenTangentSection
            (I := 𝓘(Real, E)) (normalQuarter (I := I) Y x) V) y) →
    mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (z : E)
        (((Integral.Connection.metricCov (I := 𝓘(Real, E))
          (M := E) (normalTotal (I := I) Y x)).toFun
          (fun u : E => V u) (z : E)) v) =
      ((Integral.Connection.metricCov (I := I) (M := Y.M) Y.metric).toFun
        (fun y : Y.M => Z y)
        (expMapDiffeo (I := I) Y.metric x (z : E)))
        (mfderiv 𝓘(Real, E) I
          (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (z : E) v) := by
  classical
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
    normalQuarterImageSigma (I := I) Y x
  intro V Z z v hEq
  let U := normalQuarter (I := I) Y x
  let W := normalQuarterImage (I := I) Y x
  let Phi := normalQuarterDiffeo (I := I) Y x
  let VU := Integral.Connection.restrictOpenTangentSection
    (I := 𝓘(Real, E)) U V
  let PW := Integral.Connection.pushFwdSectionCross
    (I := 𝓘(Real, E)) (J := I) Phi VU
  have hres := Integral.Connection.metricCov_restrictOpen_globalSection
    (I := 𝓘(Real, E)) (normalTotal (I := I) Y x) U V z v
  rw [normalTotal_quarter (I := I) Y x] at hres
  have hpull := Integral.Connection.metricCov_pullbackCross
    (I := 𝓘(Real, E)) (J := I)
    (Y.metric.restrictOpen (I := I) W) Phi VU z v
  have hfield :
      (Integral.Connection.metricCov (I := I) (M := W)
        (Y.metric.restrictOpen (I := I) W)).toFun
          (Integral.Connection.restrictOpenTangentField (I := I) W
            (fun y : Y.M => Z y)) (Phi z) =
        (Integral.Connection.metricCov (I := I) (M := W)
          (Y.metric.restrictOpen (I := I) W)).toFun
            (fun y : W => PW y) (Phi z) := by
    apply Integral.Connection.metricCov_congr_nhds
      (I := I) (M := W) (Y.metric.restrictOpen (I := I) W)
      (Integral.Connection.mdiffAt_restrictOpen_section (I := I) W Z (Phi z))
      (PW.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    simpa only [Integral.Connection.restrictOpenTangentSection] using hEq
  have htgt := Integral.Connection.metricCov_restrictOpen_globalSection
    (I := I) Y.metric W Z (Phi z)
      (mfderiv 𝓘(Real, E) I (Phi : U → W) z v)
  have htoAmbient :
      ((Integral.Connection.metricCov (I := I) (M := W)
          (Y.metric.restrictOpen (I := I) W)).toFun
        (fun y : W => PW y) (Phi z))
        (mfderiv 𝓘(Real, E) I (Phi : U → W) z v) =
      ((Integral.Connection.metricCov (I := I) (M := Y.M) Y.metric).toFun
        (fun y : Y.M => Z y) (Phi z : Y.M))
        (mfderiv 𝓘(Real, E) I (Phi : U → W) z v) := by
    rw [← hfield]
    exact htgt
  have hpbAmbient := htoAmbient
  rw [← hpull] at hpbAmbient
  have hleft := quarterDiffeo_mfd (I := I) Y x z
    (((Integral.Connection.metricCov (I := 𝓘(Real, E))
      (M := E) (normalTotal (I := I) Y x)).toFun
      (fun u : E => V u) (z : E)) v)
  have hdir := quarterDiffeo_mfd (I := I) Y x z v
  have hbase := quarterDiffeo_apply (I := I) Y x z
  rw [← hleft, ← hres, ← hdir, ← hbase]
  exact hpbAmbient




theorem normalGeo_map
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (gamma : Real → E) (s : Set Real) (hs : IsOpen s)
    (hmem : ∀ t ∈ s, gamma t ∈ (normalQuarter (I := I) Y x : Set E))
    (hgamma : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞ gamma s)
    (hgeo : Geometry.Riemannian.Geodesic.IsGeodesicOn (I := 𝓘(Real, E))
      (normalTotal (I := I) Y x) gamma s) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Geometry.Riemannian.Geodesic.IsGeodesicOn (I := I) Y.metric
      (fun t ↦ expMapDiffeo (I := I) Y.metric x (gamma t)) s := by
  classical
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
    normalQuarterImageSigma (I := I) Y x
  let z0 : normalQuarter (I := I) Y x := ⟨0, by
    change (0 : E) ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4)
    rw [Metric.mem_ball, dist_self]
    exact div_pos (expMapC2Radius_pos (I := I) Y.metric x) (by norm_num)⟩
  let gammaQ : Real → normalQuarter (I := I) Y x := fun t ↦
    if ht : t ∈ s then ⟨gamma t, hmem t ht⟩ else z0
  have hval : ∀ t ∈ s, (gammaQ t : E) = gamma t := by
    intro t ht
    simp only [gammaQ, dif_pos ht]
  have hbaseSmooth : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞
      (fun t ↦ (gammaQ t : E)) s :=
    hgamma.congr hval
  have hqSmooth : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞ gammaQ s := by
    intro t ht
    exact (codRestr_contMDiffAt (I := 𝓘(Real, Real)) (J := 𝓘(Real, E))
      (V := normalQuarter (I := I) Y x) (f := fun r ↦ (gammaQ r : E))
      (fun r ↦ (gammaQ r).2)
      ((hbaseSmooth t ht).contMDiffAt (hs.mem_nhds ht))).contMDiffWithinAt
  have hqGeoAmbient : Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := 𝓘(Real, E)) (normalTotal (I := I) Y x)
      (fun t ↦ (gammaQ t : E)) s := by
    intro t ht
    have hev : (fun r ↦ (gammaQ r : E)) =ᶠ[nhds t] gamma :=
      (Set.EqOn.eventuallyEq_of_mem hval (hs.mem_nhds ht))
    exact Geometry.Riemannian.Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hval t ht) hev (hgeo t ht)
  have hqGeoRestr : Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := 𝓘(Real, E))
      ((normalTotal (I := I) Y x).restrictOpen (I := 𝓘(Real, E))
        (normalQuarter (I := I) Y x)) gammaQ s :=
    (Geometry.Riemannian.Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E)) (normalTotal (I := I) Y x)
      (normalQuarter (I := I) Y x) gammaQ s).2 hqGeoAmbient
  rw [normalTotal_quarter (I := I) Y x] at hqGeoRestr
  have hmapRestr := Geometry.Riemannian.Geodesic.geodesicOn_mapLocal
    (I := 𝓘(Real, E)) (J := I)
    (Y.metric.restrictOpen (I := I) (normalQuarterImage (I := I) Y x))
    (normalQuarterDiffeo (I := I) Y x) gammaQ s hs hqSmooth hqGeoRestr
  have hmapAmbient : Geometry.Riemannian.Geodesic.IsGeodesicOn (I := I)
      Y.metric
      (fun t ↦ ((normalQuarterDiffeo (I := I) Y x (gammaQ t) :
        normalQuarterImage (I := I) Y x) : Y.M)) s :=
    (Geometry.Riemannian.Geodesic.geodesicOn_open_iff (I := I) Y.metric
      (normalQuarterImage (I := I) Y x)
      (fun t ↦ normalQuarterDiffeo (I := I) Y x (gammaQ t)) s).1 hmapRestr
  intro t ht
  have hev : (fun r ↦ expMapDiffeo (I := I) Y.metric x (gamma r)) =ᶠ[nhds t]
      (fun r ↦ ((normalQuarterDiffeo (I := I) Y x (gammaQ r) :
        normalQuarterImage (I := I) Y x) : Y.M)) := by
    filter_upwards [hs.mem_nhds ht] with r hr
    rw [← hval r hr]
    exact (quarterDiffeo_apply (I := I) Y x (gammaQ r)).symm
  exact Geometry.Riemannian.Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    hev.self_of_nhds hev (hmapAmbient t ht)

end HCGCompactness
end DifferentialGeometry
