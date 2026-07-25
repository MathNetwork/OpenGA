import DifferentialGeometry.Geometry.Coordinates.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Connection.LeviCivita.MetricKoszul
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Metric.BumpExtend
import DifferentialGeometry.Geometry.Metric.MetricExistence
import DifferentialGeometry.Geometry.Metric.PullbackCross

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



def normalBall (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Opens E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x), Metric.isOpen_ball⟩



noncomputable def normalExpPD
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    PartialDiffeomorph 𝓘(Real, E) I E Y.M (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let Φ := expMapDiffeo (I := I) Y.metric x
  let U : Opens E := normalBall (I := I) Y x
  have hU : (U : Set E) ⊆ Φ.source := by
    intro v hv
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
      (by simpa [U, normalBall, Metric.mem_ball, dist_zero_right] using hv)
  have himage : (Φ : E → Y.M) '' (U : Set E) =
      (fun v : E ↦
        (expMap (I := I) Y.metric x (show TangentSpace I x from v) : Y.M)) ''
        (U : Set E) := by
    apply image_congr
    intro v hv
    exact expMapDiffeo_apply_eq (I := I) Y.metric x (hU hv)
  exact
    { toPartialEquiv :=
        { toFun := Φ
          invFun := normalChartAt (I := I) Y.metric x
          source := U
          target := (Φ : E → Y.M) '' (U : Set E)
          map_source' := by
            intro v hv
            exact ⟨v, hv, rfl⟩
          map_target' := by
            rintro q ⟨v, hv, rfl⟩
            have hleft : normalChartAt (I := I) Y.metric x ((Φ : E → Y.M) v) = v :=
              Φ.left_inv' (hU hv)
            rw [hleft]
            exact hv
          left_inv' := by
            intro v hv
            exact Φ.left_inv' (hU hv)
          right_inv' := by
            rintro q ⟨v, hv, rfl⟩
            have hleft : normalChartAt (I := I) Y.metric x ((Φ : E → Y.M) v) = v :=
              Φ.left_inv' (hU hv)
            rw [hleft] }
      open_source := U.2
      open_target := image_opens_isOpen Φ hU
      contMDiffOn_toFun := by
        simpa only [Φ, U, normalBall] using
          expMapDiffeo_contMDiffOn_expBall (I := I) Y x
      contMDiffOn_invFun := by
        have hsm := normalChartAt_contMDiffOn_infty (I := I) Y.metric x
        have hsm' : ContMDiffOn I 𝓘(Real, E) ∞
            (normalChartAt (I := I) Y.metric x) ((Φ : E → Y.M) '' (U : Set E)) := by
          rw [himage]
          simpa only [U, normalBall] using hsm
        exact hsm' }

@[simp]
theorem normalExpPD_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalExpPD (I := I) Y x).source = normalBall (I := I) Y x := by
  rfl



def normalImage
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
      (normalBall (I := I) Y x : Set E),
    image_opens_isOpen (normalExpPD (I := I) Y x) (by simp)⟩



noncomputable def normalBallDiffeo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Diffeomorph 𝓘(Real, E) I (normalBall (I := I) Y x)
      (normalImage (I := I) Y x)
      (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simpa only [normalImage] using
    PartialDiffeomorph.toOpensDiffeoCross (normalExpPD (I := I) Y x) (by simp)

@[implicit_reducible] private noncomputable def normalBallSigma
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SigmaCompactSpace (normalBall (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : LocallyCompactSpace (normalBall (I := I) Y x) :=
    (normalBall (I := I) Y x).2.locallyCompactSpace
  infer_instance

@[implicit_reducible] private noncomputable def normalImageSigma
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SigmaCompactSpace (normalImage (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (normalBallDiffeo (I := I) Y x :
      normalBall (I := I) Y x → normalImage (I := I) Y x) = Set.univ :=
    Set.range_eq_univ.mpr (normalBallDiffeo (I := I) Y x).surjective
  rw [← hrange]
  exact isSigmaCompact_range (normalBallDiffeo (I := I) Y x).continuous

private theorem ballDiffeo_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ((normalBallDiffeo (I := I) Y x z : normalImage (I := I) Y x) : Y.M) =
      expMapDiffeo (I := I) Y.metric x (z : E) := by
  rfl

private theorem ballDiffeo_mfd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalBall (I := I) Y x) (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    mfderiv 𝓘(Real, E) I
        (normalBallDiffeo (I := I) Y x :
          normalBall (I := I) Y x → normalImage (I := I) Y x) z v =
      mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (z : E) v := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have h := PartialDiffeomorph.opensDiffeo_mfd
    (normalExpPD (I := I) Y x) (by simp) z v
  simpa only [normalBallDiffeo, normalExpPD] using h



noncomputable def normalMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SmoothRiemannianMetric 𝓘(Real, E) (normalBall (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  letI : SigmaCompactSpace (normalImage (I := I) Y x) :=
    normalImageSigma (I := I) Y x
  exact Diffeomorph.pullbackMetricCross
    (Y.metric.restrictOpen (I := I) (normalImage (I := I) Y x))
    (normalBallDiffeo (I := I) Y x)



theorem normalMetric_inner
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalBall (I := I) Y x) (v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalMetric (I := I) Y x).inner z v w =
      normalCoordMetric (I := I) Y x z v w := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  letI : SigmaCompactSpace (normalImage (I := I) Y x) :=
    normalImageSigma (I := I) Y x
  rw [normalMetric, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [ballDiffeo_apply, ballDiffeo_mfd, ballDiffeo_mfd]
  exact (normalCoordMetric_apply (I := I) Y x (z : E) v w).symm



noncomputable def normalCut
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffBump (0 : E) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let R := expMapC2Radius (I := I) Y.metric x
  have hR : 0 < R := expMapC2Radius_pos (I := I) Y.metric x
  exact ⟨R / 4, R / 2, by positivity, by linarith⟩


theorem normalCut_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ (normalCut (I := I) Y x : E → Real) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (normalCut (I := I) Y x).contDiff.contMDiff


theorem normalCut_range
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (z : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalCut (I := I) Y x : E → Real) z ∈ Set.Icc (0 : Real) 1 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨(normalCut (I := I) Y x).nonneg, (normalCut (I := I) Y x).le_one⟩



theorem normalCut_supp
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    tsupport (normalCut (I := I) Y x : E → Real) ⊆
      (normalBall (I := I) Y x : Set E) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [(normalCut (I := I) Y x).tsupport_eq]
  change Metric.closedBall (0 : E) (expMapC2Radius (I := I) Y.metric x / 2) ⊆
    Metric.ball 0 (expMapC2Radius (I := I) Y.metric x)
  exact Metric.closedBall_subset_ball (by
    have hR := expMapC2Radius_pos (I := I) Y.metric x
    linarith)


theorem normalCut_one
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ {z : E}, z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
      (normalCut (I := I) Y x : E → Real) z = 1 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  apply (normalCut (I := I) Y x).one_of_mem_closedBall
  exact Metric.ball_subset_closedBall hz


theorem normalInner_sub
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x / 4) ⊆
      (normalBall (I := I) Y x : Set E) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  change Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x / 4) ⊆
    Metric.ball 0 (expMapC2Radius (I := I) Y.metric x)
  exact Metric.ball_subset_ball (by
    have hR := expMapC2Radius_pos (I := I) Y.metric x
    linarith)



private noncomputable def modelFlatMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    SmoothRiemannianMetric 𝓘(Real, E) E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  let B : E →L[Real] E →L[Real] Real := normalCoordMetric (I := I) Y x 0
  have hBsymm : ∀ v w : E, B v w = B w v := by
    intro v w
    dsimp only [B]
    rw [normalMetric_zero (I := I)]
    exact Y.metric.symm x v w
  have hBpos : ∀ v : E, v ≠ 0 → 0 < B v v := by
    intro v hv
    dsimp only [B]
    rw [normalMetric_zero (I := I)]
    exact Y.metric.pos x v hv
  exact
    { inner := fun _ ↦ B
      symm := fun _ ↦ hBsymm
      pos := fun _ ↦ hBpos
      isVonNBounded := fun _ ↦
        DifferentialGeometry.Geometry.posDef_isVonNBounded
          B hBpos
      contMDiff := by
        intro y
        rw [contMDiffAt_section]
        convert contMDiffAt_const (I := 𝓘(Real, E))
          (I' := 𝓘(Real, E →L[Real] E →L[Real] Real))
          (x := y) (c := B)
        ext v w
        rw [DifferentialGeometry.Geometry.metricCoeffInModel_apply
          (I := 𝓘(Real, E)) y (by simp) B v w]
        rw [TangentBundle.symmL_model_space]
        rfl }

noncomputable def normalTotal
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SmoothRiemannianMetric 𝓘(Real, E) E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  exact (modelFlatMetric (I := I) Y x).bumpExtendOpen
    (normalBall (I := I) Y x) (normalMetric (I := I) Y x)
    (normalCut (I := I) Y x : E → Real)
    (normalCut_smooth (I := I) Y x) (normalCut_range (I := I) Y x)
    (normalCut_supp (I := I) Y x)



theorem normalTotal_inner
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) → ∀ v w : E,
      (normalTotal (I := I) Y x).inner z v w =
        normalCoordMetric (I := I) Y x z v w := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  letI : SigmaCompactSpace (normalImage (I := I) Y x) :=
    normalImageSigma (I := I) Y x
  intro z hz v w
  have hsub := normalInner_sub (I := I) Y x
  calc
    (normalTotal (I := I) Y x).inner z v w =
        (normalMetric (I := I) Y x).inner ⟨z, hsub hz⟩ v w := by
      simpa only [normalTotal] using
        bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
          (modelFlatMetric (I := I) Y x) (normalBall (I := I) Y x)
          (normalMetric (I := I) Y x) (normalCut (I := I) Y x : E → Real)
          (normalCut_smooth (I := I) Y x) (normalCut_range (I := I) Y x)
          (normalCut_supp (I := I) Y x)
          (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x / 4))
          (fun q hq ↦ normalCut_one (I := I) Y x hq) hsub z hz v w
    _ = normalCoordMetric (I := I) Y x z v w :=
      normalMetric_inner (I := I) Y x ⟨z, hsub hz⟩ v w


theorem normalTotal_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
      (normalTotal (I := I) Y x).inner z = normalCoordMetric (I := I) Y x z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact normalTotal_inner (I := I) Y x z hz v w



theorem normal_cov_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
    ∀ (hco : IsCoercive (normalCoordMetric (I := I) Y x z)) (v w : E),
    (Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
        (normalTotal (I := I) Y x) (fun _ : E ↦ w) z) v =
      MetricKoszul.koszulVec hco
        (fderiv Real (normalCoordMetric (I := I) Y x) z) v w := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz hco v w
  have hsub := normalInner_sub (I := I) Y x
  have hB : (fun y : E ↦ (normalTotal (I := I) Y x).inner y) =ᶠ[nhds z]
      normalCoordMetric (I := I) Y x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact normalTotal_eq (I := I) Y x y hy
  have hdiff : DifferentiableAt Real (normalCoordMetric (I := I) Y x) z := by
    exact ((normalCoordMetric_contDiffOn_expBall (I := I) Y x).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact Integral.Connection.const_cov_eq_nhds
    (normalTotal (I := I) Y x) (normalCoordMetric (I := I) Y x)
    hB hdiff hco v w




theorem normal_cov_eq_fderiv
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
    ∀ (hco : IsCoercive (normalCoordMetric (I := I) Y x z))
      (V : E → E)
      (_hV : MDifferentiableAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, E))
        (fun y : E ↦ (⟨y, V y⟩ : TangentBundle 𝓘(Real, E) E)) z)
      (v : E),
    (Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
        (normalTotal (I := I) Y x) V z) v =
      fderiv Real V z v +
        MetricKoszul.koszulVec hco
          (fderiv Real (normalCoordMetric (I := I) Y x) z) v (V z) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz hco V _hV v
  have hsub := normalInner_sub (I := I) Y x
  have hB : (fun y : E ↦ (normalTotal (I := I) Y x).inner y) =ᶠ[nhds z]
      normalCoordMetric (I := I) Y x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact normalTotal_eq (I := I) Y x y hy
  have hdiff : DifferentiableAt Real (normalCoordMetric (I := I) Y x) z := by
    exact ((normalCoordMetric_contDiffOn_expBall (I := I) Y x).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact Integral.Connection.cov_eq_fderiv_add
    (normalTotal (I := I) Y x) (normalCoordMetric (I := I) Y x)
    hB hdiff hco V _hV v

end HCGCompactness
end DifferentialGeometry
