import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition

set_option autoImplicit false










noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



theorem normalOverlap_of_map
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hUx :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x))
    (hVy :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      V ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) Y.metric x z) U
        ((fun v : E =>
          (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M)) '' V)) :
    NormalOverlapOn (I := I) Y x y U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  have hzx : z ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x (by
      simpa only [Metric.mem_ball, dist_zero_right] using hUx hz)
  refine ⟨hzx, ?_⟩
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  change (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M) =
    expMapDiffeo (I := I) Y.metric x z at hvz
  have hvy : v ∈ (expMapDiffeo (I := I) Y.metric y).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric y (by
      simpa only [Metric.mem_ball, dist_zero_right] using hVy hv)
  rw [normalChartAt_source_eq]
  rw [← hvz, ← expMapDiffeo_apply_eq (I := I) Y.metric y hvy]
  exact (expMapDiffeo (I := I) Y.metric y).map_source hvy



theorem normalTrans_mapsTo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hVy :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      V ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) Y.metric x z) U
        ((fun v : E =>
          (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M)) '' V)) :
    Set.MapsTo (normalTransition (I := I) Y x y) U V := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  obtain ⟨v, hv, hvz⟩ := hmaps hz
  change (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M) =
    expMapDiffeo (I := I) Y.metric x z at hvz
  have hvy : v ∈ (normalChartAt (I := I) Y.metric y).target :=
    ball_subset_normalChartAt_target (I := I) Y.metric y (by
      simpa only [Metric.mem_ball, dist_zero_right] using hVy hv)
  change normalChartAt (I := I) Y.metric y
      (expMapDiffeo (I := I) Y.metric x z) ∈ V
  rw [← hvz, ← normalChartAt_symm_apply (I := I) Y.metric y hvy]
  rw [normalChartAt_right_inv (I := I) Y.metric y hvy]
  exact hv



omit [NeZero (Module.finrank Real E)] in
theorem NormalOverlapOn.decode
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x y : Y.M}
    {U : Set E} (h : NormalOverlapOn (I := I) Y x y U)
    {z : E} (hz : z ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalChartAt (I := I) Y.metric y).symm
        (normalTransition (I := I) Y x y z) =
      (normalChartAt (I := I) Y.metric x).symm z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨_hzx, hzy⟩ := h z hz
  change (normalChartAt (I := I) Y.metric x).symm z ∈
    (normalChartAt (I := I) Y.metric y).source at hzy
  change (normalChartAt (I := I) Y.metric y).symm
      (normalChartAt (I := I) Y.metric y
        ((normalChartAt (I := I) Y.metric x).symm z)) =
    (normalChartAt (I := I) Y.metric x).symm z
  exact normalChartAt_left_inv (I := I) Y.metric y hzy



omit [NeZero (Module.finrank Real E)] in
theorem NormalOverlapOn.cancel
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x y : Y.M}
    {U : Set E} (h : NormalOverlapOn (I := I) Y x y U)
    {z : E} (hz : z ∈ U) :
    normalTransition (I := I) Y y x
        (normalTransition (I := I) Y x y z) = z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨hzx, hzy⟩ := h z hz
  change (normalChartAt (I := I) Y.metric x).symm z ∈
    (normalChartAt (I := I) Y.metric y).source at hzy
  have hzt : z ∈ (normalChartAt (I := I) Y.metric x).target := by
    rwa [normalChartAt_target_eq]
  change normalChartAt (I := I) Y.metric x
      ((normalChartAt (I := I) Y.metric y).symm
        (normalChartAt (I := I) Y.metric y
          ((normalChartAt (I := I) Y.metric x).symm z))) = z
  rw [normalChartAt_left_inv (I := I) Y.metric y hzy]
  exact normalChartAt_right_inv (I := I) Y.metric x hzt

end HCGCompactness
end DifferentialGeometry
