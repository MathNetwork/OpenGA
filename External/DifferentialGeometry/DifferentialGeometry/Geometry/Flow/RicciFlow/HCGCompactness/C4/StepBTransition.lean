import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalizedAA
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.H6IsometryDeriv

set_option autoImplicit false







































namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]










theorem exists_transitionLimit_on
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (J : ℕ → E → E) (Jbar : ℕ → E → E)
    (hJ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (J k) U)
    (hJbar : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Jbar k) V)
    (hbJ : IsometryDerivBoundsOn U J) (hbJbar : IsometryDerivBoundsOn V Jbar)
    (hLeft : ∀ k, ∀ x ∈ U, Jbar k (J k x) = x) (hRight : ∀ k, ∀ y ∈ V, J k (Jbar k y) = y) :
    ∃ (φ : ℕ → ℕ) (Jinf : E → E) (Jbarinf : E → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jinf U ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jbarinf V ∧
        MapCInfConvOnCompacts U (fun k => J (φ k)) Jinf ∧
        MapCInfConvOnCompacts V (fun k => Jbar (φ k)) Jbarinf ∧
        (∀ x ∈ U, Jinf x ∈ V → Jbarinf (Jinf x) = x) ∧
        (∀ y ∈ V, Jbarinf y ∈ U → Jinf (Jbarinf y) = y) :=
  isometry_seq_diffeo_on hU hV J Jbar hJ hJbar hbJ hbJbar hLeft hRight



section HCGNormalTransition

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



def NormalOverlapOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M) (U : Set E) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  forall z : E, z ∈ U ->
    z ∈ (expMapDiffeo (I := I) Y.metric x).source ∧
      expMapDiffeo (I := I) Y.metric x z ∈ (normalChartAt (I := I) Y.metric y).source








theorem contDiffOn_normalTransition
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M) {U : Set E}
    (hUx :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x))
    (hmaps :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) Y.metric x z) U
        ((fun v : E => (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M)) ''
          Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (normalTransition (I := I) Y x y) U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [← contMDiffOn_iff_contDiffOn]
  have hexp : ContMDiffOn 𝓘(ℝ, E) I ∞ (fun z => expMapDiffeo (I := I) Y.metric x z) U :=
    (expMapDiffeo_contMDiffOn_expBall (I := I) Y x).mono hUx
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) Y.metric y)
      ((fun v : E => (expMap (I := I) Y.metric y (show TangentSpace I y from v) : Y.M)) ''
        Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y)) :=
    normalChartAt_contMDiffOn_infty (I := I) Y.metric y
  exact hchart.comp hexp hmaps








theorem exists_trans_h6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : ∀ k : ℕ, (X.obj k).M)
    {U V Ua Va : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hUa : IsOpen Ua) (hVa : IsOpen Va)
    (hUanorm : ∃ Z : Real, ∀ z ∈ Ua, ‖z‖ ≤ Z)
    (hVanorm : ∃ Z : Real, ∀ z ∈ Va, ‖z‖ ≤ Z)
    (hUmetric : ∀ k, U ⊆ Metric.ball (0 : E) (metricInput.radius k (x k)))
    (hVmetric : ∀ k, V ⊆ Metric.ball (0 : E) (metricInput.radius k (y k)))
    (hUametric : ∀ k, Ua ⊆ Metric.ball (0 : E) (metricInput.radius k (x k)))
    (hVametric : ∀ k, Va ⊆ Metric.ball (0 : E) (metricInput.radius k (y k)))
    (hUexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x k)))
    (hVexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      V ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y k)))
    (hUaexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Ua ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x k)))
    (hVaexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Va ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y k)))
    (hJ : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (x k) (y k)) U)
    (hJbar : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (y k) (x k)) V)
    (hovlJ : ∀ k, NormalOverlapOn (I := I) (X.obj k) (x k) (y k) U)
    (hovlJbar : ∀ k, NormalOverlapOn (I := I) (X.obj k) (y k) (x k) V)
    (hmapJ : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (x k) (y k)) U Va)
    (hmapJbar : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (y k) (x k)) V Ua)
    (hLeft : ∀ k, ∀ z ∈ U,
      normalTransition (I := I) (X.obj k) (y k) (x k)
        (normalTransition (I := I) (X.obj k) (x k) (y k) z) = z)
    (hRight : ∀ k, ∀ w ∈ V,
      normalTransition (I := I) (X.obj k) (x k) (y k)
        (normalTransition (I := I) (X.obj k) (y k) (x k) w) = w) :
    ∃ (φ : ℕ → ℕ) (Jinf : E → E) (Jbarinf : E → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jinf U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) Jbarinf V ∧
        MapCInfConvOnCompacts U
          (fun k => normalTransition (I := I) (X.obj (φ k)) (x (φ k)) (y (φ k))) Jinf ∧
        MapCInfConvOnCompacts V
          (fun k => normalTransition (I := I) (X.obj (φ k)) (y (φ k)) (x (φ k))) Jbarinf ∧
        (∀ z ∈ U, Jinf z ∈ V → Jbarinf (Jinf z) = z) ∧
        (∀ w ∈ V, Jbarinf w ∈ U → Jinf (Jbarinf w) = w) := by
  apply exists_transitionLimit_on hU hV
    (fun k => normalTransition (I := I) (X.obj k) (x k) (y k))
    (fun k => normalTransition (I := I) (X.obj k) (y k) (x k))
    hJ hJbar
  · exact H6Isometry.normal_bounds_on (I := I) X metricInput x y U Va hU hVa
      hVanorm hUmetric hVametric hUexp hVaexp hJ hovlJ hmapJ
  · exact H6Isometry.normal_bounds_on (I := I) X metricInput y x V Ua hV hUa
      hUanorm hVmetric hUametric hVexp hUaexp hJbar hovlJbar hmapJbar
  · exact hLeft
  · exact hRight

end HCGNormalTransition

end HCGCompactness
end DifferentialGeometry
