import Definitions.Def_OpenGA_GeodesicBall
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology

namespace OpenGA

/-- **Math.** A finite positive-radius reference ball for an open-positive measure.
The measure is abstract: identifying it with Riemannian volume is an obligation
of the geometric application. No claim of a Ricci flow is encoded here. -/
structure MeasuredReferenceBall where
  Carrier : Type
  [topology : TopologicalSpace Carrier]
  [measurable : MeasurableSpace Carrier]
  [chart : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Carrier]
  [smooth : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [sigmaCompact : SigmaCompactSpace Carrier]
  metric : Riemannian.RiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) Carrier
  measure : Measure Carrier
  open_pos : ∀ s : Set Carrier, IsOpen s → s.Nonempty → 0 < measure s
  center : Carrier
  radius : ℝ
  radius_pos : 0 < radius
  measure_lt_top : measure (metric.geodesicBall center radius) < ⊤
  modelVolume : ℝ
  modelVolume_pos : 0 < modelVolume

attribute [instance] MeasuredReferenceBall.topology MeasuredReferenceBall.measurable
  MeasuredReferenceBall.chart MeasuredReferenceBall.smooth MeasuredReferenceBall.hausdorff
  MeasuredReferenceBall.sigmaCompact

noncomputable def MeasuredReferenceBall.anchor (B : MeasuredReferenceBall) : ℝ :=
  (B.measure (B.metric.geodesicBall B.center B.radius)).toReal / B.modelVolume

end OpenGA
