import OpenGALib.Analysis.SurgeryComparison
import OpenGALib.ComparisonGeometry.BallMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

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

structure MeasuredRadialSurgeryData where
  events : Set ℝ
  modelParameter : ℝ
  modelParameter_nonneg : 0 ≤ modelParameter
  referenceRadius : ℝ
  removalRadius : ℝ
  removalRadius_pos : 0 < removalRadius
  radius_le : removalRadius ≤ referenceRadius
  referenceBall : MeasuredReferenceBall
  totalBudget : ℝ
  density : ℝ → ℝ → ℝ≥0∞
  density_measurable : ∀ t ∈ events,
    AEMeasurable (density t) (volume.restrict (Ioc 0 referenceRadius))
  density_comparison : ∀ t ∈ events, CrossAnti referenceRadius (density t)
    (fun r => ENNReal.ofReal (hypDensity modelParameter 2 r))
  reference_lower : ∀ t ∈ events, ENNReal.ofReal referenceBall.anchor ≤
    (∫⁻ r in Ioc (0 : ℝ) referenceRadius, density t r) /
      ENNReal.ofReal (hypRadVol modelParameter 2 referenceRadius)
  removedVolume : ℝ → ℝ
  removedVolume_nonneg : ∀ t ∈ events, 0 ≤ removedVolume t
  removal_contains : ∀ t ∈ events,
    (∫⁻ r in Ioc (0 : ℝ) removalRadius, density t r) ≤ ENNReal.ofReal (removedVolume t)
  volume_budget : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ events →
    ∑ t ∈ s, removedVolume t ≤ totalBudget


structure MeasuredSurgeryComparisonData (initialWidth finalTime : ℝ) where
  volumeControl : MeasuredRadialSurgeryData
  events_inside : volumeControl.events ⊆ Ioo 0 finalTime
  finalTime_pos : 0 < finalTime
  scalar : ℝ → ℝ → ℝ
  width : ℝ → ℝ → ℝ
  scalar_cont : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ContinuousOn (scalar a) (Icc a b)
  width_cont : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ContinuousOn (width a) (Icc a b)
  scalar_initial : -6 ≤ scalar 0 0
  width_initial : width 0 0 ≤ initialWidth
  width_nonneg : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Icc a b, 0 ≤ width a t
  scalar_slope : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Ico a b, ∀ q : ℝ, q < (2 / 3 : ℝ) * (scalar a t) ^ 2 →
      ∀ᶠ s in 𝓝[>] t, q < slope (scalar a) t s
  comparison : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Ico a b, Nonempty (WidthComparisonData (width a) t (scalar a t))
  scalar_jump : ∀ a b c,
    EventFreeInterval volumeControl.events finalTime a b →
    EventFreeInterval volumeControl.events finalTime b c → scalar a b ≤ scalar b b
  width_jump : ∀ a b c,
    EventFreeInterval volumeControl.events finalTime a b →
    EventFreeInterval volumeControl.events finalTime b c → width b b ≤ width a b


/-- **Math.** The reference ball supplies a positive real anchor; finite measure is
needed when passing from extended nonnegative values to real values. -/
theorem MeasuredReferenceBall.anchor_pos (B : MeasuredReferenceBall) : 0 < B.anchor := by
  apply div_pos _ B.modelVolume_pos
  apply ENNReal.toReal_pos_iff.mpr
  exact ⟨B.metric.measure_geodesicBall_pos B.center B.open_pos
    (B.metric.isOpen_geodesicBall B.center B.radius) B.radius_pos, B.measure_lt_top⟩

/-- **Math.** Construct the existing budget, deriving its anchor positivity from the
reference ball while preserving the uniform comparison and loss assumptions. -/
noncomputable def MeasuredRadialSurgeryData.toBudget (D : MeasuredRadialSurgeryData) :
    RadialSurgeryVolumeBudget where
  events := D.events
  modelParameter := D.modelParameter
  modelParameter_nonneg := D.modelParameter_nonneg
  referenceRadius := D.referenceRadius
  removalRadius := D.removalRadius
  removalRadius_pos := D.removalRadius_pos
  radius_le := D.radius_le
  anchor := D.referenceBall.anchor
  anchor_pos := D.referenceBall.anchor_pos
  totalBudget := D.totalBudget
  density := D.density
  density_measurable := D.density_measurable
  density_comparison := D.density_comparison
  reference_lower := D.reference_lower
  removedVolume := D.removedVolume
  removedVolume_nonneg := D.removedVolume_nonneg
  removal_contains := D.removal_contains
  volume_budget := D.volume_budget

/-- **Math.** The measured data construct a process of the original type. No new
assumptions are added to the target process or the Poincare goal. -/
noncomputable def MeasuredSurgeryComparisonData.toProcess {W T : ℝ}
    (D : MeasuredSurgeryComparisonData W T) : SurgeryComparisonProcess W T where
  volumeControl := D.volumeControl.toBudget
  events_inside := D.events_inside
  finalTime_pos := D.finalTime_pos
  scalar := D.scalar
  width := D.width
  scalar_cont := D.scalar_cont
  width_cont := D.width_cont
  scalar_initial := D.scalar_initial
  width_initial := D.width_initial
  width_nonneg := D.width_nonneg
  scalar_slope := D.scalar_slope
  comparison := D.comparison
  scalar_jump := D.scalar_jump
  width_jump := D.width_jump

theorem nonempty_surgeryComparisonProcess_of_measuredData {W T : ℝ}
    (D : MeasuredSurgeryComparisonData W T) : Nonempty (SurgeryComparisonProcess W T) :=
  ⟨D.toProcess⟩

end OpenGA
