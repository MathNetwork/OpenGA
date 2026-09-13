import Definitions.Def_OpenGA_MeasuredReferenceBall
import Definitions.Def_OpenGA_SurgeryComparisonProcess
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace OpenGA

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


end OpenGA
