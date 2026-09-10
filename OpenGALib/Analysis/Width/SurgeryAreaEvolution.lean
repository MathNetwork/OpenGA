import OpenGALib.Analysis.Width.AreaEvolution
import OpenGALib.ComparisonGeometry.MeasuredSurgery

/-!
# Surgery comparison from area evolution

The uniform area derivative estimates replace the already-integrated width
comparison field. All radial volume, scalar, and jump conditions are retained.
Constructing these profiles from a geometric surgery flow remains open.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace OpenGA

structure SurgeryAreaEvolutionData (initialWidth finalTime : ℝ) where
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
  area_evolution : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Ico a b, Nonempty (WidthAreaEvolutionData (width a) t (scalar a t))
  scalar_jump : ∀ a b c,
    EventFreeInterval volumeControl.events finalTime a b →
    EventFreeInterval volumeControl.events finalTime b c → scalar a b ≤ scalar b b
  width_jump : ∀ a b c,
    EventFreeInterval volumeControl.events finalTime a b →
    EventFreeInterval volumeControl.events finalTime b c → width b b ≤ width a b


noncomputable def SurgeryAreaEvolutionData.toMeasured {W T : ℝ}
    (D : SurgeryAreaEvolutionData W T) : MeasuredSurgeryComparisonData W T where
  volumeControl := D.volumeControl
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
  scalar_jump := D.scalar_jump
  width_jump := D.width_jump
  comparison := by
    intro a b hab t ht
    obtain ⟨A⟩ := D.area_evolution a b hab t ht
    exact nonempty_widthComparisonData_of_areaEvolution A

theorem nonempty_measuredSurgeryComparisonData_of_areaEvolution {W T : ℝ}
    (D : SurgeryAreaEvolutionData W T) : Nonempty (MeasuredSurgeryComparisonData W T) :=
  ⟨D.toMeasured⟩

end OpenGA
