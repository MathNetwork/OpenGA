import Theorems.Thm_OpenGA_MeasuredReferenceBall_anchor_pos
import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open OpenGA

namespace OpenGA
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


end OpenGA

theorem solution {W T : ℝ} (D : MeasuredSurgeryComparisonData W T) : Nonempty (SurgeryComparisonProcess W T) := ⟨D.toProcess⟩
