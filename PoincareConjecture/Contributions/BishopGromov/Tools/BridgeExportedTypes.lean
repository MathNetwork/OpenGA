import Lean
import Theorems.Thm_OpenGA_RadialSurgeryVolumeBudget_removedVolume_lower
import Theorems.Thm_OpenGA_RadialSurgeryVolumeBudget_events_finite
import Theorems.Thm_OpenGA_exists_event_free_partition
import Theorems.Thm_OpenGA_nonempty_widthComparisonTrace_of_surgeryComparisonProcess
open Lean in
run_meta do
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  for name in [`OpenGA.EventFreeInterval,
    `OpenGA.RadialSurgeryVolumeBudget,
    `OpenGA.RadialSurgeryVolumeBudget.anchor,
    `OpenGA.RadialSurgeryVolumeBudget.anchor_pos,
    `OpenGA.RadialSurgeryVolumeBudget.casesOn,
    `OpenGA.RadialSurgeryVolumeBudget.ctorIdx,
    `OpenGA.RadialSurgeryVolumeBudget.density,
    `OpenGA.RadialSurgeryVolumeBudget.density_comparison,
    `OpenGA.RadialSurgeryVolumeBudget.density_measurable,
    `OpenGA.RadialSurgeryVolumeBudget.events,
    `OpenGA.RadialSurgeryVolumeBudget.events_finite,
    `OpenGA.RadialSurgeryVolumeBudget.mk,
    `OpenGA.RadialSurgeryVolumeBudget.mk.inj,
    `OpenGA.RadialSurgeryVolumeBudget.mk.injEq,
    `OpenGA.RadialSurgeryVolumeBudget.mk.noConfusion,
    `OpenGA.RadialSurgeryVolumeBudget.mk.sizeOf_spec,
    `OpenGA.RadialSurgeryVolumeBudget.modelParameter,
    `OpenGA.RadialSurgeryVolumeBudget.modelParameter_nonneg,
    `OpenGA.RadialSurgeryVolumeBudget.noConfusion,
    `OpenGA.RadialSurgeryVolumeBudget.noConfusionType,
    `OpenGA.RadialSurgeryVolumeBudget.radius_le,
    `OpenGA.RadialSurgeryVolumeBudget.rec,
    `OpenGA.RadialSurgeryVolumeBudget.recOn,
    `OpenGA.RadialSurgeryVolumeBudget.referenceRadius,
    `OpenGA.RadialSurgeryVolumeBudget.reference_lower,
    `OpenGA.RadialSurgeryVolumeBudget.removalRadius,
    `OpenGA.RadialSurgeryVolumeBudget.removalRadius_pos,
    `OpenGA.RadialSurgeryVolumeBudget.removal_contains,
    `OpenGA.RadialSurgeryVolumeBudget.removedVolume,
    `OpenGA.RadialSurgeryVolumeBudget.removedVolume_lower,
    `OpenGA.RadialSurgeryVolumeBudget.removedVolume_nonneg,
    `OpenGA.RadialSurgeryVolumeBudget.totalBudget,
    `OpenGA.RadialSurgeryVolumeBudget.volume_budget,
    `OpenGA.SurgeryComparisonProcess,
    `OpenGA.SurgeryComparisonProcess.casesOn,
    `OpenGA.SurgeryComparisonProcess.comparison,
    `OpenGA.SurgeryComparisonProcess.ctorIdx,
    `OpenGA.SurgeryComparisonProcess.events_inside,
    `OpenGA.SurgeryComparisonProcess.finalTime_pos,
    `OpenGA.SurgeryComparisonProcess.mk,
    `OpenGA.SurgeryComparisonProcess.mk.inj,
    `OpenGA.SurgeryComparisonProcess.mk.injEq,
    `OpenGA.SurgeryComparisonProcess.mk.noConfusion,
    `OpenGA.SurgeryComparisonProcess.mk.sizeOf_spec,
    `OpenGA.SurgeryComparisonProcess.noConfusion,
    `OpenGA.SurgeryComparisonProcess.noConfusionType,
    `OpenGA.SurgeryComparisonProcess.rec,
    `OpenGA.SurgeryComparisonProcess.recOn,
    `OpenGA.SurgeryComparisonProcess.scalar,
    `OpenGA.SurgeryComparisonProcess.scalar_cont,
    `OpenGA.SurgeryComparisonProcess.scalar_initial,
    `OpenGA.SurgeryComparisonProcess.scalar_jump,
    `OpenGA.SurgeryComparisonProcess.scalar_slope,
    `OpenGA.SurgeryComparisonProcess.volumeControl,
    `OpenGA.SurgeryComparisonProcess.width,
    `OpenGA.SurgeryComparisonProcess.width_cont,
    `OpenGA.SurgeryComparisonProcess.width_initial,
    `OpenGA.SurgeryComparisonProcess.width_jump,
    `OpenGA.SurgeryComparisonProcess.width_nonneg,
    `OpenGA.WidthComparisonTrace,
    `OpenGA.WidthComparisonTrace.casesOn,
    `OpenGA.WidthComparisonTrace.comparison,
    `OpenGA.WidthComparisonTrace.count,
    `OpenGA.WidthComparisonTrace.count_pos,
    `OpenGA.WidthComparisonTrace.ctorIdx,
    `OpenGA.WidthComparisonTrace.first_time,
    `OpenGA.WidthComparisonTrace.last_time,
    `OpenGA.WidthComparisonTrace.mk,
    `OpenGA.WidthComparisonTrace.mk.inj,
    `OpenGA.WidthComparisonTrace.mk.injEq,
    `OpenGA.WidthComparisonTrace.mk.noConfusion,
    `OpenGA.WidthComparisonTrace.mk.sizeOf_spec,
    `OpenGA.WidthComparisonTrace.noConfusion,
    `OpenGA.WidthComparisonTrace.noConfusionType,
    `OpenGA.WidthComparisonTrace.rec,
    `OpenGA.WidthComparisonTrace.recOn,
    `OpenGA.WidthComparisonTrace.scalar,
    `OpenGA.WidthComparisonTrace.scalar_cont,
    `OpenGA.WidthComparisonTrace.scalar_initial,
    `OpenGA.WidthComparisonTrace.scalar_jump,
    `OpenGA.WidthComparisonTrace.scalar_slope,
    `OpenGA.WidthComparisonTrace.times,
    `OpenGA.WidthComparisonTrace.times_strict,
    `OpenGA.WidthComparisonTrace.width,
    `OpenGA.WidthComparisonTrace.width_cont,
    `OpenGA.WidthComparisonTrace.width_initial,
    `OpenGA.WidthComparisonTrace.width_jump,
    `OpenGA.WidthComparisonTrace.width_nonneg,
    `OpenGA.exists_event_free_partition,
    `OpenGA.nonempty_widthComparisonTrace_of_surgeryComparisonProcess] do
    let some ci := env.find? name | throwError "Missing declaration {name}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Lean.Level.param (Lean.Name.mkSimple s!"universe_{i}")
    let type := ci.type.instantiateLevelParams ci.levelParams levels
    let printed ← Lean.withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
      Lean.Meta.ppExpr type
    let mut fields := [("name", Lean.Json.str name.toString), ("type", Lean.Json.str printed.pretty)]
    if let .defnInfo d := ci then
      let value := d.value.instantiateLevelParams ci.levelParams levels
      let shown ← Lean.withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
        Lean.Meta.ppExpr value
      fields := fields ++ [("value", Lean.Json.str shown.pretty)]
    rows := rows.push (Lean.Json.mkObj fields)
  Lean.logInfo (Lean.Json.arr rows).compress
