import Definitions.Def_OpenGA_UnorientedGrassmannian
import Definitions.Def_OpenGA_EuclideanVarifold
import Definitions.Def_OpenGA_VarifoldConvergence
import Definitions.Def_OpenGA_WeightedMapVarifold
import Definitions.Def_OpenGA_ParametrizedVarifold
import Theorems.Thm_OpenGA_Varifold_tendsto_weightMeasure_integral
import Theorems.Thm_OpenGA_Varifold_testIntegral_ofWeightedMap
import Theorems.Thm_OpenGA_Varifold_ofWeightedMap_eq_of_plane_eq
import Theorems.Thm_OpenGA_Varifold_testIntegral_ofParametrization
import Theorems.Thm_OpenGA_Varifold_ofParametrization_independent_of_lift
import Theorems.Thm_OpenGA_Varifold_mass_ofParametrization_le_energy

open Lean in
run_meta do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in [`OpenGA.Grassmannian,`OpenGA.Grassmannian.continuous_projection,`OpenGA.Grassmannian.dist_eq,`OpenGA.Grassmannian.ext,`OpenGA.Grassmannian.ext_iff,`OpenGA.Grassmannian.finrank_plane,`OpenGA.Grassmannian.instBorelSpace,`OpenGA.Grassmannian.instCompactSpace,`OpenGA.Grassmannian.instMeasurableSpace,`OpenGA.Grassmannian.instMetricSpace,`OpenGA.Grassmannian.instSecondCountableTopology,`OpenGA.Grassmannian.isClosed_range_projection,`OpenGA.Grassmannian.isStarProjection_projection,`OpenGA.Grassmannian.isometry_projection,`OpenGA.Grassmannian.norm_projection_le,`OpenGA.Grassmannian.plane,`OpenGA.Grassmannian.projection,`OpenGA.Grassmannian.projection_eq_self_iff,`OpenGA.Grassmannian.projection_injective,`OpenGA.Grassmannian.projection_mem,`OpenGA.Grassmannian.range_projection,`OpenGA.Grassmannian.trace_projection,`OpenGA.Varifold,`OpenGA.Varifold.SurfaceTangentLift,`OpenGA.Varifold.SurfaceTangentLift.casesOn,`OpenGA.Varifold.SurfaceTangentLift.measurable_plane,`OpenGA.Varifold.SurfaceTangentLift.mk,`OpenGA.Varifold.SurfaceTangentLift.mk.noConfusion,`OpenGA.Varifold.SurfaceTangentLift.noConfusion,`OpenGA.Varifold.SurfaceTangentLift.plane,`OpenGA.Varifold.SurfaceTangentLift.plane_eq_range,`OpenGA.Varifold.SurfaceTangentLift.rec,`OpenGA.Varifold.SurfaceTangentLift.recOn,`OpenGA.Varifold.casesOn,`OpenGA.Varifold.continuous_surfaceJacobian,`OpenGA.Varifold.continuous_testIntegral,`OpenGA.Varifold.ext,`OpenGA.Varifold.ext_iff,`OpenGA.Varifold.ext_of_testIntegral_eq,`OpenGA.Varifold.finite_area_of_isCompact,`OpenGA.Varifold.instAdd,`OpenGA.Varifold.instSMulNNReal,`OpenGA.Varifold.instT2Space,`OpenGA.Varifold.instTopologicalSpace,`OpenGA.Varifold.instZero,`OpenGA.Varifold.integrable_testFunction,`OpenGA.Varifold.integral_weightMeasure,`OpenGA.Varifold.isClosed_support,`OpenGA.Varifold.isEmbedding_testIntegral,`OpenGA.Varifold.liftSpatialTest,`OpenGA.Varifold.liftSpatialTest_apply,`OpenGA.Varifold.linearSurfaceTangentLift,`OpenGA.Varifold.mass,`OpenGA.Varifold.mass_add,`OpenGA.Varifold.mass_eq_weightMeasure_univ,`OpenGA.Varifold.mass_ofParametrization,`OpenGA.Varifold.mass_ofParametrization_le_energy,`OpenGA.Varifold.mass_ofWeightedMap,`OpenGA.Varifold.mass_zero,`OpenGA.Varifold.measure,`OpenGA.Varifold.measure_add,`OpenGA.Varifold.measure_ofWeightedMap,`OpenGA.Varifold.measure_smul,`OpenGA.Varifold.measure_zero,`OpenGA.Varifold.mem_support_iff,`OpenGA.Varifold.mk,`OpenGA.Varifold.mk.noConfusion,`OpenGA.Varifold.noConfusion,`OpenGA.Varifold.ofParametrization,`OpenGA.Varifold.ofParametrization_independent_of_lift,`OpenGA.Varifold.ofWeightedMap,`OpenGA.Varifold.ofWeightedMap_eq_of_plane_eq,`OpenGA.Varifold.rec,`OpenGA.Varifold.recOn,`OpenGA.Varifold.regular,`OpenGA.Varifold.support,`OpenGA.Varifold.surfaceJacobian,`OpenGA.Varifold.surfaceJacobian_eq_areaDensity,`OpenGA.Varifold.tendsto_add,`OpenGA.Varifold.tendsto_iff_testIntegral,`OpenGA.Varifold.tendsto_weightMeasure_integral,`OpenGA.Varifold.testIntegral,`OpenGA.Varifold.testIntegral_add,`OpenGA.Varifold.testIntegral_liftSpatialTest,`OpenGA.Varifold.testIntegral_ofParametrization,`OpenGA.Varifold.testIntegral_ofWeightedMap,`OpenGA.Varifold.weightMeasure,`OpenGA.Varifold.weightMeasure_add,`OpenGA.Varifold.weightMeasure_apply,`OpenGA.Varifold.weightMeasure_compact_lt_top,`OpenGA.Varifold.weightMeasure_finiteOnCompacts,`OpenGA.Varifold.weightMeasure_ofWeightedMap,`OpenGA.Varifold.weightMeasure_regular,`OpenGA.Varifold.weightMeasure_zero] do
    let some ci := env.find? name | throwError "Missing {name}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"universe_{i}")
    let type := ci.type.instantiateLevelParams ci.levelParams levels
    let shown ← withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
      Meta.ppExpr type
    let mut fields := [("name", Json.str name.toString), ("type", Json.str shown.pretty)]
    if let .defnInfo d := ci then
      let value := d.value.instantiateLevelParams ci.levelParams levels
      let printed ← withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
        Meta.ppExpr value
      fields := fields ++ [("value", Json.str printed.pretty)]
    rows := rows.push (Json.mkObj fields)
  logInfo (Json.arr rows).compress
