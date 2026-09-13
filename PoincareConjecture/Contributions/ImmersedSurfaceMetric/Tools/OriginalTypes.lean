import OpenGALib.Riemannian.Surface
open Lean in
run_meta do
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  for name in [`DifferentialGeometry.Geometry.posDef_isVonNBounded,
    `DifferentialGeometry.cotangentCov_clmSection_smooth_aux,
    `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd,
    `OpenGA.Surface.inducedInner,
    `OpenGA.Surface.inducedInner_apply,
    `OpenGA.Surface.inducedInner_contMDiff,
    `OpenGA.Surface.inducedInner_pos,
    `OpenGA.Surface.inducedMetric,
    `OpenGA.Surface.inducedMetric_inner,
    `OpenGA.Surface.patchArea_inducedMetric,
    `OpenGA.Surface.surfaceDensity_inducedMetric,
    `OpenGA.Surface.surfaceMetricMatrix_inducedMetric,
    `contMDiffAt_clm_of_pointwise] do
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
      let axioms ← Lean.collectAxioms name
      unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "Unexpected definition axiom: {axioms}"
    rows := rows.push (Lean.Json.mkObj fields)
  Lean.logInfo (Lean.Json.arr rows).compress
