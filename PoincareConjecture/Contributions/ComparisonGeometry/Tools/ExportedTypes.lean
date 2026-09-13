import Theorems.Thm_Riemannian_RiemannianMetric_isOpen_geodesicBall
open Lean in
run_meta do
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  for name in [`DifferentialGeometry.SmoothRiemannianMetric,
    `Riemannian.RiemannianMetric,
    `DifferentialGeometry.riemannianEDistOf,
    `DifferentialGeometry.riemannianEDistOf_self,
    `Riemannian.RiemannianMetric.geodesicBall,
    `Riemannian.RiemannianMetric.mem_geodesicBall,
    `Riemannian.RiemannianMetric.geodesicBall_eq_empty,
    `Riemannian.RiemannianMetric.geodesicBall_mono,
    `Riemannian.RiemannianMetric.self_mem_geodesicBall,
    `Riemannian.RiemannianMetric.geodesicBall_nonempty,
    `Riemannian.RiemannianMetric.isOpen_geodesicBall] do
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
