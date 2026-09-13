import DifferentialGeometry.Geometry.Comparison.Volume.RatioIntegral
import OpenGALib.Analysis.IntegralComparison
open Lean in
run_meta do
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  for name in [
    `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_Iic_cross,
    `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_cross_le,
    `OpenGA.antitoneOn_lintegral_Ioc_div] do
    let some ci := env.find? name | throwError "Missing declaration {name}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Lean.Level.param (Lean.Name.mkSimple s!"universe_{i}")
    let type := ci.type.instantiateLevelParams ci.levelParams levels
    let printed ← Lean.withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
      Lean.Meta.ppExpr type
    rows := rows.push (Lean.Json.mkObj [("name", Lean.Json.str name.toString),
      ("type", Lean.Json.str printed.pretty)])
  Lean.logInfo (Lean.Json.arr rows).compress
