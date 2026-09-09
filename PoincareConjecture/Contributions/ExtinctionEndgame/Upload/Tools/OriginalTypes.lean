import Reduction

open Lean in
run_meta do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in [`OpenGA.ClosedThreeManifold,`OpenGA.ClosedThreeManifold.Carrier,`OpenGA.ClosedThreeManifold.IsSphereCovered,`OpenGA.ClosedThreeManifold.IsSphereHandle,`OpenGA.ClosedThreeManifold.IsStandardFactor,`OpenGA.ClosedThreeManifold.casesOn,`OpenGA.ClosedThreeManifold.charts,`OpenGA.ClosedThreeManifold.compact,`OpenGA.ClosedThreeManifold.connected,`OpenGA.ClosedThreeManifold.hausdorff,`OpenGA.ClosedThreeManifold.instLocallyPathConnectedSpaceCarrier,`OpenGA.ClosedThreeManifold.mk,`OpenGA.ClosedThreeManifold.mk.noConfusion,`OpenGA.ClosedThreeManifold.noConfusion,`OpenGA.ClosedThreeManifold.rec,`OpenGA.ClosedThreeManifold.recOn,`OpenGA.ClosedThreeManifold.topology,`OpenGA.ConnectedSum.BoundaryIdentification,`OpenGA.ConnectedSum.Space,`OpenGA.ConnectedSum.instTopologicalSpaceSpace,`OpenGA.ConnectedSumClosure,`OpenGA.ConnectedSumClosure.casesOn,`OpenGA.ConnectedSumClosure.factor,`OpenGA.ConnectedSumClosure.homeomorph,`OpenGA.ConnectedSumClosure.rec,`OpenGA.ConnectedSumClosure.recOn,`OpenGA.ConnectedSumClosure.sum,`OpenGA.CoordinateBall,`OpenGA.CoordinateBall.Punctured,`OpenGA.CoordinateBall.boundary,`OpenGA.CoordinateBall.casesOn,`OpenGA.CoordinateBall.chart,`OpenGA.CoordinateBall.closedBall_subset_source,`OpenGA.CoordinateBall.instTopologicalSpacePunctured,`OpenGA.CoordinateBall.mk,`OpenGA.CoordinateBall.mk.noConfusion,`OpenGA.CoordinateBall.noConfusion,`OpenGA.CoordinateBall.rec,`OpenGA.CoordinateBall.recOn,`OpenGA.EuclideanThree,`OpenGA.FiniteSurgeryHistory,`OpenGA.FiniteSurgeryHistory.casesOn,`OpenGA.FiniteSurgeryHistory.rec,`OpenGA.FiniteSurgeryHistory.recOn,`OpenGA.FiniteSurgeryHistory.refl,`OpenGA.FiniteSurgeryHistory.step,`OpenGA.IsConnectedSum,`OpenGA.SphereOne,`OpenGA.SphereThree,`OpenGA.SphereTwo,`OpenGA.SurgeryReconstruction,`OpenGA.SurgeryTopologyEvolution,`OpenGA.SurgeryTopologyEvolution.FiniteExtinction,`OpenGA.SurgeryTopologyEvolution.HasWidthControl,`OpenGA.SurgeryTopologyEvolution.casesOn,`OpenGA.SurgeryTopologyEvolution.components,`OpenGA.SurgeryTopologyEvolution.finiteExtinction_of_width_control,`OpenGA.SurgeryTopologyEvolution.history,`OpenGA.SurgeryTopologyEvolution.initial,`OpenGA.SurgeryTopologyEvolution.initial_interval,`OpenGA.SurgeryTopologyEvolution.mk,`OpenGA.SurgeryTopologyEvolution.mk.noConfusion,`OpenGA.SurgeryTopologyEvolution.noConfusion,`OpenGA.SurgeryTopologyEvolution.rec,`OpenGA.SurgeryTopologyEvolution.recOn,`OpenGA.SurgeryTopologyEvolution.topology_from_extinction,`OpenGA.WidthComparisonTrace.le_extinctionTime,`OpenGA.instCoeSortClosedThreeManifoldType,`OpenGA.widthExtinctionTime,`PoincareFormalization.ExtinctionEndgame.exists_width_controlled_surgery_topology,`PoincareFormalization.ExtinctionEndgame.nonempty_homeomorph_sphere_of_connected_sum_spheres,`PoincareFormalization.ExtinctionEndgame.nonempty_homeomorph_sphere_of_standard_decomposition,`PoincareFormalization.ExtinctionEndgame.not_simply_connected_sphere_handle,`PoincareFormalization.ExtinctionEndgame.simply_connected_factors_of_connected_sum] do
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
