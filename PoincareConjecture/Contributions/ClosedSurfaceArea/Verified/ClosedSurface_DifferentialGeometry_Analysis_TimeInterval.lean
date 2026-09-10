import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real

set_option autoImplicit false

open scoped Topology

namespace DifferentialGeometry.Geometry.Curvature

structure RealTimeInterval where
  carrier : Set Real
  regular : Set Real
  initial : Real
  initial_mem : initial ∈ carrier
  regular_subset : regular ⊆ carrier
  regular_isOpen : IsOpen regular
  regular_mem_nhds : ∀ {t : Real}, t ∈ regular -> carrier ∈ 𝓝 t

namespace RealTimeInterval

abbrev FlowTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.carrier}

abbrev RegularTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.regular}

end RealTimeInterval

end DifferentialGeometry.Geometry.Curvature
