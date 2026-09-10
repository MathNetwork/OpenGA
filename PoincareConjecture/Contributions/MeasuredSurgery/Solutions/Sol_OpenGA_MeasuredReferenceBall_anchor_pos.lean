import Theorems.Thm_Riemannian_RiemannianMetric_isOpen_geodesicBall
import Theorems.Thm_Riemannian_RiemannianMetric_measure_geodesicBall_pos
import Definitions.Def_OpenGA_MeasuredReferenceBall
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology

open OpenGA

theorem solution (B : MeasuredReferenceBall) : 0 < B.anchor := by
  apply div_pos _ B.modelVolume_pos
  apply ENNReal.toReal_pos_iff.mpr
  exact ⟨B.metric.measure_geodesicBall_pos B.center B.open_pos
    (B.metric.isOpen_geodesicBall B.center B.radius) B.radius_pos, B.measure_lt_top⟩

