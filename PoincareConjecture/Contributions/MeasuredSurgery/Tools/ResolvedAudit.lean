import Definitions.Def_OpenGA_GeodesicBall
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_OpenGA_MeasuredReferenceBall
import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData
/-
Reuses qinz1yang/differential-geometry, Copyright 2026 The DifferentialGeometry
contributors, Apache-2.0, commit 1b535dd102b94cc42b107cca27059687888f08b3.
The metric and distance are upstream/Mathlib constructions. The ball interface
is curated in OpenGA; source hypotheses and mathematical definitions are preserved.
-/

noncomputable section
set_option autoImplicit false

open Bundle Set DifferentialGeometry
open scoped Manifold ContDiff ENNReal

open Riemannian Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Balls for the Riemannian distance are open in the manifold topology. -/
theorem Riemannian.RiemannianMetric.isOpen_geodesicBall [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    IsOpen (g.geodesicBall p r) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  change IsOpen {x | edist p x < ENNReal.ofReal r}
  simpa only [Metric.eball, edist_comm] using
    (Metric.isOpen_eball : IsOpen (Metric.eball p (ENNReal.ofReal r)))


set_option autoImplicit false
open MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open Riemannian

/-- **Math.** An open-positive measure assigns positive measure to an open
positive-radius geodesic ball. The openness assumption can be discharged by
`RiemannianMetric.isOpen_geodesicBall`. -/
theorem Riemannian.RiemannianMetric.measure_geodesicBall_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {μ : Measure M}
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) {r : ℝ}
    (hμ : ∀ s : Set M, IsOpen s → s.Nonempty → 0 < μ s)
    (hopen : IsOpen (g.geodesicBall p r)) (hr : 0 < r) :
    0 < μ (g.geodesicBall p r) := by
  exact hμ _ hopen (g.geodesicBall_nonempty p hr)

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology

open OpenGA

theorem OpenGA.MeasuredReferenceBall.anchor_pos (B : MeasuredReferenceBall) : 0 < B.anchor := by
  apply div_pos _ B.modelVolume_pos
  apply ENNReal.toReal_pos_iff.mpr
  exact ⟨B.metric.measure_geodesicBall_pos B.center B.open_pos
    (B.metric.isOpen_geodesicBall B.center B.radius) B.radius_pos, B.measure_lt_top⟩


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

theorem OpenGA.nonempty_surgeryComparisonProcess_of_measuredData {W T : ℝ} (D : MeasuredSurgeryComparisonData W T) : Nonempty (SurgeryComparisonProcess W T) := ⟨D.toProcess⟩
open Lean in
run_meta do
  for name in [`OpenGA.MeasuredReferenceBall.anchor_pos, `OpenGA.nonempty_surgeryComparisonProcess_of_measuredData] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom: {axioms}"
    logInfo "Checked {name}: {axioms}"
