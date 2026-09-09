import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import OpenGALib.Analysis.AreaEnergy
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# DifferentialGeometry integration

OpenGA's `RiemannianMetric` and upstream's `SmoothRiemannianMetric` are
definitionally the same Mathlib metric. The upstream volume construction
therefore accepts an OpenGA metric directly, with no conversion of tensors.

We use upstream's finite-volume and positive-open-set theorems to integrate
our area and energy densities on a compact Riemannian manifold. For continuous
vector fields, equality of the integrals forces orthogonality and equal norms
everywhere. The fields still need to be identified with differential vectors
in a geometric application; no global tangent frame is assumed here.

Upstream: qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
We import the upstream proofs and preserve their namespaces and attribution.
-/

set_option autoImplicit false

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace Riemannian.RiemannianMetric

/-- **Math.** The upstream Riemannian volume of an OpenGA metric. -/
noncomputable abbrev volumeMeasure (g : RiemannianMetric I M) : Measure M :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g

/-- **Math.** Compact manifolds have finite Riemannian volume. -/
theorem volumeMeasure_isFiniteMeasure [CompactSpace M] (g : RiemannianMetric I M) :
    IsFiniteMeasure g.volumeMeasure :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

/-- **Math.** Every nonempty open set has positive Riemannian volume. -/
theorem volumeMeasure_isOpenPosMeasure (g : RiemannianMetric I M) :
    g.volumeMeasure.IsOpenPosMeasure :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure g

end Riemannian.RiemannianMetric

namespace OpenGA

variable [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (g : Riemannian.RiemannianMetric I M) {v w : M → F}

omit [InnerProductSpace ℝ F] in
/-- **Math.** Continuous vector fields have integrable energy density on a
compact Riemannian manifold. -/
theorem integrable_energyDensity_riemannian (hv : Continuous v) (hw : Continuous w) :
    Integrable (fun x => energyDensity (v x) (w x)) g.volumeMeasure := by
  let : IsFiniteMeasure g.volumeMeasure := g.volumeMeasure_isFiniteMeasure
  have hcont : Continuous (fun x => energyDensity (v x) (w x)) := by
    unfold energyDensity
    fun_prop
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Math.** Area-energy comparison using upstream Riemannian volume;
compactness and continuity supply integrability. -/
theorem integral_areaDensity_le_energyDensity_riemannian
    (hv : Continuous v) (hw : Continuous w) :
    (∫ x, areaDensity (v x) (w x) ∂g.volumeMeasure) ≤
      ∫ x, energyDensity (v x) (w x) ∂g.volumeMeasure := by
  have hv' : AEStronglyMeasurable v g.volumeMeasure :=
    (hv.stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace v)).aestronglyMeasurable
  have hw' : AEStronglyMeasurable w g.volumeMeasure :=
    (hw.stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace w)).aestronglyMeasurable
  exact integral_areaDensity_le_energyDensity
    hv' hw'
    (integrable_energyDensity_riemannian g hv hw)

/-- **Math.** With continuous fields, equality of area and energy integrals
forces an orthogonal equal-length pair at every point. -/
theorem integral_areaDensity_eq_energyDensity_riemannian_iff
    (hv : Continuous v) (hw : Continuous w) :
    (∫ x, areaDensity (v x) (w x) ∂g.volumeMeasure) =
        (∫ x, energyDensity (v x) (w x) ∂g.volumeMeasure) ↔
      ∀ x, ⟪v x, w x⟫_ℝ = 0 ∧ ‖v x‖ = ‖w x‖ := by
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  have harea : Continuous (fun x => areaDensity (v x) (w x)) :=
    continuous_areaDensity.comp (hv.prodMk hw)
  have henergy : Continuous (fun x => energyDensity (v x) (w x)) := by
    unfold energyDensity
    fun_prop
  have hE := integrable_energyDensity_riemannian g hv hw
  have hv' : AEStronglyMeasurable v g.volumeMeasure :=
    (hv.stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace v)).aestronglyMeasurable
  have hw' : AEStronglyMeasurable w g.volumeMeasure :=
    (hw.stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace w)).aestronglyMeasurable
  rw [integral_eq_iff_of_ae_le
    (integrable_areaDensity hv' hw' hE) hE
    (Filter.Eventually.of_forall fun x => areaDensity_le_energyDensity (v x) (w x))]
  rw [harea.ae_eq_iff_eq g.volumeMeasure henergy, funext_iff]
  exact forall_congr' fun x => areaDensity_eq_energyDensity_iff (v x) (w x)

end OpenGA
