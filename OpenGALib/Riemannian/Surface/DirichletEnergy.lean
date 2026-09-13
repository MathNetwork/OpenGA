import OpenGALib.Riemannian.Surface.Area
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame

/-!
# Dirichlet energy of surface maps

Use the actual manifold derivative, the domain metric's orthonormal frame at
each point, and the domain Riemannian volume measure. No immersion hypothesis
is imposed. The nonnegative integral takes values in ENNReal so that finiteness
is not silently assumed. This uses classical derivatives; weak derivatives
and the W1,2 mapping-space topology are not defined by this module.

The metric, centered orthonormal frames, and measure are reused from the
pinned DifferentialGeometry dependency (Apache-2.0). The normalization is
one half of the squared Hilbert--Schmidt norm, as in CM equation (1.2).
-/

noncomputable section
open Bundle MeasureTheory
open scoped Manifold ContDiff BigOperators ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure

namespace OpenGA.Surface

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Model N]
  [IsManifold 𝓘(ℝ, Model) ∞ N] [T2Space N] [SigmaCompactSpace N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

def dirichletDensity (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N)
    (g : SmoothRiemannianMetric I M) (f : N → M) (x : N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin (Module.finrank ℝ Model),
    g.inner (f x)
      (mfderiv 𝓘(ℝ, Model) I f x (smoothOrthoFrame q x i x))
      (mfderiv 𝓘(ℝ, Model) I f x (smoothOrthoFrame q x i x))

omit [T2Space N] [SigmaCompactSpace N] in
theorem dirichletDensity_nonneg (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N)
    (g : SmoothRiemannianMetric I M) (f : N → M) (x : N) :
    0 ≤ dirichletDensity q g f x := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  by_cases h : mfderiv 𝓘(ℝ, Model) I f x (smoothOrthoFrame q x i x) = 0
  · simp [h]
  · exact (g.pos _ _ h).le

/-- Extended Dirichlet energy; smooth sweepout slices use this functional. -/
def dirichletEnergy (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N)
    (g : SmoothRiemannianMetric I M) (f : N → M) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (dirichletDensity q g f x) ∂(riemannianVolumeMeasure 𝓘(ℝ, Model) N q)

/-- On the integrable domain this is the usual real Dirichlet integral. -/
theorem dirichletEnergy_eq_ofReal_integral
    (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N) (g : SmoothRiemannianMetric I M)
    (f : N → M)
    (hf : Integrable (dirichletDensity q g f) (riemannianVolumeMeasure 𝓘(ℝ, Model) N q)) :
    dirichletEnergy q g f = ENNReal.ofReal
      (∫ x, dirichletDensity q g f x ∂(riemannianVolumeMeasure 𝓘(ℝ, Model) N q)) :=
  (ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall (dirichletDensity_nonneg q g f))).symm

theorem dirichletEnergy_lt_top_of_integrable
    (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N) (g : SmoothRiemannianMetric I M)
    (f : N → M)
    (hf : Integrable (dirichletDensity q g f) (riemannianVolumeMeasure 𝓘(ℝ, Model) N q)) :
    dirichletEnergy q g f < ⊤ := by
  rw [dirichletEnergy_eq_ofReal_integral q g f hf]
  exact ENNReal.ofReal_lt_top

omit [T2Space N] [SigmaCompactSpace N] in
@[simp] theorem dirichletDensity_const (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N)
    (g : SmoothRiemannianMetric I M) (c : M) (x : N) :
    dirichletDensity q g (fun _ => c) x = 0 := by
  simp [dirichletDensity, mfderiv_const]

@[simp] theorem dirichletEnergy_const (q : SmoothRiemannianMetric 𝓘(ℝ, Model) N)
    (g : SmoothRiemannianMetric I M) (c : M) :
    dirichletEnergy q g (fun _ => c) = 0 := by
  simp [dirichletEnergy]

end OpenGA.Surface
