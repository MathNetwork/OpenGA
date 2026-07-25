import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef


noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def riemannianMeasureFamily
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) : ℝ → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)

lemma riemannianMeasureFamily_def
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t) := rfl

structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where

  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t

  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s :=
  { hasDerivAt_chartGramMatrix := hreg.hasDerivAt_chartGramMatrix
    continuousOn_chartGramMatrix := hreg.continuousOn_chartGramMatrix
    continuousOn_deriv_chartGramMatrix := hreg.continuousOn_deriv_chartGramMatrix }

structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where

  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t

  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)

  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => chartGramMatrix (I := I) (g_fam t) x₀ x

@[simp] lemma chartGramMatrixFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartGramMatrixFamily (I := I) g_fam x₀ x t =
      chartGramMatrix (I := I) (g_fam t) x₀ x := rfl

def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

@[simp] lemma chartDensityFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      chartDensity (I := I) (g_fam t) x₀ x := rfl

lemma chartDensityFamily_eq_sqrt_det
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := rfl

theorem hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M) (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam x₀ x s i j)
        (Gprime i j) t) :
    HasDerivAt
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
      ((1 / 2) *
        trace ((chartGramMatrixFamily (I := I) g_fam x₀ x t)⁻¹ * Gprime) *
        Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det) t := by
  have hpos : 0 < (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := by
    simpa [chartGramMatrixFamily_apply] using
      chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx
  have hderiv := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := chartGramMatrixFamily (I := I) g_fam x₀ x)
    (G' := Gprime) (t := t) hEntries hpos
  have hfun :
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
        = (fun s => Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x s).det) := by
    funext s
    exact chartDensityFamily_eq_sqrt_det (I := I) g_fam x₀ x s
  rw [hfun]
  exact hderiv

end ChartDensityFamily

variable (I) in

def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t))

lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

end Measure
end Integral
end DifferentialGeometry
