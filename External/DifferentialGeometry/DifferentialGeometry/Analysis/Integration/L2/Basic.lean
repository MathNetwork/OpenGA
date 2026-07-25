import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support


noncomputable section

open Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem aestronglyMeasurable_of_continuous
    {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : M → F} (hf : Continuous f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  hf.aestronglyMeasurable

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem aestronglyMeasurable_of_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem aestronglyMeasurable_of_contMDiff_of_nat
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {n : WithTop ℕ∞} {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) n f)
    (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

theorem integrable_of_continuous_of_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F]
    {μ : MeasureTheory.Measure M} [IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hfc : Continuous f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f μ :=
  hfc.integrable_of_hasCompactSupport hfsup

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem integrable_of_contMDiff_of_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} [IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hfc : ContMDiff I 𝓘(ℝ, F) ∞ f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f μ :=
  integrable_of_continuous_of_hasCompactSupport hfc.continuous hfsup

theorem integrable_of_continuous_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : Continuous f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem integrable_of_contMDiff_compactSpace
    [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} [IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    MeasureTheory.Integrable f μ :=
  integrable_of_contMDiff_of_hasCompactSupport hf (HasCompactSupport.of_compactSpace f)

theorem integral_add_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f μ)
    (hf' : MeasureTheory.Integrable f' μ) :
    ∫ x, (f x + f' x) ∂μ = (∫ x, f x ∂μ) + (∫ x, f' x ∂μ) :=
  MeasureTheory.integral_add hf hf'

theorem integral_smul_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    (c : ℝ) (f : M → F) :
    ∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ :=
  MeasureTheory.integral_smul c f

theorem integral_sub_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f μ)
    (hf' : MeasureTheory.Integrable f' μ) :
    ∫ x, (f x - f' x) ∂μ = (∫ x, f x ∂μ) - (∫ x, f' x ∂μ) :=
  MeasureTheory.integral_sub hf hf'

theorem integral_neg_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} (f : M → F) :
    ∫ x, -f x ∂μ = -∫ x, f x ∂μ :=
  MeasureTheory.integral_neg f

theorem integral_zero_of_riemannianVolume
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} :
    ∫ _ : M, (0 : F) ∂μ = 0 :=
  MeasureTheory.integral_zero M F

theorem integral_const_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : MeasureTheory.Measure M} (c : F) :
    ∫ _ : M, c ∂μ = μ.real univ • c :=
  MeasureTheory.integral_const c

theorem integral_congr_ae_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (h : f =ᵐ[μ] f') :
    ∫ x, f x ∂μ = ∫ x, f' x ∂μ :=
  MeasureTheory.integral_congr_ae h

theorem lintegral_add_left_of_riemannianVolume
    {μ : MeasureTheory.Measure M}
    {f : M → ℝ≥0∞} (hf : Measurable f) (f' : M → ℝ≥0∞) :
    ∫⁻ x, f x + f' x ∂μ = (∫⁻ x, f x ∂μ) + (∫⁻ x, f' x ∂μ) :=
  MeasureTheory.lintegral_add_left hf f'

theorem lintegral_const_mul_of_riemannianVolume
    {μ : MeasureTheory.Measure M}
    (r : ℝ≥0∞) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, r * f x ∂μ = r * ∫⁻ x, f x ∂μ :=
  MeasureTheory.lintegral_const_mul r hf

end L2
end Integral
end DifferentialGeometry
