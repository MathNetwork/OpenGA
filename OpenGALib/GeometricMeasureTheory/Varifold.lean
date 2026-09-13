import OpenGALib.GeometricMeasureTheory.Grassmannian
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Euclidean varifolds and their weight measures

A `k`-varifold on `E` is a nonnegative Radon measure on
`E × Grassmannian E k`. The `Measure.Regular` field includes finiteness on
compact sets and regularity; total mass need not be finite. On this locally
compact metric space this gives the Radon measures used by Simon.

Reference: Leon Simon, *Introduction to Geometric Measure Theory*, 2018,
Chapter 8, Section 1, pp. 235-236. This module treats the Euclidean ambient
space. It does not identify the product with the Grassmann bundle of an
arbitrary manifold, and does not impose rectifiability or stationarity.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology CompactlySupported

namespace OpenGA

/-- A Radon measure on positions and unoriented `k`-planes. -/
structure Varifold (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (k : ℕ) where
  measure : Measure (E × Grassmannian E k)
  regular : measure.Regular

attribute [instance] Varifold.regular

namespace Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}

@[ext] theorem ext {V W : Varifold E k} (h : V.measure = W.measure) : V = W := by
  cases V
  cases W
  cases h
  rfl

/-- Spatial projection of a varifold, conventionally denoted `‖V‖`. -/
def weightMeasure (V : Varifold E k) : Measure E := V.measure.map Prod.fst

theorem weightMeasure_apply (V : Varifold E k) {A : Set E} (hA : MeasurableSet A) :
    V.weightMeasure A = V.measure (A ×ˢ Set.univ) := by
  rw [weightMeasure, Measure.map_apply measurable_fst hA]
  congr 1
  ext z
  simp

instance weightMeasure_finiteOnCompacts (V : Varifold E k) :
    IsFiniteMeasureOnCompacts V.weightMeasure := by
  constructor
  intro K hK
  rw [weightMeasure_apply V hK.measurableSet]
  exact (hK.prod isCompact_univ).measure_lt_top

/-- Compactness of the Grassmannian ensures that spatial projection is again Radon. -/
instance weightMeasure_regular (V : Varifold E k) : V.weightMeasure.Regular :=
  inferInstance

/-- Total mass, allowed to be infinite for a general varifold. -/
def mass (V : Varifold E k) : ℝ≥0∞ := V.measure Set.univ

theorem mass_eq_weightMeasure_univ (V : Varifold E k) :
    V.mass = V.weightMeasure Set.univ := by
  simp [mass, weightMeasure_apply V MeasurableSet.univ]

theorem weightMeasure_compact_lt_top (V : Varifold E k) {K : Set E} (hK : IsCompact K) :
    V.weightMeasure K < ∞ := hK.measure_lt_top

/-- The support in the ambient space is the support of the weight measure. -/
def support (V : Varifold E k) : Set E := V.weightMeasure.support

theorem isClosed_support (V : Varifold E k) : IsClosed V.support :=
  Measure.isClosed_support

theorem mem_support_iff (V : Varifold E k) (x : E) :
    x ∈ V.support ↔ ∀ U ∈ nhds x, 0 < V.weightMeasure U :=
  V.weightMeasure.mem_support_iff_forall x

instance : Zero (Varifold E k) := ⟨⟨0, inferInstance⟩⟩
instance : Add (Varifold E k) := ⟨fun V W => by
  haveI : IsFiniteMeasureOnCompacts (V.measure + W.measure) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  exact ⟨V.measure + W.measure, inferInstance⟩⟩
instance : SMul ℝ≥0 (Varifold E k) := ⟨fun c V => ⟨c • V.measure, inferInstance⟩⟩

@[simp] theorem measure_zero : (0 : Varifold E k).measure = 0 := rfl
@[simp] theorem measure_add (V W : Varifold E k) : (V + W).measure = V.measure + W.measure := rfl
@[simp] theorem measure_smul (c : ℝ≥0) (V : Varifold E k) :
    (c • V).measure = c • V.measure := rfl

@[simp] theorem weightMeasure_zero : (0 : Varifold E k).weightMeasure = 0 := by
  simp [weightMeasure]

@[simp] theorem weightMeasure_add (V W : Varifold E k) :
    (V + W).weightMeasure = V.weightMeasure + W.weightMeasure := by
  exact Measure.map_add _ _ measurable_fst

@[simp] theorem mass_zero : (0 : Varifold E k).mass = 0 := by simp [mass]
@[simp] theorem mass_add (V W : Varifold E k) : (V + W).mass = V.mass + W.mass :=
  Measure.add_apply _ _ _

/-- Pairing with a continuous, compactly supported test function on positions and planes. -/
def testIntegral (V : Varifold E k) (φ : C_c(E × Grassmannian E k, ℝ)) : ℝ :=
  ∫ z, φ z ∂V.measure

theorem integrable_testFunction (V : Varifold E k) (φ : C_c(E × Grassmannian E k, ℝ)) :
    Integrable φ V.measure := φ.integrable

@[simp] theorem testIntegral_add (V W : Varifold E k)
    (φ : C_c(E × Grassmannian E k, ℝ)) :
    (V + W).testIntegral φ = V.testIntegral φ + W.testIntegral φ :=
  integral_add_measure φ.integrable φ.integrable

/-- Integrating a spatial observable against the weight equals integrating its lift. -/
theorem integral_weightMeasure (V : Varifold E k) {f : E → ℝ}
    (hf : AEStronglyMeasurable f V.weightMeasure) :
    ∫ x, f x ∂V.weightMeasure = ∫ z, f z.1 ∂V.measure :=
  integral_map measurable_fst.aemeasurable hf

end Varifold
end OpenGA
