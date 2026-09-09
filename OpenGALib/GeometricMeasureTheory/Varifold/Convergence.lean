import OpenGALib.GeometricMeasureTheory.Varifold
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Varifold convergence

The topology is induced by all continuous compactly supported test functions on
`E × Grassmannian E k`, not by the total mass or the weight measure alone.
It is Hausdorff, and convergence is exactly convergence of these integrals.
Spatial weight measures consequently converge against compactly supported tests on `E`.

References: Simon, *Introduction to Geometric Measure Theory*, 2018, Chapter 8;
Colding-Minicozzi, *Width and finite extinction time of Ricci flow*, arXiv:0707.0108,
Section 1.3. The latter works on a compact manifold's Grassmann bundle. No quantitative
bound for a particular metrization is asserted by this qualitative convergence interface.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped CompactlySupported

namespace OpenGA.Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- Continuous compactly supported tests on both position and plane determine a varifold. -/
theorem ext_of_testIntegral_eq {V W : Varifold E k}
    (h : ∀ φ : C_c(E × Grassmannian E k, ℝ), V.testIntegral φ = W.testIntegral φ) :
    V = W :=
  ext (Measure.ext_of_integral_eq_on_compactlySupported h)

instance : TopologicalSpace (Varifold E k) :=
  TopologicalSpace.induced
    (testIntegral : Varifold E k → C_c(E × Grassmannian E k, ℝ) → ℝ) inferInstance

theorem isEmbedding_testIntegral :
    IsEmbedding (testIntegral : Varifold E k → C_c(E × Grassmannian E k, ℝ) → ℝ) :=
  ⟨⟨rfl⟩, fun _ _ h => ext_of_testIntegral_eq (congrFun h)⟩

instance : T2Space (Varifold E k) := isEmbedding_testIntegral.t2Space

/-- Varifold convergence is weak-* convergence as Radon measures on positions and planes. -/
theorem tendsto_iff_testIntegral {ι : Type*} {l : Filter ι}
    {V : ι → Varifold E k} {W : Varifold E k} :
    Tendsto V l (𝓝 W) ↔ ∀ φ : C_c(E × Grassmannian E k, ℝ),
      Tendsto (fun i => (V i).testIntegral φ) l (𝓝 (W.testIntegral φ)) := by
  rw [isEmbedding_testIntegral.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

theorem continuous_testIntegral (φ : C_c(E × Grassmannian E k, ℝ)) :
    Continuous (fun V : Varifold E k => V.testIntegral φ) :=
  (continuous_apply φ).comp isEmbedding_testIntegral.continuous

/-- Lift a spatial test function through the proper projection with compact Grassmannian fiber. -/
def liftSpatialTest (φ : C_c(E, ℝ)) : C_c(E × Grassmannian E k, ℝ) :=
  φ.comp
    { toFun := Prod.fst
      continuous_toFun := continuous_fst
      cocompact_tendsto' :=
        CocompactMap.tendsto_of_forall_preimage (fun _ hK =>
          isProperMap_fst_of_compactSpace.isCompact_preimage hK) }

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem liftSpatialTest_apply (φ : C_c(E, ℝ)) (z : E × Grassmannian E k) :
    liftSpatialTest φ z = φ z.1 := rfl

theorem testIntegral_liftSpatialTest (V : Varifold E k) (φ : C_c(E, ℝ)) :
    V.testIntegral (liftSpatialTest φ) = ∫ x, φ x ∂V.weightMeasure :=
  (V.integral_weightMeasure φ.continuous.aestronglyMeasurable).symm

/-- Varifold convergence implies vague convergence of the spatial weight measures. -/
theorem tendsto_weightMeasure_integral {ι : Type*} {l : Filter ι}
    {V : ι → Varifold E k} {W : Varifold E k} (h : Tendsto V l (𝓝 W))
    (φ : C_c(E, ℝ)) :
    Tendsto (fun i => ∫ x, φ x ∂(V i).weightMeasure) l
      (𝓝 (∫ x, φ x ∂W.weightMeasure)) := by
  simpa only [testIntegral_liftSpatialTest] using
    (tendsto_iff_testIntegral.mp h) (liftSpatialTest φ)

theorem tendsto_add {ι : Type*} {l : Filter ι}
    {V W : ι → Varifold E k} {V₀ W₀ : Varifold E k}
    (hV : Tendsto V l (𝓝 V₀)) (hW : Tendsto W l (𝓝 W₀)) :
    Tendsto (fun i => V i + W i) l (𝓝 (V₀ + W₀)) := by
  apply tendsto_iff_testIntegral.mpr
  intro φ
  simpa only [testIntegral_add] using
    ((tendsto_iff_testIntegral.mp hV) φ).add ((tendsto_iff_testIntegral.mp hW) φ)

end OpenGA.Varifold
