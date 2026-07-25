import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ} {f : ℝ → X}

omit [InnerProductSpace ℝ X] [CompleteSpace X] in

theorem aestronglyMeasurable_of_continuousOn_Ioo
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) :
    AEStronglyMeasurable f (timeMeasure T) := by
  have hrestrict : timeMeasure T = volume.restrict (Set.Ioo (0 : ℝ) T) := by
    rw [timeMeasure, Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm]
  rw [hrestrict]
  exact hf.aestronglyMeasurable measurableSet_Ioo

omit [InnerProductSpace ℝ X] [CompleteSpace X] in

theorem memLp_of_continuousOn_Ioo
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) :
    MemLp f 2 (timeMeasure T) :=
  MemLp.of_bound (aestronglyMeasurable_of_continuousOn_Ioo hf) M hM

def ofContinuousOnIoo (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) : timeL2 X T :=
  (memLp_of_continuousOn_Ioo hf hM).toLp f

theorem coeFn_ofContinuousOnIoo (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) :
    ofContinuousOnIoo hf hM =ᵐ[timeMeasure T] f :=
  (memLp_of_continuousOn_Ioo hf hM).coeFn_toLp

theorem exists_timeL2_of_continuousOn_Ioo
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) :
    ∃ F : timeL2 X T, (F : ℝ → X) =ᵐ[timeMeasure T] f :=
  ⟨ofContinuousOnIoo hf hM, coeFn_ofContinuousOnIoo hf hM⟩

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
