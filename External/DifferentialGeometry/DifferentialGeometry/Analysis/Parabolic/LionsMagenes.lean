import Mathlib.Analysis.InnerProductSpace.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open Set MeasureTheory

theorem lions_magenes_intermediate_trace
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (ι : X →L[ℝ] Y) {T : ℝ} (u : timeH1 X T) :
    ContinuousOn (fun t => ι (u.toFun t)) (Set.Icc (0 : ℝ) T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖ι (u.toFun t)‖ ≤ ‖ι‖ * ((1 + Real.sqrt T) * ‖u‖) := by
  refine ⟨?_, ?_⟩
  · exact ι.continuous.comp_continuousOn u.continuousOn_toFun
  · intro t ht
    have h1 : ‖ι (u.toFun t)‖ ≤ ‖ι‖ * ‖u.toFun t‖ := ι.le_opNorm _
    have h2 : ‖u.toFun t‖ ≤ (1 + Real.sqrt T) * ‖u‖ := u.norm_toFun_le_norm ht
    have hι : 0 ≤ ‖ι‖ := norm_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hι)

end DifferentialGeometry.PDE.RicciFlow
