import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt


noncomputable section

open Set
open scoped Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

def partialDerivWithin (s : Set E) (i : Fin (Module.finrank ℝ E))
    (u : E → ℝ) (y : E) : ℝ :=
  fderivWithin ℝ u s y ((chartModelBasis E) i)

@[simp] lemma partialDerivWithin_def (s : Set E)
    (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) :
    partialDerivWithin (E := E) s i u y =
      fderivWithin ℝ u s y ((chartModelBasis E) i) := rfl

section ComparisonWithFDeriv

variable {s : Set E} {i : Fin (Module.finrank ℝ E)} {u : E → ℝ} {y : E}

lemma partialDerivWithin_eq_partialDeriv_of_isOpen
    (hs : IsOpen s) (hy : y ∈ s) :
    partialDerivWithin (E := E) s i u y = partialDeriv (E := E) i u y := by
  unfold partialDerivWithin partialDeriv
  rw [fderivWithin_of_isOpen hs hy]

lemma partialDerivWithin_eq_partialDeriv_of_mem_interior
    (hy : y ∈ interior s) :
    partialDerivWithin (E := E) s i u y = partialDeriv (E := E) i u y := by
  have hnhds : s ∈ 𝓝 y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
  unfold partialDerivWithin partialDeriv
  rw [fderivWithin_of_mem_nhds hnhds]

lemma partialDerivWithin_congr {u v : E → ℝ}
    (huv : EqOn u v s) (hy : u y = v y) :
    partialDerivWithin (E := E) s i u y =
      partialDerivWithin (E := E) s i v y := by
  unfold partialDerivWithin
  rw [fderivWithin_congr huv hy]

lemma partialDerivWithin_congr_of_eqOn_of_mem {u v : E → ℝ}
    (huv : EqOn u v s) (hy : y ∈ s) :
    partialDerivWithin (E := E) s i u y =
      partialDerivWithin (E := E) s i v y :=
  partialDerivWithin_congr huv (huv hy)

end ComparisonWithFDeriv

section Smoothness

variable {m n : WithTop ℕ∞} {s : Set E} {u : E → ℝ}
  {i : Fin (Module.finrank ℝ E)}

lemma partialDerivWithin_contDiffOn_of_uniqueDiffOn
    (hu : ContDiffOn ℝ n u s) (hs : UniqueDiffOn ℝ s) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialDerivWithin (E := E) s i u) s := by
  have hfderiv : ContDiffOn ℝ m (fderivWithin ℝ u s) s :=
    hu.fderivWithin hs hmn
  have hconst : ContDiffOn ℝ m
      (fun _ : E => (chartModelBasis E) i) s := contDiffOn_const
  exact hfderiv.clm_apply hconst

lemma partialDerivWithin_contDiffOn_top_of_uniqueDiffOn
    (hu : ContDiffOn ℝ ∞ u s) (hs : UniqueDiffOn ℝ s) :
    ContDiffOn ℝ ∞ (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_uniqueDiffOn (n := ∞) (m := ∞) hu hs
    (by rw [ENat.coe_top_add_one])

lemma partialDerivWithin_contDiffOn_of_isOpen
    (hu : ContDiffOn ℝ n u s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_uniqueDiffOn hu hs.uniqueDiffOn hmn

lemma partialDerivWithin_contDiffOn_top_of_isOpen
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) :
    ContDiffOn ℝ ∞ (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_isOpen (n := ∞) (m := ∞) hu hs
    (by rw [ENat.coe_top_add_one])

end Smoothness

section LeibnizIdentities

variable {s : Set E} {y : E} {i : Fin (Module.finrank ℝ E)}

lemma partialDerivWithin_add (u v : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hu : DifferentiableWithinAt ℝ u s y)
    (hv : DifferentiableWithinAt ℝ v s y) :
    partialDerivWithin (E := E) s i (fun y => u y + v y) y =
      partialDerivWithin (E := E) s i u y +
        partialDerivWithin (E := E) s i v y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_add hs hu hv]
  rfl

lemma partialDerivWithin_smul (c : E → ℝ) (u : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hc : DifferentiableWithinAt ℝ c s y)
    (hu : DifferentiableWithinAt ℝ u s y) :
    partialDerivWithin (E := E) s i (fun y => c y • u y) y =
      c y • partialDerivWithin (E := E) s i u y +
        partialDerivWithin (E := E) s i c y • u y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_smul hs hc hu]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]

lemma partialDerivWithin_mul (u v : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hu : DifferentiableWithinAt ℝ u s y)
    (hv : DifferentiableWithinAt ℝ v s y) :
    partialDerivWithin (E := E) s i (fun y => u y * v y) y =
      u y * partialDerivWithin (E := E) s i v y +
        v y * partialDerivWithin (E := E) s i u y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_mul hs hu hv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

end LeibnizIdentities

section ChartTarget

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma uniqueDiffOn_extChartAt_target_apply (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    UniqueDiffWithinAt ℝ (extChartAt I α).target y :=
  uniqueDiffOn_extChartAt_target α y hy

omit [IsManifold I ∞ M] in
theorem partialDerivWithin_extChartAt_target_eq_partialDeriv
    (α : M) (i : Fin (Module.finrank ℝ E)) (u : E → ℝ)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDerivWithin (E := E) (extChartAt I α).target i u y =
      partialDeriv (E := E) i u y :=
  partialDerivWithin_eq_partialDeriv_of_mem_interior hy

end ChartTarget

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
