import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiffAt_hasMFDerivAt_of_tangent (x : M) (v : TangentSpace I x) :
    ∃ c : ℝ → M, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ c 0 ∧ c 0 = x ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  set φ : E := extChartAt I x x with hφ
  let w : E := v
  set L : ℝ → E := fun r => φ + r • w with hL
  have hL0 : L 0 = φ := by simp [hL]
  have hLcm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ L 0 := by
    rw [contMDiffAt_iff_contDiffAt]
    have : ContDiffAt ℝ ∞ (fun r : ℝ => φ + r • w) 0 := by fun_prop
    simpa [hL] using this
  have hLine : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) L 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    have hadd : HasFDerivAt L ((0 : ℝ →L[ℝ] E) + (1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
      rw [hL]
      refine HasFDerivAt.add (hasFDerivAt_const φ (0 : ℝ)) ?_
      refine (((1 : ℝ →L[ℝ] ℝ).smulRight w).hasFDerivAt (x := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards with r using by simp [ContinuousLinearMap.smulRight_apply]
    rw [zero_add] at hadd
    exact hadd
  have hsymmC : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm φ := by
    refine (contMDiffOn_extChartAt_symm (n := (∞ : WithTop ℕ∞)) x).contMDiffAt ?_
    simpa [hφ] using extChartAt_target_mem_nhds x
  have hsymmD : HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I x).symm (L 0)
      (ContinuousLinearMap.id ℝ E) := by
    have hmem : φ ∈ (extChartAt I x).target := by rw [hφ]; exact mem_extChartAt_target x
    have hdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ := by
      have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x) hmem
      rwa [I.range_eq_univ] at this
    have heq : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm univ φ
        = ContinuousLinearMap.id ℝ E := by
      rw [hφ, ← I.range_eq_univ]
      exact mfderivWithin_range_extChartAt_symm
    have hwd : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ
        (ContinuousLinearMap.id ℝ E) := heq ▸ hdiff.hasMFDerivWithinAt
    rw [hL0, ← hasMFDerivWithinAt_univ]
    exact hwd
  refine ⟨fun r => (extChartAt I x).symm (L r), ?_, ?_, ?_⟩
  · exact (hsymmC.comp_of_eq hLcm hL0 :)
  · simp [hL, hφ]
  · have hcomp := hsymmD.comp 0 hLine
    rw [Function.comp_def] at hcomp
    exact hcomp

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
