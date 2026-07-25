import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def dominatedCutoffAux (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1)

namespace dominatedCutoffAux

@[simp] theorem zero : dominatedCutoffAux 0 = 0 := by
  unfold dominatedCutoffAux
  have h : (4 : ℝ) * 0 - 1 ≤ 0 := by norm_num
  exact Real.smoothTransition.zero_of_nonpos h

theorem zero_of_le_quarter {t : ℝ} (ht : t ≤ 1/4) : dominatedCutoffAux t = 0 := by
  unfold dominatedCutoffAux
  have h : (4 : ℝ) * t - 1 ≤ 0 := by linarith
  exact Real.smoothTransition.zero_of_nonpos h

theorem one_of_half_le {t : ℝ} (ht : (1 : ℝ)/2 ≤ t) : dominatedCutoffAux t = 1 := by
  unfold dominatedCutoffAux
  have h : (1 : ℝ) ≤ 4 * t - 1 := by linarith
  exact Real.smoothTransition.one_of_one_le h

theorem nonneg (t : ℝ) : 0 ≤ dominatedCutoffAux t :=
  Real.smoothTransition.nonneg _

theorem le_one (t : ℝ) : dominatedCutoffAux t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem le_four_mul {t : ℝ} (ht : 0 ≤ t) : dominatedCutoffAux t ≤ 4 * t := by
  by_cases h : t ≤ 1/4
  · rw [zero_of_le_quarter h]
    linarith
  · have h' : (1 : ℝ)/4 < t := lt_of_not_ge h
    have h1 : (1 : ℝ) < 4 * t := by linarith
    have h2 : dominatedCutoffAux t ≤ 1 := le_one t
    linarith

theorem contDiff : ContDiff ℝ ∞ dominatedCutoffAux := by
  have h_affine : ContDiff ℝ ∞ (fun t : ℝ => 4 * t - 1) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have h_trans : ContDiff ℝ ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤))
  exact h_trans.comp h_affine

end dominatedCutoffAux

theorem chartAtlasPOU_exists_dominated_cutoff
    [T2Space M] [SigmaCompactSpace M]
    (α : M) :
    ∃ (χ : C^∞⟮I, M; ℝ⟯) (K : ℝ) (ε : ℝ), 0 < K ∧ 0 < ε ∧
      (∀ x : M, 0 ≤ χ x ∧ χ x ≤ K * (chartAtlasPOU I M α : M → ℝ) x) ∧
      (∀ x : M, ((chartAtlasPOU I M α : M → ℝ) x ≥ ε) → χ x = 1) ∧
      tsupport (χ : M → ℝ) ⊆ tsupport (chartAtlasPOU I M α : M → ℝ) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρ_def
  have hρ_contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ρ : M → ℝ) := ρ.contMDiff
  have hχ_contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => dominatedCutoffAux ((ρ : M → ℝ) x)) :=
    dominatedCutoffAux.contDiff.comp_contMDiff hρ_contMDiff
  refine ⟨⟨fun x => dominatedCutoffAux ((ρ : M → ℝ) x), hχ_contMDiff⟩,
          4, 1/2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro x
    refine ⟨?_, ?_⟩
    · exact dominatedCutoffAux.nonneg _
    · have hρ_nonneg : 0 ≤ (ρ : M → ℝ) x := by
        exact (chartAtlasPOU I M).nonneg α x
      exact dominatedCutoffAux.le_four_mul hρ_nonneg
  · intro x hx
    exact dominatedCutoffAux.one_of_half_le hx
  · have h_zero : dominatedCutoffAux 0 = 0 := dominatedCutoffAux.zero
    have h_subset : tsupport (dominatedCutoffAux ∘ (ρ : M → ℝ)) ⊆
        tsupport (ρ : M → ℝ) :=
      tsupport_comp_subset h_zero (ρ : M → ℝ)
    exact h_subset

end Measure
end Integral
end DifferentialGeometry
