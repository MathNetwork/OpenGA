import DifferentialGeometry.Analysis.Calculus.IteratedFDerivProductDifferenceBound

noncomputable section

open Set
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDerivWithin_sum_le
    {ι : Type*} {F : ι → E → ℝ} {s : Set E} (hs : IsOpen s)
    (u : Finset ι) (hF : ∀ j ∈ u, ContDiffOn ℝ ∞ (F j) s)
    (N : ℕ) {y : E} (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ N (fun z => ∑ j ∈ u, F j z) s y‖ ≤
      ∑ j ∈ u, ‖iteratedFDerivWithin ℝ N (F j) s y‖ := by
  classical
  have hsum :
      iteratedFDerivWithin ℝ N (fun z => ∑ j ∈ u, F j z) s y =
        ∑ j ∈ u, iteratedFDerivWithin ℝ N (F j) s y := by
    have hpi : (fun z => ∑ j ∈ u, F j z) = (∑ j ∈ u, F j) := by
      funext z; simp
    rw [hpi]
    exact iteratedFDerivWithin_sum_apply (𝕜 := ℝ) (f := F) (u := u) (i := N)
      (s := s) (x := y) hs.uniqueDiffOn hy
      (fun j hj => ((hF j hj).contDiffWithinAt hy).of_le (by exact_mod_cast le_top))
  rw [hsum]
  exact norm_sum_le _ _

theorem norm_iteratedFDerivWithin_two_prod_sub_le
    {f₁ f₂ g₁ g₂ : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf₁ : ContDiffOn ℝ ∞ f₁ s) (hf₂ : ContDiffOn ℝ ∞ f₂ s)
    (hg₁ : ContDiffOn ℝ ∞ g₁ s) (hg₂ : ContDiffOn ℝ ∞ g₂ s)
    {K : Set E} (hKsub : K ⊆ s) {B : ℝ} (hB_nn : 0 ≤ B) (N : ℕ)
    (hf₂bound : ∀ y ∈ K, ∀ m : ℕ, m ≤ N → ‖iteratedFDerivWithin ℝ m f₂ s y‖ ≤ B)
    (hg₁bound : ∀ y ∈ K, ∀ m : ℕ, m ≤ N → ‖iteratedFDerivWithin ℝ m g₁ s y‖ ≤ B)
    {y : E} (hy : y ∈ K) :
    ‖iteratedFDerivWithin ℝ N (fun z => f₁ z * f₂ z - g₁ z * g₂ z) s y‖ ≤
      2 ^ N * B *
        (iteratedFDerivSeminorm N (fun z => f₁ z - g₁ z) s y +
          iteratedFDerivSeminorm N (fun z => f₂ z - g₂ z) s y) := by
  classical
  have hyS : y ∈ s := hKsub hy
  have htel : (fun z => f₁ z * f₂ z - g₁ z * g₂ z) =
      (fun z => (f₁ z - g₁ z) * f₂ z + g₁ z * (f₂ z - g₂ z)) := by
    funext z; ring
  rw [htel]
  have hcd1 : ContDiffOn ℝ ∞ (fun z => (f₁ z - g₁ z) * f₂ z) s :=
    ContDiffOn.mul (hf₁.sub hg₁) hf₂
  have hcd2 : ContDiffOn ℝ ∞ (fun z => g₁ z * (f₂ z - g₂ z)) s :=
    ContDiffOn.mul hg₁ (hf₂.sub hg₂)
  have hadd :
      iteratedFDerivWithin ℝ N
        (fun z => (f₁ z - g₁ z) * f₂ z + g₁ z * (f₂ z - g₂ z)) s y =
        iteratedFDerivWithin ℝ N (fun z => (f₁ z - g₁ z) * f₂ z) s y +
          iteratedFDerivWithin ℝ N (fun z => g₁ z * (f₂ z - g₂ z)) s y :=
    iteratedFDerivWithin_add_apply
      ((hcd1.contDiffWithinAt hyS).of_le (by exact_mod_cast le_top))
      ((hcd2.contDiffWithinAt hyS).of_le (by exact_mod_cast le_top))
      hs.uniqueDiffOn hyS
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have hbound1 :
      ‖iteratedFDerivWithin ℝ N (fun z => (f₁ z - g₁ z) * f₂ z) s y‖ ≤
        2 ^ N * B * iteratedFDerivSeminorm N (fun z => f₁ z - g₁ z) s y :=
    norm_iteratedFDerivWithin_mul_le_uniformBound hs (hf₁.sub hg₁) hf₂ hKsub hB_nn N
      hf₂bound hy
  have hbound2 :
      ‖iteratedFDerivWithin ℝ N (fun z => g₁ z * (f₂ z - g₂ z)) s y‖ ≤
        2 ^ N * B * iteratedFDerivSeminorm N (fun z => f₂ z - g₂ z) s y := by
    have hcomm : (fun z => g₁ z * (f₂ z - g₂ z)) =
        (fun z => (f₂ z - g₂ z) * g₁ z) := by funext z; ring
    rw [hcomm]
    exact norm_iteratedFDerivWithin_mul_le_uniformBound hs (hf₂.sub hg₂) hg₁ hKsub hB_nn N
      hg₁bound hy
  refine (add_le_add hbound1 hbound2).trans ?_
  rw [mul_add]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
