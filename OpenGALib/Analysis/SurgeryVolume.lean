import OpenGALib.Analysis.ModelVolume
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finiteness of surgery events from radial volume comparison

This is an analytic interface for the volume-loss argument in Kleiner-Lott,
Section 3.5 (p. 13), with the comparison-of-scales input used in Sublemma
79.23 (p. 157). It does not define a Ricci flow or a surgery operation.
A geometric application must construct the radial densities, identify their
integrals with volumes of regions contained in the removed material, and
bound the total removed volume, accounting for volume growth between events.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal BigOperators
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace OpenGA

/-- **Math.** Uniform radial comparison data and a finite volume-loss budget.
No finiteness or discreteness is assumed for the set of event times. -/
structure RadialSurgeryVolumeBudget where
  events : Set ℝ
  modelParameter : ℝ
  modelParameter_nonneg : 0 ≤ modelParameter
  referenceRadius : ℝ
  removalRadius : ℝ
  removalRadius_pos : 0 < removalRadius
  radius_le : removalRadius ≤ referenceRadius
  anchor : ℝ
  anchor_pos : 0 < anchor
  totalBudget : ℝ
  density : ℝ → ℝ → ℝ≥0∞
  density_measurable : ∀ t ∈ events,
    AEMeasurable (density t) (volume.restrict (Ioc 0 referenceRadius))
  density_comparison : ∀ t ∈ events, CrossAnti referenceRadius (density t)
    (fun r => ENNReal.ofReal (hypDensity modelParameter 2 r))
  reference_lower : ∀ t ∈ events, ENNReal.ofReal anchor ≤
    (∫⁻ r in Ioc (0 : ℝ) referenceRadius, density t r) /
      ENNReal.ofReal (hypRadVol modelParameter 2 referenceRadius)
  removedVolume : ℝ → ℝ
  removedVolume_nonneg : ∀ t ∈ events, 0 ≤ removedVolume t
  removal_contains : ∀ t ∈ events,
    (∫⁻ r in Ioc (0 : ℝ) removalRadius, density t r) ≤ ENNReal.ofReal (removedVolume t)
  volume_budget : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ events →
    ∑ t ∈ s, removedVolume t ≤ totalBudget

/-- **Math.** Model-volume monotonicity supplies a uniform positive lower
bound for the volume removed at each event. -/
theorem RadialSurgeryVolumeBudget.removedVolume_lower (B : RadialSurgeryVolumeBudget)
    {t : ℝ} (ht : t ∈ B.events) :
    B.anchor * hypRadVol B.modelParameter 2 B.removalRadius ≤ B.removedVolume t := by
  have hR : 0 < B.referenceRadius := B.removalRadius_pos.trans_le B.radius_le
  have hm := antitoneOn_lintegral_div_hypRadVol B.modelParameter_nonneg
    (B.density_measurable t ht) (B.density_comparison t ht)
    ⟨B.removalRadius_pos, B.radius_le⟩ ⟨hR, le_rfl⟩ B.radius_le
  have hle := (B.reference_lower t ht).trans hm
  have hmul := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr
      (hypRadVol_pos B.modelParameter_nonneg B.removalRadius_pos)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mp hle
  have hbound := hmul.trans (B.removal_contains t ht)
  rw [← ENNReal.ofReal_mul B.anchor_pos.le] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (B.removedVolume_nonneg t ht)).mp hbound

/-- **Math.** A finite budget and a uniform positive loss force finitely
many events. The lower loss is derived from radial model comparison. -/
theorem RadialSurgeryVolumeBudget.events_finite (B : RadialSurgeryVolumeBudget) :
    B.events.Finite := by
  classical
  by_contra hinfinite
  have heps : 0 < B.anchor * hypRadVol B.modelParameter 2 B.removalRadius :=
    mul_pos B.anchor_pos (hypRadVol_pos B.modelParameter_nonneg B.removalRadius_pos)
  obtain ⟨n, hn⟩ := exists_nat_gt (B.totalBudget /
    (B.anchor * hypRadVol B.modelParameter 2 B.removalRadius))
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite n
  have hsum : (s.card : ℝ) * (B.anchor * hypRadVol B.modelParameter 2 B.removalRadius) ≤
      ∑ t ∈ s, B.removedVolume t := by
    calc
      _ = ∑ _t ∈ s, B.anchor * hypRadVol B.modelParameter 2 B.removalRadius := by simp
      _ ≤ _ := Finset.sum_le_sum fun t ht => B.removedVolume_lower (hs ht)
  rw [hcard] at hsum
  have hbudget := B.volume_budget s hs
  have hgt := (div_lt_iff₀ heps).mp hn
  linarith

end OpenGA
