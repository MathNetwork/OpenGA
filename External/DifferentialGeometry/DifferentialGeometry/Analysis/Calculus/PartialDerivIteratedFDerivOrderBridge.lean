import DifferentialGeometry.Analysis.Calculus.IteratedFDerivProductDifferenceBound
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula


noncomputable section

open Set
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma partialDeriv_contDiffOn_of_isOpen
    {u : E → ℝ} {s : Set E} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) i u) s := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) s :=
    hu.fderiv_of_isOpen hs (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

lemma partialDeriv_sub_eqOn
    {u v : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    (i : Fin (Module.finrank ℝ E)) :
    EqOn (fun z => partialDeriv (E := E) i u z - partialDeriv (E := E) i v z)
      (partialDeriv (E := E) i (fun z => u z - v z)) s := by
  intro y hy
  have hdu : DifferentiableAt ℝ u y :=
    (hu.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
  have hdv : DifferentiableAt ℝ v y :=
    (hv.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
  simp only [partialDeriv]
  have hfd : fderiv ℝ (fun z => u z - v z) y = fderiv ℝ u y - fderiv ℝ v y := by
    have := fderiv_sub (𝕜 := ℝ) hdu hdv
    simpa using this
  rw [hfd, ContinuousLinearMap.sub_apply]

theorem partial_eq_iter1 (u : E → ℝ) (i : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) i u y =
      iteratedFDeriv ℝ 1 u y ![(chartModelBasis E) i] := by
  rw [iteratedFDeriv_one_apply]
  rfl

theorem partial2_eq_iter2 (u : E → ℝ) {y : E} (hu : ContDiffAt ℝ ∞ u y)
    (m l : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (partialDeriv (E := E) l u) y =
      iteratedFDeriv ℝ 2 u y ![(chartModelBasis E) m, (chartModelBasis E) l] := by
  have hfderiv_diff : DifferentiableAt ℝ (fun z : E => fderiv ℝ u z) y := by
    have hderiv := hu.fderiv_right (m := ∞) le_rfl
    exact hderiv.differentiableAt (by simp)
  have hl : partialDeriv (E := E) l u =
      fun z : E => fderiv ℝ u z ((chartModelBasis E) l) := by
    funext z
    rfl
  rw [show partialDeriv (E := E) m (partialDeriv (E := E) l u) y =
      fderiv ℝ (fun z : E => fderiv ℝ u z ((chartModelBasis E) l)) y
        ((chartModelBasis E) m) from by rw [hl]; rfl]
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply hfderiv_diff (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

lemma partialDeriv_eqOn_fderivWithin_apply
    {u : E → ℝ} {s : Set E} (hs : IsOpen s) (i : Fin (Module.finrank ℝ E)) :
    EqOn (partialDeriv (E := E) i u)
      (fun y => fderivWithin ℝ u s y ((chartModelBasis E) i)) s := by
  intro y hy
  simp only [partialDeriv, fderivWithin_of_isOpen hs hy]

theorem partial3_eq_iter3 (u : E → ℝ) {y : E} (hu : ContDiffAt ℝ ∞ u y)
    (n m l : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) n (partialDeriv (E := E) m (partialDeriv (E := E) l u)) y =
      iteratedFDeriv ℝ 3 u y
        ![(chartModelBasis E) n, (chartModelBasis E) m, (chartModelBasis E) l] := by
  obtain ⟨t, ht_nhds, hut⟩ := hu.contDiffOn (m := 3)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3) (by simp)
  obtain ⟨s, hst, hs_open, hys⟩ := mem_nhds_iff.mp ht_nhds
  have hu_s : ContDiffOn ℝ 3 u s := hut.mono hst
  have hpartial_at : ContDiffAt ℝ ∞ (partialDeriv (E := E) l u) y := by
    unfold partialDeriv
    exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiffAt_const
  have hfderiv_s : ContDiffOn ℝ 2 (fderivWithin ℝ u s) s :=
    hu_s.fderivWithin hs_open.uniqueDiffOn (by norm_num)
  calc
    partialDeriv (E := E) n (partialDeriv (E := E) m (partialDeriv (E := E) l u)) y =
        iteratedFDeriv ℝ 2 (partialDeriv (E := E) l u) y
          ![(chartModelBasis E) n, (chartModelBasis E) m] :=
      partial2_eq_iter2 (partialDeriv (E := E) l u) hpartial_at n m
    _ = iteratedFDerivWithin ℝ 2 (partialDeriv (E := E) l u) s y
          ![(chartModelBasis E) n, (chartModelBasis E) m] := by
      rw [iteratedFDerivWithin_of_isOpen 2 hs_open hys]
    _ = iteratedFDerivWithin ℝ 2
          (fun z => fderivWithin ℝ u s z ((chartModelBasis E) l)) s y
          ![(chartModelBasis E) n, (chartModelBasis E) m] := by
      rw [iteratedFDerivWithin_congr
        (partialDeriv_eqOn_fderivWithin_apply hs_open l) hys 2]
    _ = iteratedFDerivWithin ℝ 2 (fderivWithin ℝ u s) s y
          ![(chartModelBasis E) n, (chartModelBasis E) m] ((chartModelBasis E) l) := by
      exact iteratedFDerivWithin_clm_apply_const_apply hs_open.uniqueDiffOn hfderiv_s
        (by norm_num) hys
    _ = iteratedFDerivWithin ℝ 3 u s y
          ![(chartModelBasis E) n, (chartModelBasis E) m, (chartModelBasis E) l] := by
      have htuple :
          (![(chartModelBasis E) n, (chartModelBasis E) m, (chartModelBasis E) l] : Fin 3 → E) =
            Fin.snoc (![(chartModelBasis E) n, (chartModelBasis E) m] : Fin 2 → E)
              ((chartModelBasis E) l) := by
        funext i
        fin_cases i <;> rfl
      symm
      rw [htuple]
      simpa only [Fin.init_snoc, Fin.snoc_last] using
        iteratedFDerivWithin_succ_apply_right (𝕜 := ℝ) (f := u)
        hs_open.uniqueDiffOn hys
          (Fin.snoc (![(chartModelBasis E) n, (chartModelBasis E) m] : Fin 2 → E)
            ((chartModelBasis E) l))
    _ = iteratedFDeriv ℝ 3 u y
          ![(chartModelBasis E) n, (chartModelBasis E) m, (chartModelBasis E) l] := by
      rw [iteratedFDerivWithin_of_isOpen 3 hs_open hys]

theorem norm_iteratedFDerivWithin_partialDeriv_le
    {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin (Module.finrank ℝ E))
    (N : ℕ) {y : E} (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ N (partialDeriv (E := E) i u) s y‖ ≤
      ‖(chartModelBasis E) i‖ * ‖iteratedFDerivWithin ℝ (N + 1) u s y‖ := by
  have hcongr :
      iteratedFDerivWithin ℝ N (partialDeriv (E := E) i u) s y =
        iteratedFDerivWithin ℝ N
          (fun z => fderivWithin ℝ u s z ((chartModelBasis E) i)) s y :=
    iteratedFDerivWithin_congr (partialDeriv_eqOn_fderivWithin_apply hs i) hy N
  rw [hcongr]
  have hfderiv : ContDiffOn ℝ ∞ (fderivWithin ℝ u s) s :=
    hu.fderivWithin (hs.uniqueDiffOn) (by rw [ENat.coe_top_add_one])
  have hclm := norm_iteratedFDerivWithin_clm_apply_const
    (f := fderivWithin ℝ u s) (c := (chartModelBasis E) i) (s := s) (x := y)
    (N := (⊤ : ℕ∞)) (n := N)
    (hfderiv.contDiffWithinAt hy) hs.uniqueDiffOn hy (by exact_mod_cast le_top)
  refine hclm.trans ?_
  have heq : ‖iteratedFDerivWithin ℝ N (fderivWithin ℝ u s) s y‖ =
      ‖iteratedFDerivWithin ℝ (N + 1) u s y‖ :=
    norm_iteratedFDerivWithin_fderivWithin hs.uniqueDiffOn hy
  rw [heq]

theorem iteratedFDerivSeminorm_partialDeriv_le
    {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin (Module.finrank ℝ E))
    (N : ℕ) {y : E} (hy : y ∈ s) :
    iteratedFDerivSeminorm N (partialDeriv (E := E) i u) s y ≤
      ‖(chartModelBasis E) i‖ * iteratedFDerivSeminorm (N + 1) u s y := by
  classical
  have hstep :
      iteratedFDerivSeminorm N (partialDeriv (E := E) i u) s y ≤
        ‖(chartModelBasis E) i‖ *
          ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ (l + 1) u s y‖ := by
    unfold iteratedFDerivSeminorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    exact norm_iteratedFDerivWithin_partialDeriv_le hs hu i l hy
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  unfold iteratedFDerivSeminorm
  have himg :
      ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ (l + 1) u s y‖ =
        ∑ m ∈ (Finset.range (N + 1)).image (· + 1),
          ‖iteratedFDerivWithin ℝ m u s y‖ := by
    rw [Finset.sum_image (g := (· + 1))
      (f := fun m => ‖iteratedFDerivWithin ℝ m u s y‖)
      (by intro a _ b _ hab; simpa using hab)]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨l, hl, rfl⟩ := hm
  rw [Finset.mem_range] at hl ⊢
  omega

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
