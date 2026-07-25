import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2
import DifferentialGeometry.Analysis.Sobolev.Solutions.FriedrichsCommutator

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

private lemma memLp_two_of_continuous_compact_closure
    {f : E → ℝ} (hf : Continuous f)
    {S : Set E} (hS_open : IsOpen S) (hS_cc : IsCompact (closure S)) :
    MemLp f 2 (volume.restrict S) := by
  have h_volume_closure_lt_top : volume (closure S) < ⊤ :=
    hS_cc.measure_lt_top
  have h_volume_lt_top : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) h_volume_closure_lt_top
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  obtain ⟨M, hM⟩ := hS_cc.bddAbove_image hf.abs.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable (max M 0) ?_
  rw [ae_restrict_iff' hS_open.measurableSet]
  refine Filter.Eventually.of_forall ?_
  intro x hx
  have h_in_closure : x ∈ closure S := subset_closure hx
  have h := hM (Set.mem_image_of_mem _ h_in_closure)
  rw [Real.norm_eq_abs]
  exact h.trans (le_max_left _ _)

structure SmoothApproximation
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (_u _f : E → ℝ) where

  u_seq : ℕ → E → ℝ

  f_seq : ℕ → E → ℝ

  u_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n)

  is_smooth_weak_sol :
    ∀ n, B.IsSmoothWeakSolution (u_seq n) (f_seq n)

  f_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (f_seq n) 2 (volume.restrict S)

  u_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (u_seq n) 2 (volume.restrict S)

  grad_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d,
        MemLp (fun y : E => (fderiv ℝ (u_seq n) y) (EuclideanSpace.single j 1))
          2 (volume.restrict S)

  data_bound : ℝ
  data_bound_nn : 0 ≤ data_bound

  data_integrated_bound :
    ∀ {Ω' : Set E}, IsOpen Ω' → IsCompact (closure Ω') →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        (∫ y in Ω',
            ∑ j : Fin d,
              ((fderiv ℝ (u_seq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E)) +
        (∫ y in Ω', (u_seq n y) ^ 2 ∂(volume : Measure E)) +
        (∫ y in Ω', (f_seq n y) ^ 2 ∂(volume : Measure E)) ≤
          C * data_bound

private lemma loc_per_n_smooth_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f)
    (i k : Fin d) (n : ℕ) :
    ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set E, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧ closure Ω' ⊆ Ω ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin d,
                    ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure E) +
              ∫ x in Ω', (S.u_seq n x) ^ 2 ∂(volume : Measure E) +
              ∫ x in Ω', (S.f_seq n x) ^ 2 ∂(volume : Measure E)) := by
  obtain ⟨C, hC_nn, h_eng⟩ := loc_smooth_solution (d := d) B
    hΩ'' hΩ''_compact_closure hΩ''_in_Ω h_room
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ :=
    h_eng (S.is_smooth_weak_sol n) (S.f_seq_l2_loc n) i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

theorem loc_nonsmooth_per_n_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E =>
          (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤ K * S.data_bound := by
  classical
  intro i k n
  obtain ⟨g, hg_l2, hg_partial, Ω', hΩ'_open, _hΩ''_in_Ω', _hΩ'_in_Ω,
      hΩ'_compact, C, hC_nn, hC_bound⟩ :=
    loc_per_n_smooth_bound (d := d) B hΩ'' hΩ''_compact_closure hΩ''_in_Ω
      h_room S i k n
  obtain ⟨D, hD_nn, hD_bound⟩ :=
    S.data_integrated_bound (Ω' := Ω') hΩ'_open hΩ'_compact
  refine ⟨g, hg_l2, hg_partial, C * D,
    mul_nonneg hC_nn hD_nn, ?_⟩
  have h_data_le := hD_bound n
  refine hC_bound.trans ?_
  calc C * _
      ≤ C * (D * S.data_bound) :=
        mul_le_mul_of_nonneg_left h_data_le hC_nn
    _ = (C * D) * S.data_bound := by ring

theorem loc_nonsmooth_solution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g_n : E → ℝ,
      MemLp g_n 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g_n
        (fun y : E =>
          (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g_n x ^ 2 ∂(volume : Measure E) ≤ K * S.data_bound :=
  loc_nonsmooth_per_n_bound (d := d) B hΩ'' hΩ''_compact_closure
    hΩ''_in_Ω h_room S

end DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
