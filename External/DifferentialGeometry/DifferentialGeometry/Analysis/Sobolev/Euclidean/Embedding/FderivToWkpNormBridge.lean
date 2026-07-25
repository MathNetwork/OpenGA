import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma euclN_norm_le_sum_components_norms (w : EuclN) :
    ‖w‖ ≤ ∑ i : Fin d, ‖w i‖ := by
  classical
  have h_w_sum :
      w = ∑ i : Fin d, EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

omit [NeZero d] in
private lemma norm_fderiv_eq_norm_partials
    {ψ : EuclN → ℝ} (y : EuclN) :
    ‖fderiv ℝ ψ y‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin d =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) : EuclN)‖ := by
  classical
  set v : EuclN :=
    (InnerProductSpace.toDual ℝ EuclN).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuclN) v = fderiv ℝ ψ y := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2
        (fun i : Fin d =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuclN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin d =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]

omit [NeZero d] in
private lemma norm_fderiv_le_sum_partials
    (ψ : EuclN → ℝ) (y : EuclN) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin d, ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ := by
  rw [norm_fderiv_eq_norm_partials (d := d) y]
  refine (euclN_norm_le_sum_components_norms _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

omit [NeZero d] in
private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuclN}
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    eLpNorm (fun y : EuclN => ‖fderiv ℝ ψ y‖) q μ ≤
      ∑ i : Fin d,
        eLpNorm (fun y : EuclN =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin d,
      AEStronglyMeasurable
        (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) :=
      ((hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ y : EuclN,
      ‖fderiv ℝ ψ y‖ ≤ ∑ i : Fin d,
        ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ :=
    fun y => norm_fderiv_le_sum_partials (d := d) ψ y
  have h_step1 : eLpNorm (fun y : EuclN => ‖fderiv ℝ ψ y‖) q μ ≤
      eLpNorm (fun y : EuclN =>
        ∑ i : Fin d,
          ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro y
    have hh := h_pt y
    have h_norm : ‖‖fderiv ℝ ψ y‖‖ = ‖fderiv ℝ ψ y‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => fun y : EuclN => ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun y : EuclN =>
        ∑ i : Fin d,
          ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin d,
          fun y : EuclN => ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ := by
    funext y
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

omit [NeZero d] in
private lemma classical_partial_ae_eq_chosenWeakPartial
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_supp : tsupport ψ ⊆ Ω)
    (i : Fin d) :
    (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      chosenWeakPartial' (d := d) q i ψ Ω := by
  classical
  have hψ_mem : MemWkp (d := d) 1 q ψ Ω :=
    MemWkp_of_smooth_compactSupport_pub
      (d := d) hΩ_open hψ_smooth hψ_compact hψ_supp hq_one 1
  have hψ_W1p : DeGiorgi.MemW1p (d := d) q ψ Ω :=
    MemWkp.one_iff_memW1p.mp hψ_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := d) i
        (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) ψ Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := ψ)
      hΩ_open (hψ_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := d) i
        (chosenWeakPartial' (d := d) q i ψ Ω) ψ Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem (d := d) hψ_W1p i
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := d) q i ψ Ω) (volume.restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem (d := d)
      hψ_W1p i).locallyIntegrable hq_one
  have h_classical_loc : LocallyIntegrable
      (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) :=
      (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

omit [NeZero d] in
private lemma wkpNorm_order_one_block_eq_sum_partials
    {q : ℝ≥0∞} (ψ : EuclN → ℝ) (Ω : Set EuclN) :
    (∑ β : Fin 1 → Fin d,
        eLpNorm (iterWeakPartial (d := d) q 1 β ψ Ω) q
          (volume.restrict Ω)) =
      ∑ i : Fin d,
        eLpNorm (chosenWeakPartial' (d := d) q i ψ Ω) q
          (volume.restrict Ω) := by
  classical
  have h_unfold : ∀ β : Fin 1 → Fin d,
      eLpNorm (iterWeakPartial (d := d) q 1 β ψ Ω) q (volume.restrict Ω) =
        eLpNorm (chosenWeakPartial' (d := d) q (β 0) ψ Ω) q
          (volume.restrict Ω) := by
    intro β
    have hit :
        iterWeakPartial (d := d) q 1 β ψ Ω =
          chosenWeakPartial' (d := d) q (β 0) ψ Ω := by
      rw [iterWeakPartial_succ]
      simp [iterWeakPartial_zero]
    rw [hit]
  rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
  let e : (Fin 1 → Fin d) ≃ Fin d :=
    { toFun := fun β => β 0
      invFun := fun i _ => i
      left_inv := fun β => by
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        rw [hj]
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e
    (fun β =>
      eLpNorm (chosenWeakPartial' (d := d) q (β 0) ψ Ω) q (volume.restrict Ω))
    (fun i =>
      eLpNorm (chosenWeakPartial' (d := d) q i ψ Ω) q (volume.restrict Ω))
    (fun _ => rfl)

omit [NeZero d] in
private lemma sum_eLpNorm_chosenWeakPartial_le_wkpNorm_two
    (Ω : Set EuclN) (ψ : EuclN → ℝ) :
    (∑ i : Fin d,
        eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i ψ Ω) 2
          (volume.restrict Ω)) ≤
      iteratedWeakSobolevNorm (d := d) 2 2 ψ Ω := by
  classical
  have hWkpEq :
      iteratedWeakSobolevNorm (d := d) 2 2 ψ Ω =
        ∑ j ∈ Finset.range 3,
          ∑ β : Fin j → Fin d,
            eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β ψ Ω) 2
              (volume.restrict Ω) := by
    have h := wkpNorm_eq_sum (d := d) 2 (2 : ℝ≥0∞) ψ Ω
    simpa using h
  have hJ1Block := wkpNorm_order_one_block_eq_sum_partials
    (d := d) (q := (2 : ℝ≥0∞)) ψ Ω
  have h_range3 :
      ∑ j ∈ Finset.range 3,
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β ψ Ω) 2
            (volume.restrict Ω) =
      (∑ β : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 β ψ Ω) 2
            (volume.restrict Ω)) +
        (∑ β : Fin 1 → Fin d,
            eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 1 β ψ Ω) 2
              (volume.restrict Ω)) +
        (∑ β : Fin 2 → Fin d,
            eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 2 β ψ Ω) 2
              (volume.restrict Ω)) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
        show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
        Finset.sum_range_one]
  rw [hWkpEq, h_range3, ← hJ1Block]
  have hJ0_nonneg :
      0 ≤ (∑ β : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 β ψ Ω) 2
            (volume.restrict Ω)) := zero_le _
  have hJ2_nonneg :
      0 ≤ (∑ β : Fin 2 → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 2 β ψ Ω) 2
            (volume.restrict Ω)) := zero_le _
  calc (∑ β : Fin 1 → Fin d,
            eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 1 β ψ Ω) 2
              (volume.restrict Ω))
        ≤ (∑ β : Fin 0 → Fin d,
              eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 β ψ Ω) 2
                (volume.restrict Ω)) +
            (∑ β : Fin 1 → Fin d,
                eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 1 β ψ Ω) 2
                  (volume.restrict Ω)) :=
          le_add_of_nonneg_left hJ0_nonneg
      _ ≤ ((∑ β : Fin 0 → Fin d,
              eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 β ψ Ω) 2
                (volume.restrict Ω)) +
            (∑ β : Fin 1 → Fin d,
                eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 1 β ψ Ω) 2
                  (volume.restrict Ω))) +
            (∑ β : Fin 2 → Fin d,
                eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 2 β ψ Ω) 2
                  (volume.restrict Ω)) :=
          le_add_of_nonneg_right hJ2_nonneg

omit [NeZero d] in
theorem chartTarget_fderiv_eLpNorm_le_wkpNorm_two
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {u : EuclN → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_compact : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω) :
    eLpNorm (fun y : EuclN => ‖fderiv ℝ u y‖) 2 (volume.restrict Ω) ≤
      iteratedWeakSobolevNorm (d := d) 2 2 u Ω := by
  classical
  have hq_one : (1 : ℝ≥0∞) ≤ 2 := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
  have h_grad_le :=
    eLpNorm_norm_fderiv_le_sum_eLpNorm_partials (d := d)
      (q := (2 : ℝ≥0∞)) hq_one (μ := volume.restrict Ω) hu_smooth
  have h_each_eq : ∀ i : Fin d,
      eLpNorm (fun y : EuclN => (fderiv ℝ u y) (EuclideanSpace.single i 1)) 2
        (volume.restrict Ω) =
      eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i u Ω) 2
        (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial
      (d := d) hq_one hΩ_open hu_smooth hu_compact hu_supp i)
  have h_step :
      (∑ i : Fin d,
          eLpNorm
            (fun y : EuclN => (fderiv ℝ u y) (EuclideanSpace.single i 1)) 2
            (volume.restrict Ω)) =
        ∑ i : Fin d,
          eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i u Ω) 2
            (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  have h_le_wkp :=
    sum_eLpNorm_chosenWeakPartial_le_wkpNorm_two (d := d) Ω u
  exact h_grad_le.trans (le_of_eq h_step |>.trans h_le_wkp)

omit [NeZero d] in
private lemma sum_eLpNorm_chosenWeakPartial_le_wkpNorm_one_two
    (Ω : Set EuclN) (ψ : EuclN → ℝ) :
    (∑ i : Fin d,
        eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i ψ Ω) 2
          (volume.restrict Ω)) ≤
      iteratedWeakSobolevNorm (d := d) 1 2 ψ Ω := by
  classical
  have hWkpEq :
      iteratedWeakSobolevNorm (d := d) 1 2 ψ Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin d,
            eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β ψ Ω) 2
              (volume.restrict Ω) := by
    have h := wkpNorm_eq_sum (d := d) 1 (2 : ℝ≥0∞) ψ Ω
    simpa using h
  have hJ1Block := wkpNorm_order_one_block_eq_sum_partials
    (d := d) (q := (2 : ℝ≥0∞)) ψ Ω
  have h_range2 :
      ∑ j ∈ Finset.range 2,
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β ψ Ω) 2
            (volume.restrict Ω) =
      (∑ β : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 β ψ Ω) 2
            (volume.restrict Ω)) +
        (∑ β : Fin 1 → Fin d,
            eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 1 β ψ Ω) 2
              (volume.restrict Ω)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
        Finset.sum_range_one]
  rw [hWkpEq, h_range2, ← hJ1Block]
  have hJ0_nonneg :
      0 ≤ (∑ β : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 β ψ Ω) 2
            (volume.restrict Ω)) := zero_le _
  exact le_add_of_nonneg_left hJ0_nonneg

omit [NeZero d] in
theorem chartTarget_fderiv_eLpNorm_le_wkpNorm_one_two
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {u : EuclN → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_compact : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω) :
    eLpNorm (fun y : EuclN => ‖fderiv ℝ u y‖) 2 (volume.restrict Ω) ≤
      iteratedWeakSobolevNorm (d := d) 1 2 u Ω := by
  classical
  have hq_one : (1 : ℝ≥0∞) ≤ 2 := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
  have h_grad_le :=
    eLpNorm_norm_fderiv_le_sum_eLpNorm_partials (d := d)
      (q := (2 : ℝ≥0∞)) hq_one (μ := volume.restrict Ω) hu_smooth
  have h_each_eq : ∀ i : Fin d,
      eLpNorm (fun y : EuclN => (fderiv ℝ u y) (EuclideanSpace.single i 1)) 2
        (volume.restrict Ω) =
      eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i u Ω) 2
        (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial
      (d := d) hq_one hΩ_open hu_smooth hu_compact hu_supp i)
  have h_step :
      (∑ i : Fin d,
          eLpNorm
            (fun y : EuclN => (fderiv ℝ u y) (EuclideanSpace.single i 1)) 2
            (volume.restrict Ω)) =
        ∑ i : Fin d,
          eLpNorm (chosenWeakPartial' (d := d) (2 : ℝ≥0∞) i u Ω) 2
            (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  have h_le_wkp :=
    sum_eLpNorm_chosenWeakPartial_le_wkpNorm_one_two (d := d) Ω u
  exact h_grad_le.trans (le_of_eq h_step |>.trans h_le_wkp)

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
