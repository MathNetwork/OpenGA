import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Morrey
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EuclideanMorrey

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ball_inter_closedHalfSpace_subset_ball
    {x₀ : E} {r : ℝ} :
    Metric.ball x₀ r ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ⊆
      Metric.ball x₀ r :=
  inter_subset_left

theorem ball_inter_closedHalfSpace_subset_closedHalfSpace
    {x₀ : E} {r : ℝ} :
    Metric.ball x₀ r ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
  inter_subset_right

theorem smooth_morrey_pair_bound_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x y : E},
        x ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
        y ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
          ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
            (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ R))).toReal := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_pair_bound (d := d) hp hR hu
  refine ⟨C, hC_nn, ?_⟩
  intro x y hx hy
  exact hbound (ball_inter_closedHalfSpace_subset_ball hx)
    (ball_inter_closedHalfSpace_subset_ball hy)

theorem smooth_morrey_sup_bound_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
        ‖u x‖ ≤ C * (
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
          (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_sup_bound (d := d) hp hR hu
  refine ⟨C, hC_nn, ?_⟩
  intro x hx
  exact hbound x (ball_inter_closedHalfSpace_subset_ball hx)

theorem smooth_morrey_holder_modulus_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x y : E},
        x ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
        y ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
          ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_holder_modulus (d := d) hp hR hu
  refine ⟨C, hC_nn, ?_⟩
  intro x y hx hy
  exact hbound (ball_inter_closedHalfSpace_subset_ball hx)
    (ball_inter_closedHalfSpace_subset_ball hy)

theorem smooth_morrey_pair_bound_uniform_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ {x y : E},
          x ∈ Metric.ball x₀ (R / 2) ∩
              DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
          y ∈ Metric.ball x₀ (R / 2) ∩
              DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
            ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
              (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_pair_bound_uniform (d := d) hp hR
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x y hx hy
  exact hbound hu (ball_inter_closedHalfSpace_subset_ball hx)
    (ball_inter_closedHalfSpace_subset_ball hy)

theorem smooth_morrey_sup_bound_uniform_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ x ∈ Metric.ball x₀ (R / 2) ∩
              DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
          ‖u x‖ ≤ C *
            ((eLpNorm u (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal +
             (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal) := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_sup_bound_uniform (d := d) hp hR
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x hx
  exact hbound hu x (ball_inter_closedHalfSpace_subset_ball hx)

theorem ball_subset_openHalfSpace_of_dist_pos
    {x₀ : E} {R : ℝ}
    (hx₀ : R ≤ x₀ 0) :
    Metric.ball x₀ R ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h_proj : |y 0 - x₀ 0| ≤ ‖y - x₀‖ := by
    have h_eq : |y 0 - x₀ 0| = |(y - x₀) 0| := by
      simp [PiLp.sub_apply]
    rw [h_eq]
    have h_eval :
        |(y - x₀) 0| = ‖(y - x₀) 0‖ := by
      rw [Real.norm_eq_abs]
    rw [h_eval]
    exact PiLp.norm_apply_le (y - x₀) 0
  change (0 : ℝ) < y 0
  have h_y0_ge : x₀ 0 - ‖y - x₀‖ ≤ y 0 := by
    have := abs_le.mp h_proj
    linarith [this.1]
  linarith

theorem ball_inter_closedHalfSpace_eq_ball_of_dist_pos
    {x₀ : E} {R : ℝ}
    (hx₀ : R ≤ x₀ 0) :
    Metric.ball x₀ R ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace =
      Metric.ball x₀ R := by
  apply Set.Subset.antisymm inter_subset_left
  intro y hy
  refine ⟨hy, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_subset_closedHalfSpace
    (ball_subset_openHalfSpace_of_dist_pos hx₀ hy)

theorem ball_subset_interiorHalfSpace_of_dist_pos
    {x₀ : E} {R : ℝ}
    (hx₀ : R ≤ x₀ 0)
    {Ω : Set E}
    (h_ball_sub : Metric.ball x₀ R ⊆ Ω) :
    Metric.ball x₀ R ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω := by
  intro y hy
  refine ⟨h_ball_sub hy, ?_⟩
  exact ball_subset_openHalfSpace_of_dist_pos hx₀ hy

theorem morrey_holder_representative_halfSpace_interior
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hx₀ : R ≤ x₀ 0)
    {Ω : Set E}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen Ω)
    (h_ball_sub : Metric.ball x₀ R ⊆ Ω)
    {u : E → ℝ}
    (hu : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := d) 1 (ENNReal.ofReal p) u Ω) :
    ∃ (ũ : E → ℝ) (C : ℝ) (G : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧ 0 ≤ G ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
       ∀ y ∈ Metric.ball x₀ (R / 4) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
        ‖ũ x - ũ y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) * G) := by
  classical
  have _ := hΩ
  have h_ball_sub_int :
      Metric.ball x₀ R ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω :=
    ball_subset_interiorHalfSpace_of_dist_pos hx₀ h_ball_sub
  have h_memW1p :
      DeGiorgi.MemW1p (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) := by
    have h_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := d) 1 (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
      hu
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp h_unfold
  let hw_int : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
    h_memW1p.someWitness
  have h_ball_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  let hw_ball : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R) :=
    DeGiorgi.MemW1pWitness.restrict h_ball_open h_ball_sub_int hw_int
  obtain ⟨ũ, CHolder, hũ_cont, hC_nn, h_ae, h_holder⟩ :=
    morrey_holder_representative (d := d) hp hR hw_ball
  set G : ℝ := (eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hG_def
  have hG_nn : 0 ≤ G := ENNReal.toReal_nonneg
  refine ⟨ũ, CHolder, G, hũ_cont, hC_nn, hG_nn, h_ae, ?_⟩
  intro x hx y hy
  exact h_holder x hx.1 y hy.1

theorem morrey_sup_bound_halfSpace_interior
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hx₀ : R ≤ x₀ 0)
    {Ω : Set E}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen Ω)
    (h_ball_sub : Metric.ball x₀ R ⊆ Ω)
    {u : E → ℝ}
    (hu : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := d) 1 (ENNReal.ofReal p) u Ω) :
    ∃ (ũ : E → ℝ) (C : ℝ) (Nu G : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧ 0 ≤ Nu ∧ 0 ≤ G ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
        ‖ũ x‖ ≤ C * (Nu + G)) := by
  classical
  have _ := hΩ
  have h_ball_sub_int :
      Metric.ball x₀ R ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω :=
    ball_subset_interiorHalfSpace_of_dist_pos hx₀ h_ball_sub
  have h_memW1p :
      DeGiorgi.MemW1p (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) := by
    have h_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := d) 1 (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
      hu
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp h_unfold
  let hw_int : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
    h_memW1p.someWitness
  have h_ball_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  let hw_ball : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R) :=
    DeGiorgi.MemW1pWitness.restrict h_ball_open h_ball_sub_int hw_int
  obtain ⟨ũ, CSup, hũ_cont, hC_nn, h_ae, h_sup⟩ :=
    morrey_sup_bound (d := d) hp hR hw_ball
  set Nu : ℝ := (eLpNorm u (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hNu_def
  set G : ℝ := (eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hG_def
  have hNu_nn : 0 ≤ Nu := ENNReal.toReal_nonneg
  have hG_nn : 0 ≤ G := ENNReal.toReal_nonneg
  refine ⟨ũ, CSup, Nu, G, hũ_cont, hC_nn, hNu_nn, hG_nn, h_ae, ?_⟩
  intro x hx
  have h_u_finite : eLpNorm u (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := hw_ball.memLp.eLpNorm_ne_top
  have h_grad_finite : eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
    hw_ball.weakGrad_norm_memLp.eLpNorm_ne_top
  have h_sum_eq : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) +
        eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal = Nu + G :=
    ENNReal.toReal_add h_u_finite h_grad_finite
  have h_initial := h_sup x hx.1
  rw [h_sum_eq] at h_initial
  exact h_initial

end EuclideanMorrey
end Sobolev
end Analysis
end DifferentialGeometry
