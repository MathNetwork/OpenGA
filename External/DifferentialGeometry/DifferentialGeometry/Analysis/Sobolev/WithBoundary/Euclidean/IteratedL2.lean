import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedL2
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def wkpNormL2SqHalfSpace (k : ℕ) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  wkpNormL2Sq (d := d) k u (interiorHalfSpace Ω)

def wkpNormL2HalfSpace (k : ℕ) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  wkpNormL2 (d := d) k u (interiorHalfSpace Ω)

@[simp] lemma wkpNormL2SqHalfSpace_def
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2SqHalfSpace (d := d) k u Ω =
      wkpNormL2Sq (d := d) k u (interiorHalfSpace Ω) := rfl

@[simp] lemma wkpNormL2HalfSpace_def
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2 (d := d) k u (interiorHalfSpace Ω) := rfl

theorem wkpNormL2HalfSpace_eq_rpow
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2SqHalfSpace (d := d) k u Ω ^ ((1 : ℝ) / 2) := by
  unfold wkpNormL2HalfSpace wkpNormL2SqHalfSpace
  exact wkpNormL2_eq_rpow (d := d) k u (interiorHalfSpace Ω)

def wkpInnerL2HalfSpace (k : ℕ) (u v : E → ℝ) (Ω : Set E) : ℝ :=
  wkpInnerL2 (d := d) k u v (interiorHalfSpace Ω)

@[simp] lemma wkpInnerL2HalfSpace_def
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2HalfSpace (d := d) k u v Ω =
      wkpInnerL2 (d := d) k u v (interiorHalfSpace Ω) := rfl

theorem wkpNormL2SqHalfSpace_zero
    (u : E → ℝ) (Ω : Set E) :
    wkpNormL2SqHalfSpace (d := d) 0 u Ω =
      eLpNorm u 2 ((volume : Measure E).restrict (interiorHalfSpace Ω)) ^ (2 : ℕ) := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_zero (d := d) u (interiorHalfSpace Ω)

theorem wkpNormL2SqHalfSpace_zero_fun_zero
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormL2SqHalfSpace (d := d) k (fun _ : E => (0 : ℝ)) Ω = 0 := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_zero_fun_zero (d := d) (interiorHalfSpace_isOpen hΩ)

theorem wkpNormL2HalfSpace_zero_fun_zero
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormL2HalfSpace (d := d) k (fun _ : E => (0 : ℝ)) Ω = 0 := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_zero_fun_zero (d := d) (interiorHalfSpace_isOpen hΩ)

theorem wkpNormL2SqHalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (h : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormL2SqHalfSpace (d := d) k u Ω < ∞ := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_lt_top_of_memWkp (d := d) h

theorem wkpNormL2HalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (h : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormL2HalfSpace (d := d) k u Ω < ∞ := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_lt_top_of_memWkp (d := d) h

theorem wkpNormL2SqHalfSpace_congr_ae
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict (interiorHalfSpace Ω)] v) :
    wkpNormL2SqHalfSpace (d := d) k u Ω =
      wkpNormL2SqHalfSpace (d := d) k v Ω := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_congr_ae (d := d) (interiorHalfSpace_isOpen hΩ) huv

theorem wkpNormL2HalfSpace_congr_ae
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict (interiorHalfSpace Ω)] v) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2HalfSpace (d := d) k v Ω := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_congr_ae (d := d) (interiorHalfSpace_isOpen hΩ) huv

theorem wkpNormL2SqHalfSpace_congr_ae_of_carrier
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict Ω] v) :
    wkpNormL2SqHalfSpace (d := d) k u Ω =
      wkpNormL2SqHalfSpace (d := d) k v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact wkpNormL2SqHalfSpace_congr_ae (d := d) hΩ huv

theorem wkpNormL2HalfSpace_congr_ae_of_carrier
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict Ω] v) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2HalfSpace (d := d) k v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact wkpNormL2HalfSpace_congr_ae (d := d) hΩ huv

theorem wkpNormL2HalfSpace_sq_eq_wkpNormL2SqHalfSpace
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2HalfSpace (d := d) k u Ω ^ (2 : ℕ) =
      wkpNormL2SqHalfSpace (d := d) k u Ω := by
  unfold wkpNormL2HalfSpace wkpNormL2SqHalfSpace
  exact wkpNormL2_sq_eq_wkpNormL2Sq (d := d) k u (interiorHalfSpace Ω)

theorem wkpNormL2HalfSpace_add_le
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω)
    (hv : MemWkpHalfSpace (d := d) k 2 v Ω) :
    wkpNormL2HalfSpace (d := d) k (fun x => u x + v x) Ω ≤
      wkpNormL2HalfSpace (d := d) k u Ω +
        wkpNormL2HalfSpace (d := d) k v Ω := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_add_le (d := d) (interiorHalfSpace_isOpen hΩ) hu hv

theorem wkpNormL2SqHalfSpace_const_smul
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu : MemWkpHalfSpace (d := d) k 2 u Ω) (c : ℝ) :
    wkpNormL2SqHalfSpace (d := d) k (fun x => c * u x) Ω =
      ‖c‖ₑ ^ (2 : ℕ) * wkpNormL2SqHalfSpace (d := d) k u Ω := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_const_smul (d := d) (interiorHalfSpace_isOpen hΩ) hu c

theorem wkpNormL2HalfSpace_const_smul
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu : MemWkpHalfSpace (d := d) k 2 u Ω) (c : ℝ) :
    wkpNormL2HalfSpace (d := d) k (fun x => c * u x) Ω =
      ‖c‖ₑ * wkpNormL2HalfSpace (d := d) k u Ω := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_const_smul (d := d) (interiorHalfSpace_isOpen hΩ) hu c

theorem wkpNormL2HalfSpace_le_wkpNormHalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormL2HalfSpace (d := d) k u Ω ≤
      wkpNormHalfSpace (d := d) k 2 u Ω := by
  unfold wkpNormL2HalfSpace wkpNormHalfSpace
  exact wkpNormL2_le_wkpNorm (d := d) hu

theorem wkpNormHalfSpace_le_sqrt_card_mul_wkpNormL2HalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormHalfSpace (d := d) k 2 u Ω ≤
      ENNReal.ofReal (Real.sqrt (multiIndexUpToOrderCard k d)) *
        wkpNormL2HalfSpace (d := d) k u Ω := by
  unfold wkpNormL2HalfSpace wkpNormHalfSpace
  exact wkpNorm_le_sqrt_card_mul_wkpNormL2 (d := d) hu

theorem wkpInnerL2HalfSpace_comm
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2HalfSpace (d := d) k u v Ω =
      wkpInnerL2HalfSpace (d := d) k v u Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_comm (d := d) k u v (interiorHalfSpace Ω)

theorem wkpInnerL2HalfSpace_self_nonneg
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    0 ≤ wkpInnerL2HalfSpace (d := d) k u u Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_self_nonneg (d := d) k u (interiorHalfSpace Ω)

theorem wkpInnerL2HalfSpace_add_left
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u₁ u₂ v : E → ℝ}
    (hu₁ : MemWkpHalfSpace (d := d) k 2 u₁ Ω)
    (hu₂ : MemWkpHalfSpace (d := d) k 2 u₂ Ω)
    (hv : MemWkpHalfSpace (d := d) k 2 v Ω) :
    wkpInnerL2HalfSpace (d := d) k (fun x => u₁ x + u₂ x) v Ω =
      wkpInnerL2HalfSpace (d := d) k u₁ v Ω +
        wkpInnerL2HalfSpace (d := d) k u₂ v Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_add_left (d := d) (interiorHalfSpace_isOpen hΩ)
    hu₁ hu₂ hv

theorem wkpInnerL2HalfSpace_smul_left
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (v : E → ℝ)
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) (c : ℝ) :
    wkpInnerL2HalfSpace (d := d) k (fun x => c * u x) v Ω =
      c * wkpInnerL2HalfSpace (d := d) k u v Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_smul_left (d := d) (interiorHalfSpace_isOpen hΩ)
    v hu c

theorem wkpNormL2SqHalfSpace_toReal_eq_wkpInnerL2HalfSpace_self
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    (wkpNormL2SqHalfSpace (d := d) k u Ω).toReal =
      wkpInnerL2HalfSpace (d := d) k u u Ω := by
  unfold wkpNormL2SqHalfSpace wkpInnerL2HalfSpace
  exact wkpNormL2Sq_toReal_eq_wkpInnerL2_self (d := d) hu

theorem wkpNormL2HalfSpace_sq_toReal_eq_wkpInnerL2HalfSpace_self
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    ((wkpNormL2HalfSpace (d := d) k u Ω).toReal) ^ 2 =
      wkpInnerL2HalfSpace (d := d) k u u Ω := by
  unfold wkpNormL2HalfSpace wkpInnerL2HalfSpace
  exact wkpNormL2_sq_toReal_eq_wkpInnerL2_self (d := d) hu

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
