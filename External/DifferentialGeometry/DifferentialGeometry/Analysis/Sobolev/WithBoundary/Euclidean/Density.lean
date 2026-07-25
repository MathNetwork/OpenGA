import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemWkpHalfSpace.exists_smooth_compactSupport_approx
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsHalfSpaceRelOpen Ω)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkpHalfSpace k p u Ω)
    (hu_compactSupport : HasCompactSupport u)
    (hu_supp : tsupport u ⊆ interiorHalfSpace Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        tsupport φ ⊆ interiorHalfSpace Ω ∧
        wkpNormHalfSpace k p (fun x => u x - φ x) Ω ≤ ENNReal.ofReal ε := by
  have hΩ_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  have hu' : MemWkp (d := d) k p u (interiorHalfSpace Ω) := hu
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_supp, hφ_norm⟩ :=
    MemWkp.exists_smooth_compactSupport_approx (d := d)
      hΩ_open k p hp_one hp_top hu' hu_compactSupport hu_supp ε hε
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_supp, ?_⟩
  change iteratedWeakSobolevNorm (d := d) k p (fun x => u x - φ x) (interiorHalfSpace Ω) ≤
    ENNReal.ofReal ε
  exact hφ_norm

theorem MemWkpHalfSpace.exists_smooth_compactSupport_approx_of_subset_openHalfSpace
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hsub : Ω ⊆ openHalfSpace)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkpHalfSpace k p u Ω)
    (hu_compactSupport : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧
        wkpNormHalfSpace k p (fun x => u x - φ x) Ω ≤ ENNReal.ofReal ε := by
  have hΩ : IsHalfSpaceRelOpen (d := d) Ω :=
    IsHalfSpaceRelOpen.of_isOpen_subset_open hΩ_open hsub
  have h_int_eq : interiorHalfSpace (d := d) Ω = Ω :=
    inter_eq_self_of_subset_left hsub
  have hu_supp' : tsupport u ⊆ interiorHalfSpace (d := d) Ω := by
    rw [h_int_eq]
    exact hu_supp
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_supp, hφ_norm⟩ :=
    MemWkpHalfSpace.exists_smooth_compactSupport_approx
      hΩ k p hp_one hp_top hu hu_compactSupport hu_supp' ε hε
  refine ⟨φ, hφ_smooth, hφ_compact, ?_, hφ_norm⟩
  rw [← h_int_eq]
  exact hφ_supp

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
