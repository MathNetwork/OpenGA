import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceInstance
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def closedHalfSpace : Set E := {y : E | 0 ≤ y 0}

def openHalfSpace : Set E := {y : E | 0 < y 0}

def boundaryHyperplane : Set E := {y : E | y 0 = 0}

@[simp] lemma closedHalfSpace_def :
    closedHalfSpace (d := d) = {y : E | 0 ≤ y 0} := rfl

@[simp] lemma openHalfSpace_def :
    openHalfSpace (d := d) = {y : E | 0 < y 0} := rfl

@[simp] lemma boundaryHyperplane_def :
    boundaryHyperplane (d := d) = {y : E | y 0 = 0} := rfl

theorem openHalfSpace_subset_closedHalfSpace :
    openHalfSpace (d := d) ⊆ closedHalfSpace := by
  intro y hy
  change (0 : ℝ) ≤ y 0
  exact le_of_lt hy

theorem closedHalfSpace_eq_union :
    closedHalfSpace (d := d) = openHalfSpace ∪ boundaryHyperplane := by
  ext y
  simp only [closedHalfSpace, openHalfSpace, boundaryHyperplane,
    mem_setOf_eq, mem_union]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq h.symm

omit [NeZero d] in
theorem isOpen_openHalfSpace [NeZero d] :
    IsOpen (openHalfSpace (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) := PiLp.continuous_apply 2 _ 0
  have heq : openHalfSpace (d := d) = (fun y : E => y 0) ⁻¹' Set.Ioi 0 := rfl
  rw [heq]
  exact hcont.isOpen_preimage _ isOpen_Ioi

omit [NeZero d] in
theorem isClosed_boundaryHyperplane [NeZero d] :
    IsClosed (boundaryHyperplane (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) := PiLp.continuous_apply 2 _ 0
  have heq : boundaryHyperplane (d := d) = (fun y : E => y 0) ⁻¹' {0} := rfl
  rw [heq]
  exact isClosed_singleton.preimage hcont

omit [NeZero d] in
theorem volume_boundaryHyperplane_eq_zero [NeZero d] :
    (volume : Measure E) (boundaryHyperplane (d := d)) = 0 := by
  classical
  set ker : Submodule ℝ E :=
    (EuclideanSpace.proj (0 : Fin d) :
      E →L[ℝ] ℝ).toLinearMap.ker with hker_def
  have hsubm :
      (boundaryHyperplane (d := d) : Set E) = (ker : Set E) := by
    ext y
    simp [hker_def, boundaryHyperplane, LinearMap.mem_ker,
      EuclideanSpace.proj]
  rw [hsubm]
  refine MeasureTheory.Measure.addHaar_submodule
    (μ := (volume : MeasureTheory.Measure E)) ker ?_
  intro hker_eq
  have h_in_top : EuclideanSpace.single (0 : Fin d) (1 : ℝ) ∈
      (⊤ : Submodule ℝ E) := Submodule.mem_top
  rw [← hker_eq] at h_in_top
  have h_proj_zero :
      (EuclideanSpace.proj (0 : Fin d) : E →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) = 0 := by
    have := h_in_top
    simp only [hker_def, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at this
    exact this
  have h_eval :
      (EuclideanSpace.proj (0 : Fin d) : E →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) =
      (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) 0 := rfl
  have h_one : (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) 0 = 1 := by
    rw [show (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) =
          PiLp.single 2 (0 : Fin d) (1 : ℝ) from rfl]
    rw [PiLp.single_apply]
    simp
  rw [h_one] at h_eval
  exact one_ne_zero (h_proj_zero.symm.trans h_eval).symm

def interiorHalfSpace (Ω : Set E) : Set E := Ω ∩ openHalfSpace

@[simp] lemma interiorHalfSpace_def (Ω : Set E) :
    interiorHalfSpace (d := d) Ω = Ω ∩ openHalfSpace := rfl

theorem interiorHalfSpace_subset (Ω : Set E) :
    interiorHalfSpace (d := d) Ω ⊆ Ω := inter_subset_left

theorem interiorHalfSpace_subset_openHalfSpace (Ω : Set E) :
    interiorHalfSpace (d := d) Ω ⊆ openHalfSpace := inter_subset_right

def IsHalfSpaceRelOpen (Ω : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ Ω = U ∩ closedHalfSpace

theorem IsHalfSpaceRelOpen.of_isOpen_subset_open
    {Ω : Set E} (hΩ : IsOpen Ω) (hsub : Ω ⊆ openHalfSpace) :
    IsHalfSpaceRelOpen (d := d) Ω := by
  refine ⟨Ω, hΩ, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    refine ⟨hy, ?_⟩
    exact openHalfSpace_subset_closedHalfSpace (hsub hy)
  · intro y ⟨hy, _⟩
    exact hy

theorem IsHalfSpaceRelOpen.subset_closedHalfSpace
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω ⊆ closedHalfSpace := by
  obtain ⟨U, _hU, hU_eq⟩ := hΩ
  rw [hU_eq]
  exact inter_subset_right

theorem interiorHalfSpace_eq_inter_openHalfSpace
    {Ω : Set E} {U : Set E}
    (hU_eq : Ω = U ∩ closedHalfSpace) :
    interiorHalfSpace (d := d) Ω = U ∩ openHalfSpace := by
  unfold interiorHalfSpace
  rw [hU_eq]
  ext y
  simp only [mem_inter_iff, closedHalfSpace, openHalfSpace, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hU, _⟩, h_open⟩
    exact ⟨hU, h_open⟩
  · rintro ⟨hU, h_open⟩
    exact ⟨⟨hU, le_of_lt h_open⟩, h_open⟩

omit [NeZero d] in
theorem interiorHalfSpace_isOpen [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    IsOpen (interiorHalfSpace (d := d) Ω) := by
  obtain ⟨U, hU, hU_eq⟩ := hΩ
  rw [interiorHalfSpace_eq_inter_openHalfSpace hU_eq]
  exact hU.inter (isOpen_openHalfSpace (d := d))

theorem symmDiff_interiorHalfSpace_subset_boundaryHyperplane
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω \ interiorHalfSpace Ω ⊆ boundaryHyperplane := by
  intro y ⟨hy_in, hy_notIn⟩
  unfold interiorHalfSpace at hy_notIn
  simp only [mem_inter_iff, openHalfSpace, mem_setOf_eq, not_and, not_lt]
    at hy_notIn
  have h_le : y 0 ≤ 0 := hy_notIn hy_in
  have h_ge : 0 ≤ y 0 := hΩ.subset_closedHalfSpace hy_in
  exact le_antisymm h_le h_ge

omit [NeZero d] in
theorem ae_eq_interiorHalfSpace [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω =ᵐ[(volume : Measure E)] interiorHalfSpace (d := d) Ω := by
  have h_diff1 : (volume : Measure E) (Ω \ interiorHalfSpace Ω) = 0 := by
    have hsub :=
      symmDiff_interiorHalfSpace_subset_boundaryHyperplane (d := d) hΩ
    have h_zero := volume_boundaryHyperplane_eq_zero (d := d)
    exact MeasureTheory.measure_mono_null hsub h_zero
  have h_diff2 : (volume : Measure E) (interiorHalfSpace Ω \ Ω) = 0 := by
    have h_empty : interiorHalfSpace Ω \ Ω = ∅ := by
      ext y
      simp only [mem_diff, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hy
      exact interiorHalfSpace_subset Ω hy
    rw [h_empty]
    exact measure_empty
  exact (MeasureTheory.ae_eq_set).mpr ⟨h_diff1, h_diff2⟩

omit [NeZero d] in
theorem volume_restrict_interiorHalfSpace_eq [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    (volume : Measure E).restrict Ω =
      (volume : Measure E).restrict (interiorHalfSpace (d := d) Ω) :=
  MeasureTheory.Measure.restrict_congr_set (ae_eq_interiorHalfSpace hΩ)

def MemWkpHalfSpace (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : Prop :=
  MemWkp (d := d) k p u (interiorHalfSpace Ω)

@[simp] lemma MemWkpHalfSpace_def
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    MemWkpHalfSpace (d := d) k p u Ω ↔
      MemWkp (d := d) k p u (interiorHalfSpace Ω) := Iff.rfl

theorem MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hsub : Ω ⊆ openHalfSpace) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkp (d := d) k p u Ω := by
  unfold MemWkpHalfSpace interiorHalfSpace
  rw [show Ω ∩ openHalfSpace = Ω from inter_eq_self_of_subset_left hsub]

theorem MemWkpHalfSpace.zero_iff_memLp
    {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ} :
    MemWkpHalfSpace (d := d) 0 p u Ω ↔
      MemLp u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) :=
  MemWkp.zero_iff_memLp

omit [NeZero d] in
theorem MemWkpHalfSpace.zero_iff_memLp_of_relOpen [NeZero d]
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) {u : E → ℝ} :
    MemWkpHalfSpace (d := d) 0 p u Ω ↔
      MemLp u p ((volume : Measure E).restrict Ω) := by
  rw [MemWkpHalfSpace.zero_iff_memLp,
      ← volume_restrict_interiorHalfSpace_eq hΩ]

theorem MemWkpHalfSpace.le_succ
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) (k + 1) p u Ω) :
    MemWkpHalfSpace (d := d) k p u Ω :=
  MemWkp.le_succ h

theorem MemWkpHalfSpace.le_of_le
    {k k' : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hk : k ≤ k') (h : MemWkpHalfSpace (d := d) k' p u Ω) :
    MemWkpHalfSpace (d := d) k p u Ω :=
  MemWkp.le_of_le hk h

theorem MemWkpHalfSpace.memLp
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    MemLp u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) :=
  MemWkp.memLp h

omit [NeZero d] in
theorem MemWkpHalfSpace.memLp_of_relOpen [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    MemLp u p ((volume : Measure E).restrict Ω) := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ]
  exact h.memLp

omit [NeZero d] in
theorem MemWkpHalfSpace_zero_fun [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    MemWkpHalfSpace (d := d) k p (fun _ : E => (0 : ℝ)) Ω :=
  MemWkp_zero_fun (d := d) hp (interiorHalfSpace_isOpen hΩ)

omit [NeZero d] in
theorem MemWkpHalfSpace.add [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => u x + v x) Ω :=
  MemWkp.add (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

omit [NeZero d] in
theorem MemWkpHalfSpace.const_smul [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) (c : ℝ) :
    MemWkpHalfSpace (d := d) k p (fun x => c * u x) Ω :=
  MemWkp.const_smul (d := d) hp (interiorHalfSpace_isOpen hΩ) hu c

omit [NeZero d] in
theorem MemWkpHalfSpace.neg [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => - u x) Ω :=
  MemWkp.neg (d := d) hp (interiorHalfSpace_isOpen hΩ) hu

omit [NeZero d] in
theorem MemWkpHalfSpace.sub [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => u x - v x) Ω :=
  MemWkp.sub (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

omit [NeZero d] in
theorem MemWkpHalfSpace_congr_ae [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict (interiorHalfSpace Ω)] v) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkpHalfSpace (d := d) k p v Ω :=
  MemWkp_congr_ae (d := d) hp (interiorHalfSpace_isOpen hΩ) huv

omit [NeZero d] in
theorem MemWkpHalfSpace_congr_ae_of_carrier [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict Ω] v) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkpHalfSpace (d := d) k p v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact MemWkpHalfSpace_congr_ae (d := d) hp hΩ huv

def wkpNormHalfSpace (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := d) k p u (interiorHalfSpace Ω)

@[simp] lemma wkpNormHalfSpace_def
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNormHalfSpace (d := d) k p u Ω =
      iteratedWeakSobolevNorm (d := d) k p u (interiorHalfSpace Ω) := rfl

theorem wkpNormHalfSpace_zero
    (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNormHalfSpace (d := d) 0 p u Ω =
      eLpNorm u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) :=
  wkpNorm_zero (d := d) p u (interiorHalfSpace Ω)

omit [NeZero d] in
theorem wkpNormHalfSpace_zero_of_relOpen [NeZero d]
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (u : E → ℝ) :
    wkpNormHalfSpace (d := d) 0 p u Ω =
      eLpNorm u p ((volume : Measure E).restrict Ω) := by
  rw [wkpNormHalfSpace_zero, ← volume_restrict_interiorHalfSpace_eq hΩ]

omit [NeZero d] in
theorem wkpNormHalfSpace_zero_fun_zero [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormHalfSpace (d := d) k p (fun _ : E => (0 : ℝ)) Ω = 0 :=
  wkpNorm_zero_fun_zero (d := d) hp (interiorHalfSpace_isOpen hΩ)

theorem wkpNormHalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    wkpNormHalfSpace (d := d) k p u Ω < (⊤ : ℝ≥0∞) :=
  wkpNorm_lt_top_of_memWkp h

omit [NeZero d] in
theorem wkpNormHalfSpace_add_le [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    wkpNormHalfSpace (d := d) k p (fun x => u x + v x) Ω ≤
      wkpNormHalfSpace (d := d) k p u Ω +
        wkpNormHalfSpace (d := d) k p v Ω :=
  wkpNorm_add_le (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

omit [NeZero d] in
theorem wkpNormHalfSpace_const_smul [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) (c : ℝ) :
    wkpNormHalfSpace (d := d) k p (fun x => c * u x) Ω =
      ‖c‖ₑ * wkpNormHalfSpace (d := d) k p u Ω :=
  wkpNorm_const_smul (d := d) hp (interiorHalfSpace_isOpen hΩ) hu c

omit [NeZero d] in
theorem fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ 1 u) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1))
      u (interiorHalfSpace Ω) :=
  DeGiorgi.HasWeakPartialDeriv.of_contDiff (interiorHalfSpace_isOpen hΩ)
    hu_smooth

theorem fderiv_memLp_of_smooth_compactSupport
    {p : ℝ≥0∞} {Ω : Set E} (_hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_supp : HasCompactSupport u) (i : Fin d) :
    MemLp (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) p
      ((volume : Measure E).restrict (interiorHalfSpace Ω)) := by
  have h_smooth : ContDiff ℝ ∞
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
    have h_fderiv : ContDiff ℝ ∞ (fun x => fderiv ℝ u x) :=
      hu_smooth.fderiv_right (m := (∞ : WithTop ℕ∞)) (by
        rw [ENat.coe_top_add_one])
    exact h_fderiv.clm_apply contDiff_const
  have h_supp : HasCompactSupport
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_global : MemLp
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) p volume :=
    h_smooth.continuous.memLp_of_hasCompactSupport h_supp
  exact h_global.restrict (interiorHalfSpace Ω)

theorem memLp_of_smooth_compactSupport
    {p : ℝ≥0∞} {Ω : Set E} (_hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_supp : HasCompactSupport u) :
    MemLp u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) := by
  have h_global : MemLp u p (volume : Measure E) :=
    hu_smooth.continuous.memLp_of_hasCompactSupport hu_supp
  exact h_global.restrict (interiorHalfSpace Ω)

theorem memW1p_of_smooth_compactSupport_interiorHalfSpace
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_supp : HasCompactSupport u) :
    DeGiorgi.MemW1p p u (interiorHalfSpace Ω) := by
  refine ⟨memLp_of_smooth_compactSupport hΩ hu_smooth hu_supp, ?_⟩
  intro i
  refine ⟨fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1),
    fderiv_memLp_of_smooth_compactSupport hΩ hu_smooth hu_supp i, ?_⟩
  exact fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace hΩ
    (hu_smooth.of_le (by norm_cast)) i

theorem partialDerivWithin_interiorHalfSpace_eq_partialDeriv
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) {y : E}
    (hy : y ∈ interiorHalfSpace Ω) :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin
        (interiorHalfSpace Ω) i u y =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
        i u y :=
  DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen
    (interiorHalfSpace_isOpen hΩ) hy

section EuclideanHalfSpaceChartTargets

variable {n : ℕ} [NeZero n]

theorem range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace :
    Set.range (modelWithCornersEuclideanHalfSpace n :
        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) =
      closedHalfSpace (d := n) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  ext y
  simp [closedHalfSpace]

theorem extChartAt_target_isHalfSpaceRelOpen
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] (α : M) :
    IsHalfSpaceRelOpen (d := n)
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target := by
  refine ⟨(modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace n) α).target, ?_, ?_⟩
  · exact (chartAt (EuclideanHalfSpace n) α).open_target.preimage
      (modelWithCornersEuclideanHalfSpace n).continuous_symm
  · rw [extChartAt_target,
      range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace]

end EuclideanHalfSpaceChartTargets

section UsabilityCheck

variable {n : ℕ} [NeZero n]

example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    (α : M) (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpHalfSpace (d := n) k p (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target :=
  MemWkpHalfSpace_zero_fun (d := n) hp
    (extChartAt_target_isHalfSpaceRelOpen α)

example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    (α : M) (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemWkpHalfSpace (d := n) k p u
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target)
    (hv : MemWkpHalfSpace (d := n) k p v
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target) :
    MemWkpHalfSpace (d := n) k p (fun x => u x + v x)
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target :=
  MemWkpHalfSpace.add (d := n) hp
    (extChartAt_target_isHalfSpaceRelOpen α) hu hv

example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    (α : M) {p : ℝ≥0∞}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_smooth : ContDiff ℝ ∞ u) (hu_supp : HasCompactSupport u) :
    DeGiorgi.MemW1p p u
      (interiorHalfSpace (d := n)
        (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target) :=
  memW1p_of_smooth_compactSupport_interiorHalfSpace
    (extChartAt_target_isHalfSpaceRelOpen α) hu_smooth hu_supp

end UsabilityCheck

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
