import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapStep
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Topology Function
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open DifferentialGeometry.Analysis.Sobolev.NirenbergIteration
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section GenericArithmetic

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

private theorem exists_uniform_iteratedFDeriv_bound_of_smooth_on_compact
    {η : EE → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {S : Set EE} (hS : IsCompact S) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ j ≤ m, ‖iteratedFDeriv ℝ j η x‖ ≤ C := by
  classical
  have h_per_j : ∀ j : ℕ, ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ x ∈ S, ‖iteratedFDeriv ℝ j η x‖ ≤ Cj := by
    intro j
    have h_cont : Continuous (fun x : EE => iteratedFDeriv ℝ j η x) := by
      have h := hη.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
      simpa using h.continuous
    obtain ⟨Cj, hCj⟩ := hS.exists_bound_of_continuousOn h_cont.continuousOn
    refine ⟨max 0 Cj, le_max_left _ _, ?_⟩
    intro x hx
    exact (hCj x hx).trans (le_max_right _ _)
  let Cj : ℕ → ℝ := fun j => Classical.choose (h_per_j j)
  have hCj_nn : ∀ j, 0 ≤ Cj j := fun j => (Classical.choose_spec (h_per_j j)).1
  have hCj_bound : ∀ j, ∀ x ∈ S, ‖iteratedFDeriv ℝ j η x‖ ≤ Cj j := fun j =>
    (Classical.choose_spec (h_per_j j)).2
  have h_nonempty : (Finset.range (m + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let C : ℝ := (Finset.range (m + 1)).sup' h_nonempty Cj
  have hC_ge : ∀ j ∈ Finset.range (m + 1), Cj j ≤ C := fun j hj =>
    Finset.le_sup' Cj hj
  have hC_nn : 0 ≤ C :=
    le_trans (hCj_nn 0) (hC_ge 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _)))
  refine ⟨C, hC_nn, ?_⟩
  intro x hx j hj
  have hj_mem : j ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  exact le_trans (hCj_bound j x hx) (hC_ge j hj_mem)

omit [NeZero d] in

private theorem exists_uniform_iteratedFDeriv_bound_on_precompact_open
    {η : EE → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {Ω : Set EE} (hΩ_compact_closure : IsCompact (closure Ω)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C := by
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_on_compact (d := d) hη
      hΩ_compact_closure m
  refine ⟨C, hC_nn, ?_⟩
  intro j hj x hx
  exact hC_bound x (subset_closure hx) j hj

omit [NeZero d] in

theorem memWkp_finset_sum
    {k : ℕ} {Ω : Set EE} (hΩ : IsOpen Ω)
    {ι : Type*} (S : Finset ι) (F : ι → EE → ℝ)
    (hF : ∀ a ∈ S, MemWkp (d := d) k 2 (F a) Ω) :
    MemWkp (d := d) k 2 (fun x => ∑ a ∈ S, F a x) Ω := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
  | insert a S ha ih =>
      have hF_a : MemWkp (d := d) k 2 (F a) Ω :=
        hF a (Finset.mem_insert_self a S)
      have hF_S : ∀ b ∈ S, MemWkp (d := d) k 2 (F b) Ω :=
        fun b hb => hF b (Finset.mem_insert_of_mem hb)
      have h_sum : MemWkp (d := d) k 2 (fun x => ∑ b ∈ S, F b x) Ω := ih hF_S
      have h_add :=
        MemWkp.add (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hF_a h_sum
      have h_eq :
          (fun x => F a x + ∑ b ∈ S, F b x) =
            (fun x => ∑ b ∈ insert a S, F b x) := by
        funext x
        rw [Finset.sum_insert ha]
      rwa [h_eq] at h_add

omit [NeZero d] in

theorem wkpNorm_finset_sum_le
    {k : ℕ} {Ω : Set EE} (hΩ : IsOpen Ω)
    {ι : Type*} (S : Finset ι) (F : ι → EE → ℝ)
    (hF : ∀ a ∈ S, MemWkp (d := d) k 2 (F a) Ω)
    (κ : ι → ℝ) (hκ_nn : ∀ a ∈ S, 0 ≤ κ a) (D : ℝ≥0∞)
    (hbound : ∀ a ∈ S,
      iteratedWeakSobolevNorm (d := d) k 2 (F a) Ω ≤ ENNReal.ofReal (κ a) * D) :
    iteratedWeakSobolevNorm (d := d) k 2 (fun x => ∑ a ∈ S, F a x) Ω ≤
      ENNReal.ofReal (∑ a ∈ S, κ a) * D := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [wkpNorm_zero_fun_zero (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ,
        ENNReal.ofReal_zero, zero_mul]
  | insert a S ha ih =>
      have hF_a : MemWkp (d := d) k 2 (F a) Ω :=
        hF a (Finset.mem_insert_self a S)
      have hF_S : ∀ b ∈ S, MemWkp (d := d) k 2 (F b) Ω :=
        fun b hb => hF b (Finset.mem_insert_of_mem hb)
      have hκ_S : ∀ b ∈ S, 0 ≤ κ b :=
        fun b hb => hκ_nn b (Finset.mem_insert_of_mem hb)
      have hbound_S : ∀ b ∈ S,
          iteratedWeakSobolevNorm (d := d) k 2 (F b) Ω ≤ ENNReal.ofReal (κ b) * D :=
        fun b hb => hbound b (Finset.mem_insert_of_mem hb)
      have h_sum_mem : MemWkp (d := d) k 2 (fun x => ∑ b ∈ S, F b x) Ω :=
        memWkp_finset_sum (d := d) hΩ S F hF_S
      have h_ih := ih hF_S hκ_S hbound_S
      have h_eq :
          (fun x => ∑ b ∈ insert a S, F b x) =
            (fun x => F a x + ∑ b ∈ S, F b x) := by
        funext x
        rw [Finset.sum_insert ha]
      rw [h_eq]
      have h_tri :=
        wkpNorm_add_le (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hF_a h_sum_mem
      refine h_tri.trans ?_
      have h_terms :
          iteratedWeakSobolevNorm (d := d) k 2 (F a) Ω +
              iteratedWeakSobolevNorm (d := d) k 2 (fun x => ∑ b ∈ S, F b x) Ω ≤
            ENNReal.ofReal (κ a) * D + ENNReal.ofReal (∑ b ∈ S, κ b) * D :=
        add_le_add (hbound a (Finset.mem_insert_self a S)) h_ih
      refine h_terms.trans ?_
      rw [Finset.sum_insert ha,
        ENNReal.ofReal_add (hκ_nn a (Finset.mem_insert_self a S))
          (Finset.sum_nonneg hκ_S),
        add_mul]

omit [NeZero d] in
theorem classicalPartial_memWkp_of_memWkp_succ
    {k : ℕ} {Ω : Set EE} (hΩ : IsOpen Ω)
    {ψ : EE → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ : MemWkp (d := d) (k + 1) 2 ψ Ω) (l : Fin d) :
    MemWkp (d := d) k 2
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) Ω := by
  classical
  have hψ_W1 : DeGiorgi.MemW1p (d := d) 2 ψ Ω := hψ.memW1p
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hψ_smooth hψ_W1 l
  have h_chosen_mem : MemWkp (d := d) k 2 (chosenWeakPartial' 2 l ψ Ω) Ω :=
    hψ.chosenWeakPartial_mem l
  exact (MemWkp_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae).mp
    h_chosen_mem

omit [NeZero d] in
theorem wkpNorm_classicalPartial_le
    {k : ℕ} {Ω : Set EE} (hΩ : IsOpen Ω)
    {ψ : EE → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ : MemWkp (d := d) (k + 1) 2 ψ Ω) (l : Fin d) :
    iteratedWeakSobolevNorm (d := d) k 2
        (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) 2 ψ Ω := by
  classical
  have hψ_W1 : DeGiorgi.MemW1p (d := d) 2 ψ Ω := hψ.memW1p
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hψ_smooth hψ_W1 l
  rw [← wkpNorm_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae]
  exact wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := d) k hΩ ψ l

private theorem exists_wkpNorm_smul_smooth_le_on_precompact
    (k : ℕ) {Ω : Set EE} (hΩ_open : IsOpen Ω)
    (hΩ_compact_closure : IsCompact (closure Ω))
    {η : EE → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : EE → ℝ}, MemWkp (d := d) k 2 u Ω →
      MemWkp (d := d) k 2 (fun x => η x * u x) Ω ∧
        iteratedWeakSobolevNorm (d := d) k 2 (fun x => η x * u x) Ω ≤
          ENNReal.ofReal K * iteratedWeakSobolevNorm (d := d) k 2 u Ω := by
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_on_precompact_open (d := d) hη_smooth
      hΩ_compact_closure k
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
      hΩ_open hη_smooth hC_nn hC_bound
  refine ⟨K, hK_pos.le, fun {u} hu => ⟨?_, hK_bound hu⟩⟩
  exact MemWkp.smul_smooth_bounded (d := d) k (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ_open hη_smooth hC_bound hu

end GenericArithmetic

section ArithmeticHeadline

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1600000 in

theorem perturbedSource_memWkp_of_source_memWkp
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE)) (m : ℕ)
    {Ω : Set EE} (hΩ_open : IsOpen Ω) (hΩ_compact_closure : IsCompact (closure Ω))
    (l : Fin d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u f : EE → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      ContDiff ℝ (⊤ : ℕ∞) f →
      MemWkp (d := d) (m + 2) 2 u Ω → MemWkp (d := d) (m + 1) 2 f Ω →
      MemWkp (d := d) m 2 (perturbedSource (d := d) B u f l) Ω ∧
        iteratedWeakSobolevNorm (d := d) m 2 (perturbedSource (d := d) B u f l) Ω ≤
          ENNReal.ofReal K *
            (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
              iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := by
  classical
  set dlc : EE → ℝ :=
    fun x => (fderiv ℝ B.c x) (EuclideanSpace.single l 1) with hdlc_def
  have hdlc_smooth : ContDiff ℝ (⊤ : ℕ∞) dlc :=
    contDiff_partial_eta (d := d) B.smooth_c l
  obtain ⟨K_c, hK_c_nn, hK_c_bound⟩ :=
    exists_wkpNorm_smul_smooth_le_on_precompact (d := d) m hΩ_open
      hΩ_compact_closure hdlc_smooth
  have h_dla_smooth : ∀ i j : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1)) :=
    fun i j => contDiff_partial_eta (d := d) (B.contDiff_a i j) l
  have h_pair_data : ∀ i j : Fin d, ∃ K' : ℝ, 0 ≤ K' ∧
      ∀ {w : EE → ℝ}, MemWkp (d := d) (m + 1) 2 w Ω →
        MemWkp (d := d) (m + 1) 2
            (fun y : EE => (fderiv ℝ (fun z : EE => B.a z i j) y)
              (EuclideanSpace.single l 1) * w y) Ω ∧
          iteratedWeakSobolevNorm (d := d) (m + 1) 2
              (fun y : EE => (fderiv ℝ (fun z : EE => B.a z i j) y)
                (EuclideanSpace.single l 1) * w y) Ω ≤
            ENNReal.ofReal K' * iteratedWeakSobolevNorm (d := d) (m + 1) 2 w Ω := fun i j =>
    exists_wkpNorm_smul_smooth_le_on_precompact (d := d) (m + 1) hΩ_open
      hΩ_compact_closure (h_dla_smooth i j)
  choose K_pair hK_pair_nn hK_pair_bound using h_pair_data
  set K_div : ℝ := ∑ i : Fin d, ∑ j : Fin d, K_pair i j with hKdiv_def
  have hK_div_nn : 0 ≤ K_div :=
    Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hK_pair_nn i j))
  refine ⟨K_c + K_div + 1, by positivity, ?_⟩
  intro u f hu_smooth _hu_cpt hf_smooth hu_memWkp hf_memWkp
  set D : ℝ≥0∞ :=
    iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω + iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω with hD_def
  set termA : EE → ℝ :=
    fun x => (fderiv ℝ f x) (EuclideanSpace.single l 1) with hA_def
  have hA_mem : MemWkp (d := d) m 2 termA Ω :=
    classicalPartial_memWkp_of_memWkp_succ (d := d) hΩ_open hf_smooth
      hf_memWkp l
  have hA_norm : iteratedWeakSobolevNorm (d := d) m 2 termA Ω ≤ D := by
    have h := wkpNorm_classicalPartial_le (d := d) hΩ_open hf_smooth hf_memWkp l
    exact h.trans le_self_add
  set termB : EE → ℝ := fun x => dlc x * u x with hB_def
  have hu_m : MemWkp (d := d) m 2 u Ω :=
    MemWkp.le_of_le (by omega) hu_memWkp
  have hB_mem : MemWkp (d := d) m 2 termB Ω := (hK_c_bound hu_m).1
  have hB_norm :
      iteratedWeakSobolevNorm (d := d) m 2 termB Ω ≤ ENNReal.ofReal K_c * D := by
    refine (hK_c_bound hu_m).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h_mono : iteratedWeakSobolevNorm (d := d) m 2 u Ω ≤ iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω :=
      wkpNorm_mono_order (d := d) (by omega) u Ω
    exact h_mono.trans le_add_self
  have h_diu_mem : ∀ i : Fin d, MemWkp (d := d) (m + 1) 2
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) Ω := fun i =>
    classicalPartial_memWkp_of_memWkp_succ (d := d) hΩ_open hu_smooth
      hu_memWkp i
  have h_diu_norm : ∀ i : Fin d,
      iteratedWeakSobolevNorm (d := d) (m + 1) 2
          (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) Ω ≤
        iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := fun i =>
    wkpNorm_classicalPartial_le (d := d) hΩ_open hu_smooth hu_memWkp i
  have h_pair_mem : ∀ i j : Fin d, MemWkp (d := d) (m + 1) 2
      (fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) Ω :=
    fun i j => (hK_pair_bound i j (h_diu_mem i)).1
  have h_pair_norm : ∀ i j : Fin d,
      iteratedWeakSobolevNorm (d := d) (m + 1) 2
          (fun y : EE =>
            (fderiv ℝ (fun z : EE => B.a z i j) y)
                (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) Ω ≤
        ENNReal.ofReal (K_pair i j) * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := by
    intro i j
    refine (hK_pair_bound i j (h_diu_mem i)).2.trans ?_
    exact mul_le_mul_of_nonneg_left (h_diu_norm i) (by positivity)
  set termC_summand : Fin d → Fin d → EE → ℝ :=
    fun i j x =>
      (fderiv ℝ (fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single j 1) with hCsum_def
  have hCsum_mem : ∀ i j : Fin d, MemWkp (d := d) m 2 (termC_summand i j) Ω := by
    intro i j
    have h_prod_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : EE =>
          (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
      (h_dla_smooth i j).mul (contDiff_partial_eta (d := d) hu_smooth i)
    exact classicalPartial_memWkp_of_memWkp_succ (d := d) hΩ_open
      h_prod_smooth (h_pair_mem i j) j
  have hCsum_norm : ∀ i j : Fin d,
      iteratedWeakSobolevNorm (d := d) m 2 (termC_summand i j) Ω ≤
        ENNReal.ofReal (K_pair i j) * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := by
    intro i j
    have h_prod_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : EE =>
          (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
      (h_dla_smooth i j).mul (contDiff_partial_eta (d := d) hu_smooth i)
    have h_partial_le := wkpNorm_classicalPartial_le (d := d) hΩ_open
      h_prod_smooth (h_pair_mem i j) j
    exact h_partial_le.trans (h_pair_norm i j)
  set termC_row : Fin d → EE → ℝ :=
    fun i x => ∑ j : Fin d, termC_summand i j x with hCrow_def
  have hCrow_mem : ∀ i : Fin d, MemWkp (d := d) m 2 (termC_row i) Ω := fun i =>
    memWkp_finset_sum (d := d) hΩ_open Finset.univ (termC_summand i)
      (fun j _ => hCsum_mem i j)
  have hCrow_norm : ∀ i : Fin d,
      iteratedWeakSobolevNorm (d := d) m 2 (termC_row i) Ω ≤
        ENNReal.ofReal (∑ j : Fin d, K_pair i j) *
          iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := fun i =>
    wkpNorm_finset_sum_le (d := d) hΩ_open Finset.univ (termC_summand i)
      (fun j _ => hCsum_mem i j) (fun j => K_pair i j)
      (fun j _ => hK_pair_nn i j) (iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω)
      (fun j _ => hCsum_norm i j)
  set termC : EE → ℝ := fun x => ∑ i : Fin d, termC_row i x with hC_def
  have hC_mem : MemWkp (d := d) m 2 termC Ω :=
    memWkp_finset_sum (d := d) hΩ_open Finset.univ termC_row
      (fun i _ => hCrow_mem i)
  have hC_norm :
      iteratedWeakSobolevNorm (d := d) m 2 termC Ω ≤
        ENNReal.ofReal K_div * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := by
    have h := wkpNorm_finset_sum_le (d := d) hΩ_open Finset.univ termC_row
      (fun i _ => hCrow_mem i) (fun i => ∑ j : Fin d, K_pair i j)
      (fun i _ => Finset.sum_nonneg (fun j _ => hK_pair_nn i j))
      (iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) (fun i _ => hCrow_norm i)
    rwa [hKdiv_def]
  have h_pert_eq :
      perturbedSource (d := d) B u f l =
        (fun x => (termA x - termB x) + termC x) := by
    funext x
    unfold perturbedSource
    rfl
  have h_AB_mem : MemWkp (d := d) m 2 (fun x => termA x - termB x) Ω :=
    MemWkp.sub (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hA_mem hB_mem
  have h_pert_mem : MemWkp (d := d) m 2 (perturbedSource (d := d) B u f l) Ω := by
    rw [h_pert_eq]
    exact MemWkp.add (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_AB_mem
      hC_mem
  refine ⟨h_pert_mem, ?_⟩
  rw [h_pert_eq]
  have h_tri₁ :=
    wkpNorm_add_le (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_AB_mem
      hC_mem
  have h_AB_eq : (fun x => termA x - termB x) =
      (fun x => termA x + (fun y => - termB y) x) := by
    funext x; ring
  have hnegB_mem : MemWkp (d := d) m 2 (fun y => - termB y) Ω :=
    MemWkp.neg (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hB_mem
  have h_negB_norm :
      iteratedWeakSobolevNorm (d := d) m 2 (fun y => - termB y) Ω =
        iteratedWeakSobolevNorm (d := d) m 2 termB Ω := by
    have h_neg_eq : (fun y => - termB y) = (fun y => (-1 : ℝ) * termB y) := by
      funext y; ring
    rw [h_neg_eq,
      wkpNorm_const_smul (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
        hB_mem (-1)]
    simp
  have h_tri₂ :
      iteratedWeakSobolevNorm (d := d) m 2 (fun x => termA x - termB x) Ω ≤
        iteratedWeakSobolevNorm (d := d) m 2 termA Ω + iteratedWeakSobolevNorm (d := d) m 2 termB Ω := by
    have h := wkpNorm_add_le (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
      hA_mem hnegB_mem
    rw [← h_AB_eq, h_negB_norm] at h
    exact h
  have h_combine :
      iteratedWeakSobolevNorm (d := d) m 2 (fun x => (termA x - termB x) + termC x) Ω ≤
        (iteratedWeakSobolevNorm (d := d) m 2 termA Ω + iteratedWeakSobolevNorm (d := d) m 2 termB Ω) +
          iteratedWeakSobolevNorm (d := d) m 2 termC Ω :=
    h_tri₁.trans (add_le_add h_tri₂ le_rfl)
  refine h_combine.trans ?_
  have hA_final : iteratedWeakSobolevNorm (d := d) m 2 termA Ω ≤ ENNReal.ofReal 1 * D := by
    rw [ENNReal.ofReal_one, one_mul]; exact hA_norm
  have hC_final : iteratedWeakSobolevNorm (d := d) m 2 termC Ω ≤ ENNReal.ofReal K_div * D := by
    refine hC_norm.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hD_def]; exact le_add_self
  have h_sum_le :
      (iteratedWeakSobolevNorm (d := d) m 2 termA Ω + iteratedWeakSobolevNorm (d := d) m 2 termB Ω) +
          iteratedWeakSobolevNorm (d := d) m 2 termC Ω ≤
        (ENNReal.ofReal 1 * D + ENNReal.ofReal K_c * D) +
          ENNReal.ofReal K_div * D :=
    add_le_add (add_le_add hA_final hB_norm) hC_final
  refine h_sum_le.trans ?_
  rw [← add_mul, ← add_mul,
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hK_c_nn,
    ← ENNReal.ofReal_add (by positivity) hK_div_nn]
  refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (zero_le _)
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  ring

end ArithmeticHeadline

section IteratedSource

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

noncomputable def iteratedPerturbedSource
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE)) :
    ∀ (m : ℕ), (EE → ℝ) → (EE → ℝ) → (Fin m → Fin d) → EE → ℝ
  | 0,     _, f, _   => f
  | m + 1, u, f, idx =>
      iteratedPerturbedSource B m
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single (idx 0) 1))
        (perturbedSource (d := d) B u f (idx 0))
        (fun i : Fin m => idx i.succ)

@[simp] theorem iteratedPerturbedSource_zero
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    (u f : EE → ℝ) (idx : Fin 0 → Fin d) :
    iteratedPerturbedSource (d := d) B 0 u f idx = f := rfl

theorem iteratedPerturbedSource_succ
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    (m : ℕ) (u f : EE → ℝ) (idx : Fin (m + 1) → Fin d) :
    iteratedPerturbedSource (d := d) B (m + 1) u f idx =
      iteratedPerturbedSource (d := d) B m
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single (idx 0) 1))
        (perturbedSource (d := d) B u f (idx 0))
        (fun i : Fin m => idx i.succ) := rfl

theorem contDiff_perturbedSource'
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    {u f : EE → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (l : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (perturbedSource (d := d) B u f l) := by
  unfold perturbedSource
  have h_dlf : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EE => (fderiv ℝ f x) (EuclideanSpace.single l 1)) :=
    contDiff_partial_eta (d := d) hf l
  have h_dlc : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EE => (fderiv ℝ B.c x) (EuclideanSpace.single l 1)) :=
    contDiff_partial_eta (d := d) B.smooth_c l
  have h_dlc_u : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EE => (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x) :=
    h_dlc.mul hu
  refine (h_dlf.sub h_dlc_u).add ?_
  refine ContDiff.sum ?_
  intro i _
  refine ContDiff.sum ?_
  intro j _
  have h_dla : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1)) :=
    contDiff_partial_eta (d := d) (B.contDiff_a i j) l
  have h_diu : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EE => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    contDiff_partial_eta (d := d) hu i
  exact contDiff_partial_eta (d := d) (h_dla.mul h_diu) j

theorem iterated_partial_isSmoothWeakSolution
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    (m : ℕ) :
    ∀ {u f : EE → ℝ}, B.IsSmoothWeakSolution u f → ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ (idx : Fin m → Fin d),
        B.IsSmoothWeakSolution
          (iterClassicalPartial (d := d) m idx u)
          (iteratedPerturbedSource (d := d) B m u f idx) := by
  induction m with
  | zero =>
      intro u f h_weak _hf idx
      simpa [iterClassicalPartial_zero, iteratedPerturbedSource_zero] using h_weak
  | succ m ih =>
      intro u f h_weak hf idx
      have h_step :
          B.IsSmoothWeakSolution
            (fun y : EE => (fderiv ℝ u y) (EuclideanSpace.single (idx 0) 1))
            (perturbedSource (d := d) B u f (idx 0)) :=
        partial_smooth_weak_solution (d := d) (Ω := (Set.univ : Set EE))
          isOpen_univ B h_weak hf (idx 0)
      have h_step_src_smooth :
          ContDiff ℝ (⊤ : ℕ∞) (perturbedSource (d := d) B u f (idx 0)) :=
        contDiff_perturbedSource' (d := d) B h_weak.1 hf (idx 0)
      have h_rec := ih h_step h_step_src_smooth (fun i : Fin m => idx i.succ)
      rw [iterClassicalPartial_succ, iteratedPerturbedSource_succ]
      exact h_rec

end IteratedSource

section TensorMixed

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem tensorComponent_iterated_partial_isSmoothWeakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (iterClassicalPartial (d := Module.finrank ℝ E) m idx
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀))
      (iteratedPerturbedSource (d := Module.finrank ℝ E)
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target) m
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
        idx) := by
  classical
  have h_base :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponent_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak
  have h_base_src_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp
  exact iterated_partial_isSmoothWeakSolution (d := Module.finrank ℝ E)
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target) m h_base
    h_base_src_smooth idx

end TensorMixed

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
